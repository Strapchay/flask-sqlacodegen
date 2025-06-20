# coding: utf-8
"""Contains the code generation logic and helper functions."""
from collections import defaultdict
from keyword import iskeyword
import inspect
import sys
import re

from sqlalchemy import (
    Enum,
    ForeignKeyConstraint,
    PrimaryKeyConstraint,
    CheckConstraint,
    UniqueConstraint,
    Table,
    Column,
    ARRAY,
    func,
    text as sa_text,
    Index,
)
from sqlalchemy.sql.expression import (
    true as sa_true,
    false as sa_false,
)
from sqlalchemy.schema import (
    ForeignKey,
    FetchedValue,
)
from sqlalchemy.util import OrderedDict
from sqlalchemy.types import Boolean, String
import sqlalchemy

try:
    from sqlalchemy.sql.expression import TextClause
except ImportError:
    from sqlalchemy.sql.expression import _TextClause as TextClause

_re_boolean_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \(0, 1\)")
_re_column_name = re.compile(r'(?:(["`]?)(?:.*)\1\.)?(["`]?)(.*)\2')
_re_enum_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \((.+)\)")
_re_enum_item = re.compile(r"'(.*?)(?<!\\)'")
_re_invalid_identifier = re.compile(
    r"[^a-zA-Z0-9_]" if sys.version_info[0] < 3 else r"(?u)\W"
)
_re_invalid_relationship = re.compile(r'[^a-zA-Z0-9._()\[\]{}= \'",]')

_re_first_cap = re.compile("(.)([A-Z][a-z]+)")
_re_all_cap = re.compile("([a-z0-9])([AZ])")

_dataclass = False


class _DummyInflectEngine(object):
    def singular_noun(self, noun):
        return noun

    def plural_noun(self, noun):
        return noun


def _get_column_names(constraint):
    if isinstance(constraint.columns, list):
        return [col.name for col in constraint.columns]
    return list(constraint.columns.keys())


def _convert_to_valid_identifier(name):
    assert name, "Identifier cannot be empty"
    if name[0].isdigit() or iskeyword(name):
        name = "_" + name
    return _re_invalid_identifier.sub("_", name)


def _get_compiled_expression(statement):
    if isinstance(statement, TextClause):
        return statement.text
    dialect = statement._from_objects[0].bind.dialect
    compiler = statement._compiler(dialect)

    class LiteralCompiler(compiler.__class__):
        def visit_bindparam(
            self, bindparam, within_columns_clause=False, literal_binds=False, **kwargs
        ):
            return super(LiteralCompiler, self).render_literal_bindparam(
                bindparam,
                within_columns_clause=within_columns_clause,
                literal_binds=literal_binds,
                **kwargs,
            )

    compiler = LiteralCompiler(dialect, statement)
    return compiler.process(statement)


def _get_constraint_sort_key(constraint):
    if isinstance(constraint, CheckConstraint):
        try:
            sql_text = str(constraint.sqltext)
        except Exception:
            sql_text = repr(constraint.sqltext)
        return "C{0}".format(sql_text)
    return constraint.__class__.__name__[0] + repr(_get_column_names(constraint))


def _get_common_fk_constraints(table1, table2):
    c1 = set(
        c
        for c in table1.constraints
        if isinstance(c, ForeignKeyConstraint) and c.elements[0].column.table == table2
    )
    c2 = set(
        c
        for c in table2.constraints
        if isinstance(c, ForeignKeyConstraint) and c.elements[0].column.table == table1
    )
    return c1.union(c2)


def _getargspec_init(method):
    try:
        sig = inspect.signature(method)
        params_list = []
        defaults_list = []
        for param in sig.parameters.values():
            params_list.append(param.name)
            if param.default is not inspect.Parameter.empty:
                defaults_list.append(param.default)
        return type(
            "ArgSpec",
            (),
            {
                "args": params_list,
                "defaults": tuple(defaults_list) if defaults_list else None,
            },
        )()
    except (TypeError, ValueError):
        if method is object.__init__:
            return type("ArgSpec", (), {"args": ["self"], "defaults": None})()
        else:
            return type(
                "ArgSpec", (), {"args": ["self", "*args", "**kwargs"], "defaults": None}
            )()


def _render_column_type(codegen, coltype):
    prepend = "db." if codegen.flask else "sa."
    args = []

    enum_to_render_as_python_class = None
    is_array_of_enum = False

    if isinstance(coltype, Enum):
        enum_to_render_as_python_class = coltype
    elif isinstance(coltype, ARRAY) and isinstance(coltype.item_type, Enum):
        enum_to_render_as_python_class = coltype.item_type
        is_array_of_enum = True

    if (
        enum_to_render_as_python_class
        and enum_to_render_as_python_class.name
        and enum_to_render_as_python_class.enums
    ):

        sql_enum_key = (
            enum_to_render_as_python_class.name,
            tuple(sorted(enum_to_render_as_python_class.enums)),
        )
        if sql_enum_key in codegen.enum_registry:
            python_enum_class_name = codegen.enum_registry[sql_enum_key]

            rendered_sqla_enum = f"{prepend}Enum(*{python_enum_class_name}_values, name='{enum_to_render_as_python_class.name}'"
            if not getattr(enum_to_render_as_python_class, "native_enum", True):
                rendered_sqla_enum += ", native_enum=False"
            if (
                getattr(enum_to_render_as_python_class, "create_constraint", True)
                is False
            ):
                rendered_sqla_enum += ", create_constraint=False"

            if getattr(enum_to_render_as_python_class, "schema", None):
                rendered_sqla_enum += (
                    f", schema='{enum_to_render_as_python_class.schema}'"
                )
            rendered_sqla_enum += ")"

            if is_array_of_enum:
                array_args = [rendered_sqla_enum]
                if getattr(coltype, "dimensions", None) is not None:
                    array_args.append(f"dimensions={coltype.dimensions}")
                return f"{prepend}ARRAY({', '.join(array_args)})"
            else:
                return rendered_sqla_enum

    argspec = _getargspec_init(coltype.__class__.__init__)
    arg_defaults = dict(
        zip(argspec.args[-len(argspec.defaults or ()) :], argspec.defaults or ())
    )
    missing = object()
    use_kwargs = False

    is_generic_enum_rendering = isinstance(coltype, Enum)

    for attr in argspec.args[1:]:
        if attr.startswith("_"):
            continue

        value = getattr(coltype, attr, missing)
        default_value_in_spec = arg_defaults.get(attr, missing)

        if is_generic_enum_rendering and attr == "enums":
            args.extend(repr(v) for v in value)
            continue

        if value is missing or value == default_value_in_spec:
            use_kwargs = True
        elif use_kwargs:
            args.append(f"{attr}={repr(value)}")
        else:
            args.append(repr(value))

    type_name_str = coltype.__class__.__name__
    if type_name_str == "ENUM" and is_generic_enum_rendering:
        type_name_str = "Enum"

    text = prepend + type_name_str
    if args:
        text += "({0})".format(", ".join(args))
    return text


def _render_server_default_expr(codegen, server_default_obj, column):
    """
    Render server default in a way that Alembic can understand and reproduce.
    Returns the Python code string FOR THE VALUE of the server_default parameter.
    """
    prepend = "db." if codegen.flask else "sa."

    if hasattr(column, 'identity') and column.identity is not None and column.primary_key:
        return None

    if not hasattr(server_default_obj, "arg") or server_default_obj.arg is None:
        if (
            column.primary_key
            and isinstance(column.type, (sqlalchemy.Integer, sqlalchemy.BigInteger))
            and (column.autoincrement is True or str(column.autoincrement).lower() == 'auto')
            and not (hasattr(column, 'identity') and column.identity is not None)
        ):
            return None

        if isinstance(server_default_obj, FetchedValue):
             codegen.collector.add_import(FetchedValue)
             return f"{prepend}FetchedValue()"
        return None


    default_arg = server_default_obj.arg

    if isinstance(default_arg, sqlalchemy.sql.functions.FunctionElement):
        if default_arg.name.lower() in ("now", "current_timestamp"):
            codegen.collector.add_import(func)
            return f"{prepend}func.now()"
        elif default_arg.name.lower() == "current_date":
            codegen.collector.add_import(func)
            return f"{prepend}func.current_date()"
        elif default_arg.name.lower() == "current_time":
            codegen.collector.add_import(func)
            return f"{prepend}func.current_time()"
        try:
            compiled_default = str(
                default_arg.compile(compile_kwargs={"literal_binds": True})
            )
            codegen.collector.add_import(sa_text)
            return f"{prepend}text({repr(compiled_default)})"
        except Exception:
            codegen.collector.add_import(FetchedValue)
            return f"{prepend}FetchedValue()"


    if isinstance(default_arg, TextClause):
        default_text = default_arg.text.strip()

        if isinstance(column.type, sqlalchemy.types.Boolean):
            if default_text.lower() == "true" or default_text == "1":
                codegen.collector.add_import(sa_text)
                return f"{prepend}text('true')"
            elif default_text.lower() == "false" or default_text == "0":
                codegen.collector.add_import(sa_text)
                return f"{prepend}text('false')"

        try:
            pass
        except ValueError:
            pass

        codegen.collector.add_import(sa_text)
        return f"{prepend}text({repr(default_text)})"

    if isinstance(default_arg, str):
        return repr(default_arg)
    elif default_arg is True:
        codegen.collector.add_import(sa_text)
        return f"{prepend}text('true')"
    elif default_arg is False:
        codegen.collector.add_import(sa_text)
        return f"{prepend}text('false')"
    elif isinstance(default_arg, (int, float)):
        codegen.collector.add_import(sa_text)
        return f"{prepend}text('{str(default_arg)}')"

    codegen.collector.add_import(FetchedValue)
    return f"{prepend}FetchedValue()"

def _render_column(self, column, show_name):
    codegen = self.codegen
    prepend = "db." if codegen.flask else "sa."

    args = []

    if show_name:
        args.append(repr(column.name))

    args.append(_render_column_type(codegen, column.type))

    for fk_obj in column.foreign_keys:
        args.append(_render_constraint(fk_obj))

    is_identity_column = hasattr(column, 'identity') and column.identity is not None

    if is_identity_column:
        codegen.collector.add_import(sqlalchemy.Identity)

        identity_params = []
        identity_constructor_attrs = ['start', 'increment', 'minvalue', 'maxvalue', 'cycle', 'cache', 'order']

        for attr_name in identity_constructor_attrs:
            if hasattr(column.identity, attr_name):
                value = getattr(column.identity, attr_name)
                if value is not None:
                    if attr_name == 'cycle' and value is False and column.identity.start is None:
                        pass
                    else:
                        identity_params.append(f"{attr_name}={repr(value)}")

        rendered_identity_params = ", ".join(identity_params)
        args.append(f"{prepend}Identity({rendered_identity_params})")

    kwargs_list = []

    if hasattr(column, "key") and column.key != column.name:
        kwargs_list.append(f"key='{column.key}'")

    if column.primary_key:
        kwargs_list.append("primary_key=True")

    if column.nullable is False and not column.primary_key:
        kwargs_list.append("nullable=False")
    elif column.nullable is True and column.primary_key:
        kwargs_list.append("nullable=True")

    has_table_level_single_col_uc = False
    for constr in column.table.constraints:
        if (
            isinstance(constr, UniqueConstraint)
            and len(constr.columns) == 1
            and constr.columns[0].name == column.name
        ):
            has_table_level_single_col_uc = True
            break

    has_table_level_single_col_unique_idx = False
    for idx in column.table.indexes:
        if idx.unique and len(idx.columns) == 1 and idx.columns[0].name == column.name:
            has_table_level_single_col_unique_idx = True
            break

    if getattr(column, "unique", False) and not column.primary_key:
        if (
            not has_table_level_single_col_uc
            and not has_table_level_single_col_unique_idx
        ):
            kwargs_list.append("unique=True")

    elif (
        getattr(column, "index", False)
        and not getattr(column, "unique", False)
        and not column.primary_key
    ):
        has_table_level_single_col_idx = False
        for idx in column.table.indexes:
            if (
                not idx.unique
                and len(idx.columns) == 1
                and idx.columns[0].name == column.name
            ):
                has_table_level_single_col_idx = True
                break
        if not has_table_level_single_col_idx:
            kwargs_list.append("index=True")

    if column.server_default and not is_identity_column:
        default_value_expr = _render_server_default_expr(
            codegen, column.server_default, column
        )
        if default_value_expr:
            kwargs_list.append(f"server_default={default_value_expr}")

    if not is_identity_column:
        if column.primary_key and isinstance(column.type, (sqlalchemy.Integer, sqlalchemy.BigInteger)):
            if column.autoincrement is False:
                kwargs_list.append("autoincrement=False")
        elif column.autoincrement is True and not column.primary_key:
            kwargs_list.append("autoincrement=True")


    if hasattr(column, "comment") and column.comment and not codegen.nocomments:
        kwargs_list.append(f"comment={repr(column.comment)}")
    elif (
        hasattr(column, "info")
        and column.info
        and column.info.get("description")
        and not codegen.nocomments
    ):
        if not (hasattr(column, "comment") and column.comment):
            kwargs_list.append(f'comment={repr(column.info["description"])}')

    args.extend(kwargs_list)
    return f"{prepend}Column({', '.join(args)})"

def _render_constraint(constraint):
    if isinstance(constraint, ForeignKey):
        table = constraint.column.table
    else:
        table = constraint.table
    prepend = "db." if hasattr(table, "_codegen") and table._codegen.flask else "sa."

    def render_fk_options(*opts):
        rendered_opts = []
        for opt in opts:
            if isinstance(opt, list):
                rendered_opts.append(repr(opt))
            else:
                rendered_opts.append(
                    repr(opt)
                    if isinstance(opt, str)
                    and not (opt.startswith("'") or opt.startswith('"'))
                    else opt
                )

        for attr in (
            "ondelete",
            "onupdate",
            "deferrable",
            "initially",
            "match",
            "name",
        ):
            value = getattr(constraint, attr, None)
            if value:
                rendered_opts.append(f"{attr}={repr(value)}")
        return ", ".join(rendered_opts)

    if isinstance(constraint, ForeignKey):
        remote_column = f"{constraint.column.table.fullname}.{constraint.column.name}"
        fk_options = []
        for attr in (
            "ondelete",
            "onupdate",
            "deferrable",
            "initially",
            "match",
            "use_alter",
            "name",
        ):
            value = getattr(constraint, attr, None)
            if value:
                fk_options.append(f"{attr}={repr(value)}")
        options_str = ""
        if fk_options:
            options_str = ", " + ", ".join(fk_options)
        return f"{prepend}ForeignKey({repr(remote_column)}{options_str})"

    elif isinstance(constraint, ForeignKeyConstraint):
        local_columns = [col.name for col in constraint.columns]
        remote_columns = [
            f"{fk.column.table.fullname}.{fk.column.name}" for fk in constraint.elements
        ]
        return f"{prepend}ForeignKeyConstraint({render_fk_options(local_columns, remote_columns)})"

    elif isinstance(constraint, CheckConstraint):
        sqltext_repr = repr(_get_compiled_expression(constraint.sqltext))
        name_repr = ""
        if getattr(constraint, "name", None):
            name_repr = f", name={repr(constraint.name)}"
        return f"{prepend}CheckConstraint({sqltext_repr}{name_repr})"

    elif isinstance(constraint, UniqueConstraint):
        columns_repr = [repr(col.name) for col in constraint.columns]
        name_repr = ""
        if getattr(constraint, "name", None):
            name_repr = f", name={repr(constraint.name)}"
        return f"{prepend}UniqueConstraint({', '.join(columns_repr)}{name_repr})"

    return f"{prepend}{constraint.__class__.__name__}()"


def _underscore(name):
    s1 = _re_first_cap.sub(r"\1_\2", name)
    return _re_all_cap.sub(r"\1_\2", s1).lower()


def _is_model_descendant(model_a, model_b):
    # Original logic
    if model_a.name == model_b.name:
        return True
    if not model_b.children:
        return False
    return any(_is_model_descendant(model_a, b) for b in model_b.children)


def _render_index(index):
    prepend = (
        "db."
        if hasattr(index.table, "_codegen") and index.table._codegen.flask
        else "sa."
    )
    columns_repr = [repr(col.name) for col in index.columns]

    args = [repr(index.name)] + columns_repr

    if getattr(index, "unique", False):
        args.append("unique=True")

    if hasattr(index, "kwargs"):
        for k, v in index.kwargs.items():
            if k not in ("unique", "_column_flag", "columns", "name"):
                args.append(f"{k}={repr(v)}")

    return f"{prepend}Index({', '.join(args)})"


class ImportCollector(OrderedDict):
    def add_import(self, obj):
        type_ = type(obj) if not isinstance(obj, type) else obj
        module_name = type_.__module__

        if module_name.startswith("sqlalchemy.dialects"):
            self.add_literal_import(
                module_name.split(".")[0] + "." + module_name.split(".")[1],
                module_name.split(".")[2],
            )

        elif module_name.startswith("sqlalchemy"):
            pkgname = module_name
            top_level_types = {
                "Column",
                "Table",
                "ForeignKey",
                "ForeignKeyConstraint",
                "CheckConstraint",
                "UniqueConstraint",
                "Index",
                "Enum",
                "ARRAY",
                "Boolean",
                "String",
                "Integer",
                "Numeric",
                "Date",
                "DateTime",
                "Text",
                "Float",
                "BigInteger",
                "true",
                "false",
                "func",
                "text",
                "Identity",
            }
            if type_.__name__ in top_level_types:
                pkgname = "sqlalchemy"
            elif module_name == "sqlalchemy.sql.schema":
                pkgname = "sqlalchemy.schema"

            self.add_literal_import(pkgname, type_.__name__)
        else:
            self.add_literal_import(module_name, type_.__name__)

    def add_literal_import(self, pkgname, name):
        names = self.setdefault(pkgname, set())
        names.add(name)

    def render(self):
        return "\n".join(
            "from {0} import {1}".format(package, ", ".join(sorted(names)))
            for package, names in self.items()
        )


class Model(object):
    def __init__(self, table, codegen):
        super(Model, self).__init__()
        self.table = table
        self.schema = table.schema
        self.codegen = codegen
        self.table._codegen = codegen

        for column in table.columns:
            cls = column.type.__class__
            for supercls in cls.__mro__:
                if hasattr(supercls, "__visit_name__"):
                    cls = supercls
                if (
                    supercls.__name__ != supercls.__name__.upper()
                    and not supercls.__name__.startswith("_")
                ):
                    break
            column.type = column.type.adapt(cls)

    def add_imports(self, collector):
        if self.table.columns:
            collector.add_import(Column)
        for column in self.table.columns:
            collector.add_import(column.type)
            if isinstance(column.type, ARRAY):
                collector.add_import(ARRAY)
            if column.server_default:
                pass

        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, ForeignKeyConstraint):
                if len(constraint.columns) > 1:
                    collector.add_import(ForeignKeyConstraint)
            elif isinstance(constraint, UniqueConstraint):
                if len(constraint.columns) > 1:
                    collector.add_import(UniqueConstraint)
            elif not isinstance(constraint, PrimaryKeyConstraint):
                collector.add_import(constraint)

        for index in self.table.indexes:
            if len(index.columns) > 1 or (
                len(index.columns) == 1
                and not getattr(index.columns[0], "unique", False)
                and not getattr(index.columns[0], "index", False)
            ):
                collector.add_import(Index)


class ModelTable(Model):
    def add_imports(self, collector):
        super(ModelTable, self).add_imports(collector)
        collector.add_import(Table)

    def render(self):
        prepend = "db." if self.codegen.flask else ""
        met = " metadata," if not self.codegen.flask else ""
        if not self.codegen.flask and prepend == "":
            prepend = "sa."

        text = "t_{0} = {1}Table(\n    {0!r},{2}\n".format(
            self.table.name, prepend, met
        )
        for column in self.table.columns:
            text += "    {0},\n".format(_render_column(self, column, True))

        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if (
                isinstance(constraint, ForeignKeyConstraint)
                and len(constraint.columns) == 1
            ):
                continue
            if (
                isinstance(constraint, UniqueConstraint)
                and len(constraint.columns) == 1
            ):
                col_is_unique_on_column_def = getattr(
                    constraint.columns[0], "unique", False
                )
                if col_is_unique_on_column_def:
                    continue
            text += "    {0},\n".format(_render_constraint(constraint))

        for index in self.table.indexes:
            if len(index.columns) > 1 or (
                len(index.columns) == 1
                and not (
                    getattr(index.columns[0], "index", False)
                    or getattr(index.columns[0], "unique", False)
                )
            ):
                text += "    {0},\n".format(_render_index(index))

        if self.schema:
            text += "    schema='{0}',\n".format(self.schema)

        if (
            hasattr(self.table, "comment")
            and self.table.comment
            and not self.codegen.nocomments
        ):
            text += f"    comment={repr(self.table.comment)},\n"

        return text.rstrip("\n,") + "\n)"


class ModelClass(Model):
    def __init__(
        self,
        table,
        association_tables,
        inflect_engine,
        detect_joined,
        collector,
        codegen,
    ):
        super(ModelClass, self).__init__(table, codegen)
        self.name = self._tablename_to_classname(table.name, inflect_engine)
        self.parent_name = "db.Model" if codegen.flask else "Base"
        self.children = []
        self.attributes = OrderedDict()

        for column in table.columns:
            self._add_attribute(column.name, column)
            if _dataclass and column.type.python_type.__module__ != "builtins":
                collector.add_literal_import(
                    column.type.python_type.__module__, column.type.python_type.__name__
                )

        pk_column_names = set(col.name for col in table.primary_key.columns)
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, ForeignKeyConstraint):
                target_table = constraint.elements[0].column.table
                target_cls_name = self._tablename_to_classname(
                    target_table.name, inflect_engine
                )

                is_joined_inheritance = (
                    detect_joined
                    and self.parent_name in ("Base", "db.Model")
                    and set(_get_column_names(constraint)) == pk_column_names
                    and target_table.name != table.name
                )

                if is_joined_inheritance:
                    self.parent_name = target_cls_name
                else:
                    relationship_ = ManyToOneRelationship(
                        self.name, target_cls_name, constraint, inflect_engine
                    )
                    self._add_attribute(relationship_.preferred_name, relationship_)

        for association_table_obj in association_tables:
            fk_constraints = [
                c
                for c in association_table_obj.constraints
                if isinstance(c, ForeignKeyConstraint)
            ]
            fk_constraints.sort(key=_get_constraint_sort_key)
            if len(fk_constraints) == 2:
                fk_to_self = None
                fk_to_other = None
                for fk_constr in fk_constraints:
                    if any(
                        elem.column.table == self.table for elem in fk_constr.elements
                    ):
                        fk_to_self = fk_constr
                    else:
                        fk_to_other = fk_constr

                if fk_to_self and fk_to_other:
                    target_table_for_relation = fk_to_other.elements[0].column.table
                    target_cls_name = self._tablename_to_classname(
                        target_table_for_relation.name, inflect_engine
                    )

                    relationship_ = ManyToManyRelationship(
                        self.name,
                        target_cls_name,
                        association_table_obj,
                        inflect_engine,
                    )
                    self._add_attribute(relationship_.preferred_name, relationship_)

    @staticmethod
    def _tablename_to_classname(tablename, inflect_engine):
        return "".join(
            part[:1].upper() + part[1:] for part in re.split("_|-", tablename)
        )

    def _add_attribute(self, attrname, value):
        tempname = _convert_to_valid_identifier(attrname)
        counter = 1
        base_name = tempname
        while tempname in self.attributes:
            tempname = f"{base_name}_{counter}"
            counter += 1
        self.attributes[tempname] = value
        return tempname

    def add_imports(self, collector):
        super(ModelClass, self).add_imports(collector)
        if any(isinstance(value, Relationship) for value in self.attributes.values()):
            collector.add_literal_import("sqlalchemy.orm", "relationship")
        for child in self.children:
            child.add_imports(collector)

    def render(self):
        global _dataclass
        text = "class {0}({1}):\n".format(self.name, self.parent_name)

        if _dataclass:
            text = "@dataclass\n" + text

        text += "    __tablename__ = {0!r}\n".format(self.table.name)

        table_args_list = []
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if (
                isinstance(constraint, ForeignKeyConstraint)
                and len(constraint.columns) == 1
            ):
                continue

            if (
                isinstance(constraint, UniqueConstraint)
                and len(constraint.columns) == 1
            ):
                column_obj = constraint.columns[0]
                if getattr(column_obj, "unique", False):
                    if not constraint.name and getattr(column_obj, "unique", False):
                        continue
            table_args_list.append(_render_constraint(constraint))

        for index_obj in self.table.indexes:
            if len(index_obj.columns) > 1:
                table_args_list.append(_render_index(index_obj))
            elif len(index_obj.columns) == 1:
                column_obj = index_obj.columns[0]
                is_already_on_column = False
                if index_obj.unique:
                    if getattr(column_obj, "unique", False):
                        is_already_on_column = True
                elif getattr(column_obj, "index", False):
                    is_already_on_column = True

                if not is_already_on_column:
                    table_args_list.append(_render_index(index_obj))

        table_kwargs_dict = {}
        if self.schema:
            table_kwargs_dict["schema"] = self.schema
        if (
            hasattr(self.table, "comment")
            and self.table.comment
            and not self.codegen.nocomments
        ):
            table_kwargs_dict["comment"] = self.table.comment

        if table_args_list or table_kwargs_dict:
            rendered_args_for_tuple = []
            rendered_args_for_tuple.extend(table_args_list)

            if table_kwargs_dict:
                kwargs_str_parts = [
                    f"{repr(k)}: {repr(v)}"
                    for k, v in sorted(table_kwargs_dict.items())
                ]
                rendered_args_for_tuple.append(f"{{{', '.join(kwargs_str_parts)}}}")

            if rendered_args_for_tuple:
                final_args_str = ",\n        ".join(rendered_args_for_tuple)
                if len(rendered_args_for_tuple) == 1 and not (
                    rendered_args_for_tuple[0].startswith("{")
                    and rendered_args_for_tuple[0].endswith("}")
                ):
                    final_args_str += ","
                text += "    __table_args__ = (\n        {0}\n    )\n".format(
                    final_args_str
                )

        text += "\n"

        for attr, column_obj in self.attributes.items():
            if isinstance(column_obj, Column):
                show_name_flag = attr != column_obj.name
                if _dataclass:
                    text += "    {0} : {1}\n".format(
                        attr, column_obj.type.python_type.__name__
                    )
                text += "    {0} = {1}\n".format(
                    attr, _render_column(self, column_obj, show_name_flag)
                )

        if any(isinstance(value, Relationship) for value in self.attributes.values()):
            text += "\n"
        for attr, relationship_obj in self.attributes.items():
            if isinstance(relationship_obj, Relationship):
                text += "    {0} = {1}\n".format(attr, relationship_obj.render())

        for child_class in self.children:
            text += "\n\n" + child_class.render()
        return text


class Relationship(object):
    def __init__(self, source_cls, target_cls):
        super(Relationship, self).__init__()
        self.source_cls = source_cls
        self.target_cls = target_cls
        self.kwargs = OrderedDict()
        self.backref_name = _underscore(self.source_cls)
        self._codegen = None

    def render(self):
        prepend = (
            "db."
            if hasattr(self, "_codegen") and self._codegen and self._codegen.flask
            else "sa.orm."
        )

        text = prepend + "relationship("
        args = [repr(self.target_cls)]

        rendered_kwargs = []
        for key, value in self.kwargs.items():
            rendered_kwargs.append(f"{key}={value}")

        args.extend(rendered_kwargs)

        if "secondaryjoin" in self.kwargs or len(args) > 2:
            text += "\n        "
            delimiter, end = ",\n        ", "\n    )"
        else:
            delimiter, end = ", ", ")"

        return text + delimiter.join(args) + end

    def make_backref(self, relationships, classes):
        target_class_model = classes.get(self.target_cls)

        base_backref_candidate = _underscore(self.backref_name)
        current_backref = base_backref_candidate
        suffix_num = 0

        used_backrefs_for_target = {
            rel.backref_name
            for rel in relationships
            if isinstance(rel, Relationship)
            and hasattr(rel, "kwargs")
            and "backref" in rel.kwargs
            and rel.target_cls == self.target_cls
        }
        if target_class_model and hasattr(target_class_model, "attributes"):
            used_backrefs_for_target.update(target_class_model.attributes.keys())

        while current_backref in used_backrefs_for_target:
            suffix_num += 1
            current_backref = f"{base_backref_candidate}_{suffix_num}"

        self.backref_name = current_backref
        self.kwargs["backref"] = repr(current_backref)


class ManyToOneRelationship(Relationship):
    def __init__(self, source_cls, target_cls, constraint, inflect_engine):
        super(ManyToOneRelationship, self).__init__(source_cls, target_cls)
        self._codegen = constraint.table._codegen

        local_fk_column_names = [col.name for col in constraint.columns]
        first_local_fk_col_name = local_fk_column_names[0]

        if source_cls == target_cls:
            self.preferred_name = "parent"
        else:
            if first_local_fk_col_name.endswith(
                "_id"
            ) or first_local_fk_col_name.endswith("_fk"):
                base_name = re.sub(r"(_id|_fk)$", "", first_local_fk_col_name)
                self.preferred_name = (
                    inflect_engine.singular_noun(base_name) or base_name
                )
            else:
                target_table_name_from_fk = constraint.elements[0].column.table.name
                self.preferred_name = (
                    inflect_engine.singular_noun(target_table_name_from_fk)
                    or target_table_name_from_fk
                )

        local_fk_columns_set = set(local_fk_column_names)
        if (
            constraint.table.primary_key
            and set(pk_col.name for pk_col in constraint.table.primary_key.columns)
            == local_fk_columns_set
        ):
            self.kwargs["uselist"] = "False"
        else:
            for uc in constraint.table.constraints:
                if (
                    isinstance(uc, UniqueConstraint)
                    and set(uc_col.name for uc_col in uc.columns)
                    == local_fk_columns_set
                ):
                    self.kwargs["uselist"] = "False"
                    break

        join_conditions = []
        for i, fk_element in enumerate(constraint.elements):
            local_col_name_on_source = constraint.columns[i].name
            remote_col_name_on_target = fk_element.column.name
            join_conditions.append(
                f"{source_cls}.{local_col_name_on_source} == {target_cls}.{remote_col_name_on_target}"
            )

        if len(join_conditions) > 1:
            self.kwargs["primaryjoin"] = repr(f"and_({', '.join(join_conditions)})")
        else:
            self.kwargs["primaryjoin"] = repr(join_conditions[0])

        if source_cls == target_cls:
            parent_pk_cols_expressions = [
                f"{target_cls}.{pk_col.name}"
                for pk_col in constraint.elements[0].column.table.primary_key
            ]
            if len(parent_pk_cols_expressions) == 1:
                self.kwargs["remote_side"] = repr(parent_pk_cols_expressions[0])
            else:
                self.kwargs["remote_side"] = repr(parent_pk_cols_expressions)


class ManyToManyRelationship(Relationship):
    def __init__(self, source_cls, target_cls, association_table, inflect_engine):
        super(ManyToManyRelationship, self).__init__(source_cls, target_cls)
        self._codegen = association_table._codegen

        prefix = (
            association_table.schema + "."
            if association_table.schema is not None
            else ""
        )
        self.kwargs["secondary"] = repr(prefix + association_table.name)

        self.preferred_name = inflect_engine.plural_noun(target_cls.lower())
        if not self.preferred_name:
            self.preferred_name = target_cls.lower() + "_collection"

        fk_constraints = [
            c
            for c in association_table.constraints
            if isinstance(c, ForeignKeyConstraint)
        ]
        fk_constraints.sort(key=lambda fk: fk.elements[0].column.table.name)

        fk_to_source_table = None
        fk_to_target_table = None

        for fk_constr in fk_constraints:
            if any(
                elem.column.table.name == _underscore(source_cls)
                for elem in fk_constr.elements
            ):
                fk_to_source_table = fk_constr
            elif any(
                elem.column.table.name == _underscore(target_cls)
                for elem in fk_constr.elements
            ):
                fk_to_target_table = fk_constr

        if not fk_to_source_table or not fk_to_target_table:
            if source_cls == target_cls and len(fk_constraints) == 2:
                fk_to_source_table = fk_constraints[0]
                fk_to_target_table = fk_constraints[1]
                self.preferred_name = inflect_engine.plural_noun(
                    target_cls.lower()
                ) or (target_cls.lower() + "_collection")

        if fk_to_source_table:
            pri_join_conds = []
            for i, elem in enumerate(fk_to_source_table.elements):
                source_table_pk_col_name = elem.column.name
                assoc_table_fk_col_name = fk_to_source_table.columns[i].name
                pri_join_conds.append(
                    f"{source_cls}.{source_table_pk_col_name} == {association_table.name}.c.{assoc_table_fk_col_name}"
                )
            self.kwargs["primaryjoin"] = (
                repr(f"and_({', '.join(pri_join_conds)})")
                if len(pri_join_conds) > 1
                else repr(pri_join_conds[0])
            )

        if fk_to_target_table:
            sec_join_conds = []
            for i, elem in enumerate(fk_to_target_table.elements):
                target_table_pk_col_name = elem.column.name
                assoc_table_fk_col_name = fk_to_target_table.columns[i].name
                sec_join_conds.append(
                    f"{target_cls}.{target_table_pk_col_name} == {association_table.name}.c.{assoc_table_fk_col_name}"
                )
            self.kwargs["secondaryjoin"] = (
                repr(f"and_({', '.join(sec_join_conds)})")
                if len(sec_join_conds) > 1
                else repr(sec_join_conds[0])
            )

        self.backref_name = inflect_engine.plural_noun(_underscore(source_cls)) or (
            _underscore(source_cls) + "_collection"
        )


class CodeGenerator(object):
    header = '# coding: utf-8\n"""\nAuto-generated by sqlacodegen-modified.\n"""'
    footer = ""

    def __init__(
        self,
        metadata,
        noindexes=False,
        noconstraints=False,
        nojoined=False,
        noinflect=False,
        nobackrefs=False,
        flask=False,
        ignore_cols=None,
        noclasses=False,
        nocomments=False,
        notables=False,
        dataclass=False,
    ):
        super(CodeGenerator, self).__init__()

        self.metadata = metadata
        self.flask = flask
        if noinflect:
            self.inflect_engine = _DummyInflectEngine()
        else:
            import inflect

            self.inflect_engine = inflect.engine()

        _ignore_columns = ignore_cols or []
        self.nocomments = nocomments
        self.dataclass = dataclass
        if self.dataclass:
            global _dataclass
            _dataclass = True

        self.enum_registry = {}
        self.py_enum_definitions = OrderedDict()
        self.enum_counter = 0

        links = defaultdict(list)
        association_table_names = set()

        for table_name, table_obj in metadata.tables.items():
            if table_name in (
                "alembic_version",
                "migrate_version",
            ):
                continue

            fk_constraints = [
                const
                for const in table_obj.constraints
                if isinstance(const, ForeignKeyConstraint)
            ]

            is_pure_association = True
            if not table_obj.primary_key or not fk_constraints:
                is_pure_association = False
            else:
                pk_col_names = {col.name for col in table_obj.primary_key.columns}
                all_col_names = {col.name for col in table_obj.columns}
                if pk_col_names != all_col_names:
                    is_pure_association = False

                if is_pure_association:
                    fk_col_names_in_pks = set()
                    for fk_c in fk_constraints:
                        for col in fk_c.columns:
                            fk_col_names_in_pks.add(col.name)
                    if fk_col_names_in_pks != pk_col_names:
                        is_pure_association = False

            if is_pure_association and len(fk_constraints) >= 2:
                association_table_names.add(table_name)
                for fk_c in fk_constraints:
                    referred_table_name = fk_c.elements[0].column.table.name
                    if referred_table_name != table_name:
                        links[referred_table_name].append(table_obj)

        self.models = []
        self.collector = ImportCollector()

        if metadata.tables:
            self.collector.add_import(sqlalchemy)
            if self.flask:
                self.collector.add_literal_import("flask_sqlalchemy", "SQLAlchemy")
            else:
                self.collector.add_literal_import(
                    "sqlalchemy.ext.declarative", "declarative_base"
                )
                self.collector.add_literal_import("sqlalchemy", "MetaData")
            if self.dataclass:
                self.collector.add_literal_import("dataclasses", "dataclass")

        self.classes = {}

        sorted_tables = sorted(
            metadata.tables.values(), key=lambda t: (t.schema or "", t.name)
        )

        for table in sorted_tables:
            if table.name in ("alembic_version", "migrate_version"):
                continue
            if table.name in association_table_names and not notables:
                if notables:
                    model = ModelTable(table, self)
                    self.models.append(model)
                    model.add_imports(self.collector)
                continue

            if noindexes:
                table.indexes.clear()
            if noconstraints:
                table.constraints = {
                    c for c in table.constraints if isinstance(c, PrimaryKeyConstraint)
                }

            for column in table.columns:
                self._process_column_enum_type(column)

            if notables:
                model = ModelTable(table, self)
            elif noclasses or not table.primary_key:
                model = ModelTable(table, self)
            else:
                relevant_assoc_tables = [
                    metadata.tables[name] for name in association_table_names
                ]

                model = ModelClass(
                    table,
                    relevant_assoc_tables,
                    self.inflect_engine,
                    not nojoined,
                    self.collector,
                    self,
                )
                self.classes[model.name] = model

            self.models.append(model)
            model.add_imports(self.collector)

        if not notables and not noclasses:
            for model_class_instance in list(self.models):
                if isinstance(
                    model_class_instance, ModelClass
                ) and model_class_instance.parent_name not in ("Base", "db.Model"):
                    parent_class_model = self.classes.get(
                        model_class_instance.parent_name
                    )
                    if parent_class_model:
                        parent_class_model.children.append(model_class_instance)
                        if model_class_instance in self.models:
                            self.models.remove(model_class_instance)

            if not nobackrefs:
                all_relationships = []
                for model_class_instance in self.classes.values():
                    for attr_value in model_class_instance.attributes.values():
                        if isinstance(attr_value, Relationship):
                            all_relationships.append(attr_value)

                for rel in all_relationships:
                    rel.make_backref(all_relationships, self.classes)

    def _process_column_enum_type(self, column):
        """Helper to process Enum types on columns and register them for Python class generation."""
        coltype = column.type
        sql_enum_object_to_process = None

        if isinstance(coltype, Enum):
            sql_enum_object_to_process = coltype
        elif isinstance(coltype, ARRAY) and isinstance(coltype.item_type, Enum):
            sql_enum_object_to_process = coltype.item_type

        if sql_enum_object_to_process and sql_enum_object_to_process.enums:
            actual_sql_enum_name_from_db = sql_enum_object_to_process.name
            if not actual_sql_enum_name_from_db:
                return

            python_enum_class_name_to_generate = _convert_to_valid_identifier(
                actual_sql_enum_name_from_db
            )
            if not python_enum_class_name_to_generate:
                self.enum_counter += 1
                python_enum_class_name_to_generate = f"EnumType{self.enum_counter}"

            sql_enum_key = (
                actual_sql_enum_name_from_db,
                tuple(sorted(sql_enum_object_to_process.enums)),
            )

            if sql_enum_key not in self.enum_registry:
                final_python_class_name = python_enum_class_name_to_generate
                disambiguation_counter = 0
                while (
                    final_python_class_name in self.py_enum_definitions
                    and tuple(sorted(self.py_enum_definitions[final_python_class_name]))
                    != sql_enum_key[1]
                ):
                    disambiguation_counter += 1
                    final_python_class_name = (
                        f"{python_enum_class_name_to_generate}_{disambiguation_counter}"
                    )

                self.enum_registry[sql_enum_key] = final_python_class_name
                self.py_enum_definitions[final_python_class_name] = list(
                    sql_enum_object_to_process.enums
                )
                self.collector.add_literal_import("enum", "Enum")

    def render(self, outfile=sys.stdout):
        print(self.header, file=outfile)

        if self.py_enum_definitions:
            self.collector.add_literal_import("enum", "Enum")

        rendered_imports = self.collector.render()

        final_imports_to_print = rendered_imports
        enum_class_to_use_in_def = "Enum"

        if self.py_enum_definitions:
            if (
                "from enum import Enum" in final_imports_to_print
                and "as PyEnum" not in final_imports_to_print
            ):
                final_imports_to_print = final_imports_to_print.replace(
                    "from enum import Enum", "from enum import Enum as PyEnum"
                )
                if "enum" in self.collector and "Enum" in self.collector["enum"]:
                    enum_imports = list(self.collector["enum"])
                    try:
                        enum_imports.remove("Enum")
                    except ValueError:
                        pass

                    new_enum_import_line = "from enum import Enum as PyEnum"
                    if enum_imports:
                        new_enum_import_line += ", " + ", ".join(sorted(enum_imports))

                    if "enum" in self.collector and "Enum" in self.collector["enum"]:
                        self.collector["enum"].remove("Enum")
                        if not self.collector["enum"]:
                            del self.collector["enum"]
                    final_imports_to_print = self.collector.render()
                    if self.py_enum_definitions:
                        print("from enum import Enum as PyEnum\n", file=outfile)
                        enum_class_to_use_in_def = "PyEnum"
            elif "from enum import Enum as PyEnum" in final_imports_to_print:
                enum_class_to_use_in_def = "PyEnum"

        if final_imports_to_print:
            print(final_imports_to_print + "\n", file=outfile)
        elif (
            self.py_enum_definitions
            and enum_class_to_use_in_def == "PyEnum"
            and "from enum import Enum as PyEnum" not in final_imports_to_print
        ):
            print("from enum import Enum as PyEnum\n", file=outfile)

        if self.py_enum_definitions:
            for py_name, values in self.py_enum_definitions.items():
                print(f"class {py_name}({enum_class_to_use_in_def}):", file=outfile)
                for value in values:
                    member_name = _convert_to_valid_identifier(value.upper())
                    if not member_name.isidentifier() or iskeyword(member_name):
                        member_name = f"M_{member_name}"
                        if iskeyword(member_name):
                            member_name = f"_{member_name}"
                    print(f"    {member_name} = {repr(value)}", file=outfile)
                print(
                    f"\n{py_name}_values = [e.value for e in {py_name}]\n", file=outfile
                )

        if self.flask:
            print("db = SQLAlchemy()", file=outfile)
        else:
            has_declarative_classes = any(
                isinstance(model, ModelClass)
                for model in self.models
                if isinstance(model, ModelClass)
            )
            if has_declarative_classes:
                print(
                    "\nBase = declarative_base()\nmetadata = Base.metadata",
                    file=outfile,
                )
            elif self.models:
                print("\nmetadata = MetaData()", file=outfile)

        models_to_render_directly = []
        for m in self.models:
            is_child_of_another_modelclass = False
            if isinstance(m, ModelClass):
                if m.parent_name not in ("Base", "db.Model"):
                    if m.parent_name in self.classes:
                        is_child_of_another_modelclass = True
            if not is_child_of_another_modelclass:
                models_to_render_directly.append(m)

        for model_to_render in models_to_render_directly:
            print("\n\n", file=outfile)
            print(model_to_render.render().rstrip("\n"), file=outfile)

        if self.footer:
            print(self.footer, file=outfile)
