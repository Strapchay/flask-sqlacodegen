# coding: utf-8
"""Contains the code generation logic and helper functions."""
from collections import defaultdict
from keyword import iskeyword
import inspect
import sys
import re

from sqlalchemy import (Enum, ForeignKeyConstraint, PrimaryKeyConstraint, CheckConstraint, UniqueConstraint, Table,
                        Column, ARRAY, func, text as sa_text) # Added func, sa_text for server_default
from sqlalchemy.sql.expression import true as sa_true, false as sa_false # Added for boolean server_defaults
from sqlalchemy.schema import ForeignKey, FetchedValue # Ensure FetchedValue is available
from sqlalchemy.util import OrderedDict
from sqlalchemy.types import Boolean, String # Keep for type checking
import sqlalchemy

try:
    from sqlalchemy.sql.expression import TextClause
except ImportError:
    from sqlalchemy.sql.expression import _TextClause as TextClause

_re_boolean_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \(0, 1\)")
_re_column_name = re.compile(r'(?:(["`]?)(?:.*)\1\.)?(["`]?)(.*)\2')
_re_enum_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \((.+)\)")
_re_enum_item = re.compile(r"'(.*?)(?<!\\)'")
_re_invalid_identifier = re.compile(r'[^a-zA-Z0-9_]' if sys.version_info[0] < 3 else r'(?u)\W')
_re_invalid_relationship = re.compile(r'[^a-zA-Z0-9._()\[\]{}= \'",]')

_re_first_cap = re.compile('(.)([A-Z][a-z]+)')
_re_all_cap = re.compile('([a-z0-9])([AZ])')

_dataclass = False # Global flag for @dataclass annotation, as in original


class _DummyInflectEngine(object):
    def singular_noun(self, noun):
        return noun
    def plural_noun(self, noun):
        return noun  # No pluralization


def _get_column_names(constraint):
    # Helper to get column names from a constraint
    if isinstance(constraint.columns, list): # For some constraint types
        return [col.name for col in constraint.columns]
    return list(constraint.columns.keys()) # For ForeignKeyConstraint, etc.


def _convert_to_valid_identifier(name):
    assert name, 'Identifier cannot be empty'
    if name[0].isdigit() or iskeyword(name):
        name = '_' + name
    return _re_invalid_identifier.sub('_', name)


def _get_compiled_expression(statement):
    if isinstance(statement, TextClause):
        return statement.text
    dialect = statement._from_objects[0].bind.dialect
    compiler = statement._compiler(dialect)
    class LiteralCompiler(compiler.__class__):
        def visit_bindparam(self, bindparam, within_columns_clause=False, literal_binds=False, **kwargs):
            return super(LiteralCompiler, self).render_literal_bindparam(
                bindparam, within_columns_clause=within_columns_clause,
                literal_binds=literal_binds, **kwargs
            )
    compiler = LiteralCompiler(dialect, statement)
    return compiler.process(statement)


def _get_constraint_sort_key(constraint):
    if isinstance(constraint, CheckConstraint):
        try:
            sql_text = str(constraint.sqltext)
        except Exception:
            sql_text = repr(constraint.sqltext) # Fallback
        return 'C{0}'.format(sql_text)
    return constraint.__class__.__name__[0] + repr(_get_column_names(constraint))


def _get_common_fk_constraints(table1, table2):
    c1 = set(c for c in table1.constraints if isinstance(c, ForeignKeyConstraint) and
             c.elements[0].column.table == table2)
    c2 = set(c for c in table2.constraints if isinstance(c, ForeignKeyConstraint) and
             c.elements[0].column.table == table1)
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
        return type('ArgSpec', (), {'args': params_list, 'defaults': tuple(defaults_list) if defaults_list else None})()
    except (TypeError, ValueError): # ValueError for some built-in types in Py3.11+
        if method is object.__init__:
            return type('ArgSpec', (), {'args': ['self'], 'defaults': None})()
        else: # Fallback for methods that can't be inspected easily
            return type('ArgSpec', (), {'args': ['self', '*args', '**kwargs'], 'defaults': None})()


def _render_column_type(codegen, coltype):
    prepend = 'db.' if codegen.flask else 'sa.' # Use sa. for non-flask more consistently
    args = []

    if isinstance(coltype, Enum) and coltype.name and hasattr(codegen, 'enum_registry') and coltype.name in codegen.enum_registry.values():
        python_enum_name = [k[0] for k, v in codegen.enum_registry.items() if v == coltype.name][0]
        return f"{prepend}Enum(*{python_enum_name}_values, name='{coltype.name}')"
    elif isinstance(coltype, ARRAY) and isinstance(coltype.item_type, Enum) and \
         coltype.item_type.name and hasattr(codegen, 'enum_registry') and coltype.item_type.name in codegen.enum_registry.values():
        python_enum_name = [k[0] for k, v in codegen.enum_registry.items() if v == coltype.item_type.name][0]
        return f"{prepend}ARRAY({prepend}Enum(*{python_enum_name}_values, name='{coltype.item_type.name}'))"

    argspec = _getargspec_init(coltype.__class__.__init__)
    defaults = dict(zip(argspec.args[-len(argspec.defaults or ()):], argspec.defaults or ()))
    missing = object()
    use_kwargs = False
    for attr in argspec.args[1:]: # Skip 'self'
        if attr.startswith('_'): # Skip private attributes
            continue

        value = getattr(coltype, attr, missing)
        default_value_in_spec = defaults.get(attr, missing)

        if isinstance(coltype, Enum) and attr == 'enums':
            if value is not missing:
                 args.extend(repr(arg) for arg in value)
            continue # Handled as positional, don't process as kwarg

        if value is missing or value == default_value_in_spec:
            use_kwargs = True
        elif use_kwargs:
            args.append(f"{attr}={repr(value)}")
        else:
            args.append(repr(value))

    type_name_str = coltype.__class__.__name__
    if type_name_str == "ENUM" and not (isinstance(coltype, Enum) and coltype.name and hasattr(codegen, 'enum_registry') and coltype.name in codegen.enum_registry.values()):
        type_name_str = "Enum"

    text = prepend + type_name_str
    if args:
        text += '({0})'.format(', '.join(args))
    return text

def _render_server_default_expr(codegen, server_default_obj, column_type_py):
    """
    Render server default in a way that Alembic can understand and reproduce.
    Returns the Python code string for the server_default value.
    e.g., "sa.text('false')", "sa.func.now()", "True", "'default_string'"
    """
    prepend = 'db.' if codegen.flask else 'sa.' # Use sa. for non-flask consistently

    if not hasattr(server_default_obj, 'arg'):
        return f"{prepend}FetchedValue()"

    default_arg = server_default_obj.arg

    if isinstance(default_arg, TextClause):
        default_text = default_arg.text.strip()

        if default_text.lower() == 'now()' or default_text.lower() == 'current_timestamp':
            codegen.collector.add_import(func)
            return f"{prepend}func.now()"
        if default_text.lower() == 'current_date':
            codegen.collector.add_import(func)
            return f"{prepend}func.current_date()"
        if default_text.lower() == 'current_time':
            codegen.collector.add_import(func)
            return f"{prepend}func.current_time()"

        if column_type_py is bool:
            if default_text.lower() == 'true':
                codegen.collector.add_import(sa_true)
                return f"{prepend}true()"
            elif default_text.lower() == 'false':
                codegen.collector.add_import(sa_false)
                return f"{prepend}false()"

        if default_text.lower().startswith("nextval(") and "::regclass" in default_text.lower():
            codegen.collector.add_import(sa_text)
            return f"{prepend}text({repr(default_text)})"

        if default_text.startswith("'") and default_text.endswith("'"):
            if default_text.count("'") == 2:
                return repr(default_text[1:-1])
            else:
                codegen.collector.add_import(sa_text)
                return f"{prepend}text({repr(default_text)})"

        try:
            if '.' in default_text:
                float(default_text) # Check if it's a float
                return default_text # Render as number: server_default=3.14
            else:
                int(default_text) # Check if it's an int
                return default_text # Render as number: server_default=42
        except ValueError:
            return f"{prepend}text({repr(default_text)})"

    elif isinstance(default_arg, sqlalchemy.sql.functions.Function):
        if default_arg.name.lower() == 'now' or default_arg.name.lower() == 'current_timestamp':
            codegen.collector.add_import(func)
            return f"{prepend}func.now()"
        try:
            compiled_default = str(default_arg.compile(compile_kwargs={"literal_binds": True}))
            codegen.collector.add_import(sa_text)
            return f"{prepend}text({repr(compiled_default)})"
        except Exception:
            pass

    codegen.collector.add_import(FetchedValue)
    return f"{prepend}FetchedValue()"


def _render_column(self, column, show_name):
    prepend = 'db.' if self.codegen.flask else 'sa.' # Use sa. for non-flask more consistently
    args = []

    if show_name or (hasattr(column, 'key') and column.key != column.name):
        args.append(repr(column.name))
    if hasattr(column, 'key') and column.key != column.name:
        args.append(f"key='{column.key}'")

    dedicated_fks = [c for c in column.foreign_keys if len(c.constraint.columns) == 1]
    render_coltype = not dedicated_fks or any(fk.column is column for fk in dedicated_fks)
    if render_coltype:
        args.append(_render_column_type(self.codegen, column.type))

    for fk in dedicated_fks:
        if fk.column is column: # Ensure this FK is for *this* column
            args.append(_render_constraint(fk))

    is_sole_pk = column.primary_key and len(column.table.primary_key) == 1

    if column.primary_key:
        args.append('primary_key=True')

    if column.nullable is False and not is_sole_pk:
        args.append('nullable=False')
    elif column.nullable is True and is_sole_pk :
        args.append('nullable=True')

    if getattr(column, 'unique', False): # Check if column.unique is True
        args.append('unique=True')
    elif getattr(column, 'index', False): # Check if column.index is True (and not unique)
         args.append('index=True')

    if column.server_default:
        rendered_default_expr_str = _render_server_default_expr(self.codegen, column.server_default, column.type.python_type)
        if rendered_default_expr_str: # It might return None if default is None
            args.append(rendered_default_expr_str) # This is already "server_default=..."

    if hasattr(column, 'comment') and column.comment and not self.codegen.nocomments:
        args.append(f'comment={repr(column.comment)}')

    return f"{prepend}Column({', '.join(args)})"


def _render_constraint(constraint):
    if isinstance(constraint, ForeignKey):
        table = constraint.column.table
    else:
        table = constraint.table
    prepend = 'db.' if hasattr(table, '_codegen') and table._codegen.flask else 'sa.'

    def render_fk_options(*opts):
        rendered_opts = []
        for opt in opts:
            if isinstance(opt, list):
                rendered_opts.append(repr(opt))
            else:
                rendered_opts.append(repr(opt) if isinstance(opt, str) and not (opt.startswith("'") or opt.startswith('"')) else opt)

        for attr in 'ondelete', 'onupdate', 'deferrable', 'initially', 'match', 'name':
            value = getattr(constraint, attr, None)
            if value:
                rendered_opts.append(f"{attr}={repr(value)}")
        return ', '.join(rendered_opts)

    if isinstance(constraint, ForeignKey):
        remote_column = f"{constraint.column.table.fullname}.{constraint.column.name}"
        fk_options = []
        for attr in 'ondelete', 'onupdate', 'deferrable', 'initially', 'match', 'use_alter', 'name':
             value = getattr(constraint, attr, None)
             if value:
                 fk_options.append(f"{attr}={repr(value)}")
        options_str = ""
        if fk_options:
            options_str = ", " + ", ".join(fk_options)
        return f"{prepend}ForeignKey({repr(remote_column)}{options_str})"

    elif isinstance(constraint, ForeignKeyConstraint):
        local_columns = [col.name for col in constraint.columns]
        remote_columns = [f"{fk.column.table.fullname}.{fk.column.name}" for fk in constraint.elements]
        return f"{prepend}ForeignKeyConstraint({render_fk_options(local_columns, remote_columns)})"

    elif isinstance(constraint, CheckConstraint):
        sqltext_repr = repr(_get_compiled_expression(constraint.sqltext))
        name_repr = ""
        if getattr(constraint, 'name', None):
            name_repr = f", name={repr(constraint.name)}"
        return f"{prepend}CheckConstraint({sqltext_repr}{name_repr})"

    elif isinstance(constraint, UniqueConstraint):
        columns_repr = [repr(col.name) for col in constraint.columns]
        name_repr = ""
        if getattr(constraint, 'name', None):
            name_repr = f", name={repr(constraint.name)}"
        return f"{prepend}UniqueConstraint({', '.join(columns_repr)}{name_repr})"

    return f"{prepend}{constraint.__class__.__name__}()"

def _underscore(name):
    s1 = _re_first_cap.sub(r'\1_\2', name)
    return _re_all_cap.sub(r'\1_\2', s1).lower()


def _is_model_descendant(model_a, model_b):
    if model_a.name == model_b.name:
        return True
    if not model_b.children:
        return False
    return any(_is_model_descendant(model_a, b) for b in model_b.children)


def _render_index(index):
    prepend = 'db.' if hasattr(index.table, '_codegen') and index.table._codegen.flask else 'sa.'
    columns_repr = [repr(col.name) for col in index.columns]

    args = [repr(index.name)] + columns_repr

    if getattr(index, 'unique', False):
        args.append('unique=True')

    if hasattr(index, 'kwargs'):
        for k, v in index.kwargs.items():
            if k not in ('unique', '_column_flag', 'columns', 'name'):
                args.append(f"{k}={repr(v)}")

    return f"{prepend}Index({', '.join(args)})"


class ImportCollector(OrderedDict):
    def add_import(self, obj):
        type_ = type(obj) if not isinstance(obj, type) else obj
        module_name = type_.__module__

        if module_name.startswith('sqlalchemy.dialects'):
            self.add_literal_import(module_name.split('.')[0] + '.' + module_name.split('.')[1], module_name.split('.')[2])

        elif module_name.startswith('sqlalchemy'):
            pkgname = module_name
            top_level_types = {'Column', 'Table', 'ForeignKey', 'ForeignKeyConstraint',
                               'CheckConstraint', 'UniqueConstraint', 'Index',
                               'Enum', 'ARRAY', 'Boolean', 'String', 'Integer', 'Numeric',
                               'Date', 'DateTime', 'Text', 'Float', 'BigInteger',
                               'true', 'false', 'func', 'text'} # Added true, false, func, text
            if type_.__name__ in top_level_types:
                pkgname = 'sqlalchemy'
            elif module_name == 'sqlalchemy.sql.schema':
                pkgname = 'sqlalchemy.schema'

            self.add_literal_import(pkgname, type_.__name__)
        else:
            self.add_literal_import(module_name, type_.__name__)

    def add_literal_import(self, pkgname, name):
        names = self.setdefault(pkgname, set())
        names.add(name)

    def render(self):
        return '\n'.join('from {0} import {1}'.format(package, ', '.join(sorted(names)))
                         for package, names in self.items())


class Model(object):
    def __init__(self, table, codegen):
        super(Model, self).__init__()
        self.table = table
        self.schema = table.schema
        self.codegen = codegen # Store codegen instance for access to flask flag, collector
        self.table._codegen = codegen # Attach to table for _render_constraint/index prepend

        for column in table.columns:
            cls = column.type.__class__
            for supercls in cls.__mro__:
                if hasattr(supercls, '__visit_name__'): # SQLAlchemy internal marker
                    cls = supercls
                if supercls.__name__ != supercls.__name__.upper() and \
                   not supercls.__name__.startswith('_'):
                    break
            column.type = column.type.adapt(cls)


    def add_imports(self, collector):
        if self.table.columns:
            collector.add_import(Column)
        for column in self.table.columns:
            collector.add_import(column.type) # Handles Enum, ARRAY, String etc.
            if isinstance(column.type, ARRAY): # Ensure ARRAY itself is imported if item_type is custom/complex
                collector.add_import(ARRAY)
            if column.server_default:
                collector.add_import for func, text, true, false, FetchedValue
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
            if len(index.columns) > 1 or (len(index.columns) == 1 and not getattr(index.columns[0],'unique', False) and not getattr(index.columns[0],'index',False)):
                 collector.add_import(Index)


class ModelTable(Model):
    def add_imports(self, collector):
        super(ModelTable, self).add_imports(collector)
        collector.add_import(Table)

    def render(self):
        prepend = 'db.' if self.codegen.flask else ''
        met = ' metadata,' if not self.codegen.flask else ''
        if not self.codegen.flask and prepend == '':
            prepend = 'sa.'


        text = 't_{0} = {1}Table(\n    {0!r},{2}\n'.format(self.table.name, prepend, met)
        for column in self.table.columns:
            text += '    {0},\n'.format(_render_column(self, column, True))

        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if isinstance(constraint, ForeignKeyConstraint) and len(constraint.columns) == 1:
                continue
            if isinstance(constraint, UniqueConstraint) and len(constraint.columns) == 1:
                col_is_unique_on_column_def = getattr(constraint.columns[0], 'unique', False)
                if col_is_unique_on_column_def:
                    continue
            text += '    {0},\n'.format(_render_constraint(constraint))

        for index in self.table.indexes:
            if len(index.columns) > 1 or \
               (len(index.columns) == 1 and not (getattr(index.columns[0], 'index', False) or getattr(index.columns[0], 'unique', False))):
                text += '    {0},\n'.format(_render_index(index))

        if self.schema:
            text += "    schema='{0}',\n".format(self.schema)

        if hasattr(self.table, 'comment') and self.table.comment and not self.codegen.nocomments:
            text += f"    comment={repr(self.table.comment)},\n"

        return text.rstrip('\n,') + '\n)'


class ModelClass(Model):
    def __init__(self, table, association_tables, inflect_engine, detect_joined, collector, codegen):
        super(ModelClass, self).__init__(table, codegen)
        self.name = self._tablename_to_classname(table.name, inflect_engine)
        self.parent_name = 'db.Model' if codegen.flask else 'Base'
        self.children = []
        self.attributes = OrderedDict()

        for column in table.columns:
            self._add_attribute(column.name, column)
            if _dataclass and column.type.python_type.__module__ != 'builtins':
                collector.add_literal_import(column.type.python_type.__module__, column.type.python_type.__name__)

        pk_column_names = set(col.name for col in table.primary_key.columns)
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, ForeignKeyConstraint):
                target_table = constraint.elements[0].column.table
                target_cls_name = self._tablename_to_classname(target_table.name, inflect_engine)

                is_joined_inheritance = (detect_joined and
                                         self.parent_name in ('Base', 'db.Model') and
                                         set(_get_column_names(constraint)) == pk_column_names and
                                         target_table.name != table.name) # Avoid self-referential as joined parent

                if is_joined_inheritance:
                    self.parent_name = target_cls_name
                else:
                    relationship_ = ManyToOneRelationship(self.name, target_cls_name, constraint, inflect_engine)
                    self._add_attribute(relationship_.preferred_name, relationship_)

        for association_table_obj in association_tables:
            fk_constraints = [c for c in association_table_obj.constraints if isinstance(c, ForeignKeyConstraint)]
            fk_constraints.sort(key=_get_constraint_sort_key)
            if len(fk_constraints) == 2:
                fk_to_self = None
                fk_to_other = None
                for fk_constr in fk_constraints:
                    if any(elem.column.table == self.table for elem in fk_constr.elements):
                        fk_to_self = fk_constr
                    else:
                        fk_to_other = fk_constr

                if fk_to_self and fk_to_other:
                    target_table_for_relation = fk_to_other.elements[0].column.table
                    target_cls_name = self._tablename_to_classname(target_table_for_relation.name, inflect_engine)

                    relationship_ = ManyToManyRelationship(self.name, target_cls_name, association_table_obj, inflect_engine)
                    self._add_attribute(relationship_.preferred_name, relationship_)


    @staticmethod
    def _tablename_to_classname(tablename, inflect_engine):
        classname = str(inflect_engine.singular_noun(tablename) or '')
        return ''.join(part[:1].upper() + part[1:] for part in classname.split('_'))


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
            collector.add_literal_import('sqlalchemy.orm', 'relationship')
        for child in self.children: # For joined table inheritance
            child.add_imports(collector)

    def render(self):
        global _dataclass
        text = 'class {0}({1}):\n'.format(self.name, self.parent_name)
        if _dataclass: # Original dataclass logic
            text = '@dataclass\n' + text
        text += '    __tablename__ = {0!r}\n'.format(self.table.name)

        table_args_list = []
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if isinstance(constraint, ForeignKeyConstraint) and len(constraint.columns) == 1:
                continue # Rendered on Column by _render_column
            if isinstance(constraint, UniqueConstraint) and len(constraint.columns) == 1:
                col_is_unique_on_column_def = getattr(constraint.columns[0], 'unique', False)
                if col_is_unique_on_column_def:
                    continue
            table_args_list.append(_render_constraint(constraint))

        for index in self.table.indexes:
            if len(index.columns) > 1 or \
               (len(index.columns) == 1 and not (getattr(index.columns[0], 'index', False) or getattr(index.columns[0], 'unique', False))):
                   table_args_list.append(_render_index(index))

        table_kwargs_dict = {}
        if self.schema:
            table_kwargs_dict['schema'] = self.schema

        if hasattr(self.table, 'comment') and self.table.comment and not self.codegen.nocomments:
            table_kwargs_dict['comment'] = self.table.comment

        if table_args_list or table_kwargs_dict:
            rendered_args = []
            rendered_args.extend(table_args_list)
            if table_kwargs_dict:
                kwargs_str_parts = [f"{repr(k)}: {repr(v)}" for k, v in sorted(table_kwargs_dict.items())]
                rendered_args.append(f"{{{', '.join(kwargs_str_parts)}}}")

            if rendered_args:
                final_args_str = ',\n        '.join(rendered_args)
                if len(rendered_args) == 1 and not final_args_str.endswith(','):
                     if not (final_args_str.startswith("{") and final_args_str.endswith("}")):
                        final_args_str += ','
                text += '    __table_args__ = (\n        {0}\n    )\n'.format(final_args_str)

        text += '\n'

        for attr, column_obj in self.attributes.items():
            if isinstance(column_obj, Column):
                show_name_flag = attr != column_obj.name
                if _dataclass:
                    text += '    {0} : {1}\n'.format(attr, column_obj.type.python_type.__name__)
                text += '    {0} = {1}\n'.format(attr, _render_column(self, column_obj, show_name_flag))

        if any(isinstance(value, Relationship) for value in self.attributes.values()):
            text += '\n'
        for attr, relationship_obj in self.attributes.items():
            if isinstance(relationship_obj, Relationship):
                text += '    {0} = {1}\n'.format(attr, relationship_obj.render())

        for child_class in self.children:
            text += '\n\n' + child_class.render()
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
        prepend = 'db.' if hasattr(self, '_codegen') and self._codegen and self._codegen.flask else 'sa.orm.'

        text = prepend + 'relationship('
        args = [repr(self.target_cls)]

        rendered_kwargs = []
        for key, value in self.kwargs.items():
            rendered_kwargs.append(f"{key}={value}")

        args.extend(rendered_kwargs)

        if 'secondaryjoin' in self.kwargs or len(args) > 2:
            text += '\n        '
            delimiter, end = ',\n        ', '\n    )'
        else:
            delimiter, end = ', ', ')'

        return text + delimiter.join(args) + end

    def make_backref(self, relationships, classes):
        target_class_model = classes.get(self.target_cls)

        base_backref_candidate = _underscore(self.backref_name)
        current_backref = base_backref_candidate
        suffix_num = 0

        used_backrefs_for_target = {
            rel.backref_name for rel in relationships
            if isinstance(rel, Relationship) and hasattr(rel, 'kwargs') and 'backref' in rel.kwargs and rel.target_cls == self.target_cls
        }

        if target_class_model and hasattr(target_class_model, 'attributes'):
            used_backrefs_for_target.update(target_class_model.attributes.keys())


        while current_backref in used_backrefs_for_target:
            suffix_num += 1
            current_backref = f"{base_backref_candidate}_{suffix_num}"

        self.backref_name = current_backref
        self.kwargs['backref'] = repr(current_backref)


class ManyToOneRelationship(Relationship):
    def __init__(self, source_cls, target_cls, constraint, inflect_engine):
        super(ManyToOneRelationship, self).__init__(source_cls, target_cls)
        self._codegen = constraint.table._codegen

        column_names = _get_column_names(constraint)
        colname_on_source_table = column_names[0]

        if colname_on_source_table.endswith('_id') or colname_on_source_table.endswith('_fk'):
            base_name = re.sub(r'(_id|_fk)$', '', colname_on_source_table)
            self.preferred_name = inflect_engine.singular_noun(base_name) or base_name
        else:
            target_table_name = constraint.elements[0].column.table.name
            self.preferred_name = inflect_engine.singular_noun(target_table_name) or target_table_name

        local_fk_columns_set = set(col.name for col in constraint.columns)
        if constraint.table.primary_key and set(pk_col.name for pk_col in constraint.table.primary_key.columns) == local_fk_columns_set:
            self.kwargs['uselist'] = 'False'
        else:
            for uc in constraint.table.constraints:
                if isinstance(uc, UniqueConstraint) and set(uc_col.name for uc_col in uc.columns) == local_fk_columns_set:
                    self.kwargs['uselist'] = 'False'
                    break

        if source_cls == target_cls:
            self.preferred_name = 'parent' if self.kwargs.get('uselist') == 'False' else 'children_relationship'

            pk_cols_on_target_repr = [f"{target_cls}.{pk_col.name}" for pk_col in constraint.elements[0].column.table.primary_key]
            if len(pk_cols_on_target_repr) == 1:
                 self.kwargs['remote_side'] = f"[{repr(pk_cols_on_target_repr[0])}]"
            else:
                 self.kwargs['remote_side'] = repr(pk_cols_on_target_repr)

        join_conditions = []
        for i, fk_element in enumerate(constraint.elements):
            local_col_name = constraint.columns[i].name
            remote_col_name = fk_element.column.name
            join_conditions.append(f"{source_cls}.{local_col_name} == {target_cls}.{remote_col_name}")

        if len(join_conditions) > 1:
            self.kwargs['primaryjoin'] = repr(f"and_({', '.join(join_conditions)})")
        else:
            self.kwargs['primaryjoin'] = repr(join_conditions[0])


class ManyToManyRelationship(Relationship):
    def __init__(self, source_cls, target_cls, association_table, inflect_engine):
        super(ManyToManyRelationship, self).__init__(source_cls, target_cls)
        self._codegen = association_table._codegen

        prefix = association_table.schema + '.' if association_table.schema is not None else ''
        self.kwargs['secondary'] = repr(prefix + association_table.name)

        self.preferred_name = inflect_engine.plural_noun(target_cls.lower())
        if not self.preferred_name:
             self.preferred_name = target_cls.lower() + '_collection'


        fk_constraints = [c for c in association_table.constraints if isinstance(c, ForeignKeyConstraint)]
        fk_constraints.sort(key=lambda fk: fk.elements[0].column.table.name)
        fk_to_source_table = None
        fk_to_target_table = None

        for fk_constr in fk_constraints:
            if any(elem.column.table.name == _underscore(source_cls) for elem in fk_constr.elements):
                fk_to_source_table = fk_constr
            elif any(elem.column.table.name == _underscore(target_cls) for elem in fk_constr.elements):
                fk_to_target_table = fk_constr

        if not fk_to_source_table or not fk_to_target_table:
            if source_cls == target_cls and len(fk_constraints) == 2:
                fk_to_source_table = fk_constraints[0]
                fk_to_target_table = fk_constraints[1]
                self.preferred_name = inflect_engine.plural_noun(target_cls.lower()) or (target_cls.lower()+"_collection")

        if fk_to_source_table:
            pri_join_conds = []
            for i, elem in enumerate(fk_to_source_table.elements):
                assoc_table_fk_col_name = fk_to_source_table.columns[i].name
                pri_join_conds.append(f"{source_cls}.{source_table_pk_col_name} == {association_table.name}.c.{assoc_table_fk_col_name}")
            self.kwargs['primaryjoin'] = repr(f"and_({', '.join(pri_join_conds)})") if len(pri_join_conds) > 1 else repr(pri_join_conds[0])

        if fk_to_target_table:
            sec_join_conds = []
            for i, elem in enumerate(fk_to_target_table.elements):
                assoc_table_fk_col_name = fk_to_target_table.columns[i].name
                sec_join_conds.append(f"{target_cls}.{target_table_pk_col_name} == {association_table.name}.c.{assoc_table_fk_col_name}")
            self.kwargs['secondaryjoin'] = repr(f"and_({', '.join(sec_join_conds)})") if len(sec_join_conds) > 1 else repr(sec_join_conds[0])

        self.backref_name = inflect_engine.plural_noun(_underscore(source_cls)) or (_underscore(source_cls) + "_collection")


class CodeGenerator(object):
    header = '# coding: utf-8\n"""\nAuto-generated by sqlacodegen-modified.\n"""'
    footer = ''

    def __init__(self, metadata, noindexes=False, noconstraints=False,
                 nojoined=False, noinflect=False, nobackrefs=False,
                 flask=False, ignore_cols=None, noclasses=False, nocomments=False, notables=False, dataclass=False):
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
            if table_name in ('alembic_version', 'migrate_version'):
                continue

            fk_constraints = [const for const in table_obj.constraints if isinstance(const, ForeignKeyConstraint)]

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
                 self.collector.add_literal_import('flask_sqlalchemy', 'SQLAlchemy')
            else:
                 self.collector.add_literal_import('sqlalchemy.ext.declarative', 'declarative_base')
                 self.collector.add_literal_import('sqlalchemy', 'MetaData')
            if self.dataclass:
                 self.collector.add_literal_import('dataclasses', 'dataclass')


        self.classes = {}

        sorted_tables = sorted(metadata.tables.values(), key=lambda t: (t.schema or '', t.name))

        for table in sorted_tables:
            if table.name in ('alembic_version', 'migrate_version'):
                continue
            if table.name in association_table_names and not notables:
                if notables:
                     model = ModelTable(table, self)
                     self.models.append(model)
                     model.add_imports(self.collector)
                continue

            if noindexes: table.indexes.clear()
            if noconstraints:
                table.constraints = {c for c in table.constraints if isinstance(c, PrimaryKeyConstraint)}

            for column in table.columns:
                self._process_column_enum_type(column)

            if notables:
                model = ModelTable(table, self)
            elif noclasses or not table.primary_key:
                model = ModelTable(table, self)
            else:
                relevant_assoc_tables = [metadata.tables[name] for name in association_table_names]

                model = ModelClass(table, relevant_assoc_tables, self.inflect_engine, not nojoined, self.collector, self)
                self.classes[model.name] = model

            self.models.append(model)
            model.add_imports(self.collector)

        if not notables and not noclasses:
            for model_class_instance in list(self.models):
                if isinstance(model_class_instance, ModelClass) and model_class_instance.parent_name not in ('Base', 'db.Model'):
                    parent_class_model = self.classes.get(model_class_instance.parent_name)
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
        """Helper to process Enum types on columns and register them."""
        coltype = column.type
        process_this_enum = None
        is_array = False

        if isinstance(coltype, Enum):
            process_this_enum = coltype
        elif isinstance(coltype, ARRAY) and isinstance(coltype.item_type, Enum):
            process_this_enum = coltype.item_type
            is_array = True

        if process_this_enum and process_this_enum.enums:
            py_enum_name = process_this_enum.name
            if not py_enum_name:
                self.enum_counter += 1
                py_enum_name = f"EnumType{self.enum_counter}"
            else:
                py_enum_name = _convert_to_valid_identifier(py_enum_name)
                if py_enum_name[0].islower():
                     py_enum_name = py_enum_name[0].upper() + py_enum_name[1:]

            sql_enum_key = (process_this_enum.name, tuple(sorted(process_this_enum.enums)))

            if sql_enum_key not in self.enum_registry:
                temp_py_name = py_enum_name
                py_enum_name_counter = 0
                while temp_py_name in self.py_enum_definitions and \
                      tuple(sorted(self.py_enum_definitions[temp_py_name])) != tuple(sorted(process_this_enum.enums)):
                    py_enum_name_counter +=1
                    temp_py_name = f"{py_enum_name}_{py_enum_name_counter}"
                py_enum_name = temp_py_name

                self.enum_registry[sql_enum_key] = py_enum_name
                self.py_enum_definitions[py_enum_name] = list(process_this_enum.enums)

                self.collector.add_literal_import('enum', 'Enum')
            else:
                py_enum_name = self.enum_registry[sql_enum_key]

            process_this_enum.name = py_enum_name
            if is_array:
                column.type.item_type.name = py_enum_name
            else:
                column.type.name = py_enum_name


    def render(self, outfile=sys.stdout):
        print(self.header, file=outfile)

        if self.py_enum_definitions:
            self.collector.add_literal_import('enum', 'Enum')

        rendered_imports = self.collector.render()
        if rendered_imports:
             print(rendered_imports + '\n', file=outfile)

        if self.py_enum_definitions:

            for py_name, values in self.py_enum_definitions.items():
                print(f"class {py_name}(Enum):", file=outfile)
                for value in values:
                    member_name = _convert_to_valid_identifier(value.upper())
                    if not member_name.isidentifier():
                        member_name = f"M_{member_name}"
                    print(f"    {member_name} = {repr(value)}", file=outfile)
                print(f"\n{py_name}_values = [e.value for e in {py_name}]\n", file=outfile)

        if self.flask:
            print('db = SQLAlchemy()', file=outfile)
        else:
            if any(isinstance(model, ModelClass) for model in self.models if isinstance(model, ModelClass)):
                print('\nBase = declarative_base()\nmetadata = Base.metadata', file=outfile)
            elif self.models:
                print('\nmetadata = MetaData()', file=outfile)

        top_level_models_to_render = [m for m in self.models if not (isinstance(m, ModelClass) and m.parent_name not in ('Base', 'db.Model'))]

        for model in top_level_models_to_render:
            print('\n\n', file=outfile)
            print(model.render().rstrip('\n'), file=outfile)

        if self.footer:
            print(self.footer, file=outfile)
