
"""Contains the code generation logic and helper functions."""
from collections import defaultdict
from keyword import iskeyword
import inspect
import sys
import re

from sqlalchemy import (Enum, ForeignKeyConstraint, PrimaryKeyConstraint, CheckConstraint, UniqueConstraint, Table,
                        Column, ARRAY)
from sqlalchemy.schema import ForeignKey
from sqlalchemy.util import OrderedDict
from sqlalchemy.types import Boolean, String
import sqlalchemy

try:
    from sqlalchemy.sql.expression import text, TextClause
except ImportError:
    # SQLAlchemy < 0.8
    from sqlalchemy.sql.expression import text, _TextClause as TextClause

_re_boolean_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \(0, 1\)")
_re_column_name = re.compile(r'(?:(["`]?)(?:.*)\1\.)?(["`]?)(.*)\2')
_re_enum_check_constraint = re.compile(r"(?:(?:.*?)\.)?(.*?) IN \((.+)\)")
_re_enum_item = re.compile(r"'(.*?)(?<!\\)'")
_re_invalid_identifier = re.compile(r'[^a-zA-Z0-9_]' if sys.version_info[0] < 3 else r'(?u)\W')
_re_invalid_relationship = re.compile(r'[^a-zA-Z0-9._()\[\]{}= \'",]')

_re_first_cap = re.compile('(.)([A-Z][a-z]+)')
_re_all_cap = re.compile('([a-z0-9])([A-Z])')

_dataclass = False


class _DummyInflectEngine(object):
    def singular_noun(self, noun):
        return noun
    def plural_noun(self, noun):
        import inflect
        inflect_engine = inflect.engine()
        return inflect_engine.plural_noun(noun)


def _get_column_names(constraint):
    if isinstance(constraint.columns, list):
        return constraint.columns
    return list(constraint.columns.keys())


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
        return 'C{0}'.format(constraint.sqltext)
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
        params = list(sig.parameters.keys())
        defaults = []
        for param in sig.parameters.values():
            if param.default is not inspect.Parameter.empty:
                defaults.append(param.default)
            else:
                defaults.append(None)
        defaults = tuple(d for d in defaults if d is not None) or None
        return type('ArgSpec', (), {'args': params, 'defaults': defaults})()
    except TypeError:
        if method is object.__init__:
            sig = inspect.signature(lambda self: None)
        else:
            sig = inspect.signature(lambda self, *args, **kwargs: None)
        params = list(sig.parameters.keys())
        defaults = []
        for param in sig.parameters.values():
            if param.default is not inspect.Parameter.empty:
                defaults.append(param.default)
            else:
                defaults.append(None)
        defaults = tuple(d for d in defaults if d is not None) or None
        return type('ArgSpec', (), {'args': params, 'defaults': defaults})()


def _render_column_type(codegen, coltype):
    prepend = 'db.' if codegen.flask else ''
    args = []
    if isinstance(coltype, Enum):
        # Use the registered enum name directly
        if coltype.name in codegen.enum_registry.values():
            return f"{prepend}Enum({coltype.name})"
        else:
            args.extend(repr(arg) for arg in coltype.enums)
            if coltype.name is not None:
                args.append('name={0!r}'.format(coltype.name))
    elif isinstance(coltype, ARRAY) and isinstance(coltype.item_type, Enum):
        if coltype.item_type.name in codegen.enum_registry.values():
            return f"{prepend}ARRAY({prepend}Enum({coltype.item_type.name}))"
        else:
            args.extend(repr(arg) for arg in coltype.item_type.enums)
            if coltype.item_type.name is not None:
                args.append('name={0!r}'.format(coltype.item_type.name))
            text = f"{prepend}ARRAY({prepend}Enum({', '.join(args)}))"
            return text
    else:
        argspec = _getargspec_init(coltype.__class__.__init__)
        defaults = dict(zip(argspec.args[-len(argspec.defaults or ()):], argspec.defaults or ()))
        missing = object()
        use_kwargs = False
        for attr in argspec.args[1:]:
            if attr.startswith('_'):
                continue
            value = getattr(coltype, attr, missing)
            default = defaults.get(attr, missing)
            if value is missing or value == default:
                use_kwargs = True
            elif use_kwargs:
                args.append('{0}={1}'.format(attr, repr(value)))
            else:
                args.append(repr(value))

    text = prepend + coltype.__class__.__name__
    if text == f"{prepend}ENUM":
        text = f"{prepend}Enum"
    if args:
        text += '({0})'.format(', '.join(args))
    return text

def _render_column(self, column, show_name):
    prepend = 'db.' if self.codegen.flask else ''
    kwarg = []
    is_sole_pk = column.primary_key and len(column.table.primary_key) == 1
    dedicated_fks = [c for c in column.foreign_keys if len(c.constraint.columns) == 1]
    is_unique = any(isinstance(c, UniqueConstraint) and set(c.columns) == set([column])
                    for c in column.table.constraints)
    is_unique = is_unique or any(i.unique and set(i.columns) == set([column]) for i in column.table.indexes)
    has_index = any(set(i.columns) == set([column]) for i in column.table.indexes)
    render_coltype = not dedicated_fks or any(fk.column is column for fk in dedicated_fks)

    if column.key != column.name:
        kwarg.append('key')
    if column.primary_key:
        kwarg.append('primary_key')
    if not column.nullable and not is_sole_pk:
        kwarg.append('nullable')
    if is_unique:
        column.unique = True
        kwarg.append('unique')
    elif has_index:
        column.index = True
        kwarg.append('index')
    if column.server_default:
        server_default = f'server_default={prepend}FetchedValue()'

    comment = getattr(column, 'comment', None)
    return prepend + 'Column({0})'.format(', '.join(
        ([repr(column.name)] if show_name else []) +
        ([_render_column_type(self.codegen, column.type)] if render_coltype else []) +
        [_render_constraint(x) for x in dedicated_fks] +
        [repr(x) for x in column.constraints] +
        ['{0}={1}'.format(k, repr(getattr(column, k))) for k in kwarg] +
        ([server_default] if column.server_default else []) +
        (['info={!r}'.format(comment)] if comment else [])
    ))


def _render_constraint(constraint):
    # Determine the table based on the constraint type
    if isinstance(constraint, ForeignKey):
        table = constraint.column.table  # ForeignKey uses the target column's table
    else:
        table = constraint.table  # Other constraints (e.g., ForeignKeyConstraint) have a table attribute
    prepend = 'db.' if hasattr(table, '_codegen') and table._codegen.flask else ''

    def render_fk_options(*opts):
        opts = [repr(opt) for opt in opts]
        for attr in 'ondelete', 'onupdate', 'deferrable', 'initially', 'match':
            value = getattr(constraint, attr, None)
            if value:
                opts.append('{0}={1!r}'.format(attr, value))
        return ', '.join(opts)

    if isinstance(constraint, ForeignKey):
        remote_column = '{0}.{1}'.format(constraint.column.table.fullname, constraint.column.name)
        return prepend + 'ForeignKey({0})'.format(render_fk_options(remote_column))
    elif isinstance(constraint, ForeignKeyConstraint):
        local_columns = _get_column_names(constraint)
        remote_columns = ['{0}.{1}'.format(fk.column.table.fullname, fk.column.name)
                          for fk in constraint.elements]
        return prepend + 'ForeignKeyConstraint({0})'.format(render_fk_options(local_columns, remote_columns))
    elif isinstance(constraint, CheckConstraint):
        return prepend + 'CheckConstraint({0!r})'.format(_get_compiled_expression(constraint.sqltext))
    elif isinstance(constraint, UniqueConstraint):
        columns = [repr(col.name) for col in constraint.columns]
        return prepend + 'UniqueConstraint({0})'.format(', '.join(columns))


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
    prepend = 'db.' if hasattr(index.table, '_codegen') and index.table._codegen.flask else ''
    columns = [repr(col.name) for col in index.columns]
    return prepend + 'Index({0!r}, {1})'.format(index.name, ', '.join(columns))


class ImportCollector(OrderedDict):
    def add_import(self, obj):
        type_ = type(obj) if not isinstance(obj, type) else obj
        if type_.__module__.startswith('sqlalchemy'):
            pkgname = type_.__module__
            top_level_types = {'Column', 'Table', 'ForeignKey', 'ForeignKeyConstraint', 'CheckConstraint',
                              'UniqueConstraint', 'Index', 'Enum', 'ARRAY', 'Boolean', 'String', 'Integer',
                              'Numeric', 'Date', 'DateTime', 'Text'}
            if type_.__name__ in top_level_types:
                pkgname = 'sqlalchemy'
        else:
            pkgname = type_.__module__
        self.add_literal_import(pkgname, type_.__name__)

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
        self.codegen = codegen
        self.table._codegen = codegen  # Attach codegen for prefix access

        for column in table.columns:
            cls = column.type.__class__
            for supercls in cls.__mro__:
                if hasattr(supercls, '__visit_name__'):
                    cls = supercls
                if supercls.__name__ != supercls.__name__.upper() and not supercls.__name__.startswith('_'):
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
                collector.add_literal_import('sqlalchemy.schema', 'FetchedValue')
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, ForeignKeyConstraint):
                if len(constraint.columns) > 1:
                    collector.add_literal_import('sqlalchemy', 'ForeignKeyConstraint')
                else:
                    collector.add_literal_import('sqlalchemy', 'ForeignKey')
            elif isinstance(constraint, UniqueConstraint):
                if len(constraint.columns) > 1:
                    collector.add_literal_import('sqlalchemy', 'UniqueConstraint')
            elif not isinstance(constraint, PrimaryKeyConstraint):
                collector.add_import(constraint)
        for index in self.table.indexes:
            if len(index.columns) > 1:
                collector.add_import(index)


class ModelTable(Model):
    def add_imports(self, collector):
        super(ModelTable, self).add_imports(collector)
        collector.add_import(Table)

    def render(self):
        prepend = 'db.' if self.codegen.flask else ''
        met = ' metadata,' if not self.codegen.flask else ''
        text = 't_{0} = {1}Table(\n    {0!r},{2}\n'.format(self.table.name, prepend, met)
        for column in self.table.columns:
            text += '    {0},\n'.format(_render_column(self, column, True))
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if isinstance(constraint, (ForeignKeyConstraint, UniqueConstraint)) and len(constraint.columns) == 1:
                continue
            text += '    {0},\n'.format(_render_constraint(constraint))
        for index in self.table.indexes:
            if len(index.columns) > 1:
                text += '    {0},\n'.format(_render_index(index))
        if self.schema:
            text += "    schema='{0}',\n".format(self.schema)
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
                target_cls = self._tablename_to_classname(constraint.elements[0].column.table.name, inflect_engine)
                if (detect_joined and self.parent_name in ('Base', 'db.Model') and
                        set(_get_column_names(constraint)) == pk_column_names):
                    self.parent_name = target_cls
                else:
                    relationship_ = ManyToOneRelationship(self.name, target_cls, constraint, inflect_engine)
                    self._add_attribute(relationship_.preferred_name, relationship_)

        for association_table in association_tables:
            fk_constraints = [c for c in association_table.constraints if isinstance(c, ForeignKeyConstraint)]
            fk_constraints.sort(key=_get_constraint_sort_key)
            target_cls = self._tablename_to_classname(fk_constraints[1].elements[0].column.table.name, inflect_engine)
            relationship_ = ManyToManyRelationship(self.name, target_cls, association_table, inflect_engine)
            self._add_attribute(relationship_.preferred_name, relationship_)

    @staticmethod
    def _tablename_to_classname(tablename, inflect_engine):
        camel_case_name = ''.join(part[:1].upper() + part[1:] for part in re.split(r'_|-', tablename))
        return inflect_engine.singular_noun(camel_case_name) or camel_case_name

    def _add_attribute(self, attrname, value):
        attrname = tempname = _convert_to_valid_identifier(attrname)
        counter = 1
        while tempname in self.attributes:
            tempname = attrname + str(counter)
            counter += 1
        self.attributes[tempname] = value
        return tempname

    def add_imports(self, collector):
        super(ModelClass, self).add_imports(collector)
        if any(isinstance(value, Relationship) for value in self.attributes.values()):
            collector.add_literal_import('sqlalchemy.orm', 'relationship')
        for child in self.children:
            child.add_imports(collector)

    def render(self):
        global _dataclass
        text = 'class {0}({1}):\n'.format(self.name, self.parent_name)
        if _dataclass:
            text = '@dataclass\n' + text
        text += '    __tablename__ = {0!r}\n'.format(self.table.name)

        table_args = []
        for constraint in sorted(self.table.constraints, key=_get_constraint_sort_key):
            if isinstance(constraint, PrimaryKeyConstraint):
                continue
            if isinstance(constraint, (ForeignKeyConstraint, UniqueConstraint)) and len(constraint.columns) == 1:
                continue
            table_args.append(_render_constraint(constraint))
        for index in self.table.indexes:
            if len(index.columns) > 1:
                table_args.append(_render_index(index))

        table_kwargs = {}
        if self.schema:
            table_kwargs['schema'] = self.schema

        kwargs_items = ', '.join('{0!r}: {1!r}'.format(key, table_kwargs[key]) for key in table_kwargs)
        kwargs_items = '{{{0}}}'.format(kwargs_items) if kwargs_items else None
        if table_kwargs and not table_args:
            text += '    __table_args__ = {0}\n'.format(kwargs_items)
        elif table_args:
            if kwargs_items:
                table_args.append(kwargs_items)
            if len(table_args) == 1:
                table_args[0] += ','
            text += '    __table_args__ = (\n        {0}\n    )\n'.format(',\n        '.join(table_args))

        text += '\n'
        for attr, column in self.attributes.items():
            if isinstance(column, Column):
                show_name = attr != column.name
                if _dataclass:
                    text += '    ' + attr + ' : ' + column.type.python_type.__name__ + '\n'
                text += '    {0} = {1}\n'.format(attr, _render_column(self, column, show_name))

        if any(isinstance(value, Relationship) for value in self.attributes.values()):
            text += '\n'
        for attr, relationship in self.attributes.items():
            if isinstance(relationship, Relationship):
                text += '    {0} = {1}\n'.format(attr, relationship.render())

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

    def render(self):
        prepend = 'db.' if hasattr(self, '_codegen') and self._codegen.flask else ''
        text = prepend + 'relationship('
        args = [repr(self.target_cls)]
        if 'secondaryjoin' in self.kwargs:
            text += '\n        '
            delimiter, end = ',\n        ', '\n    )'
        else:
            delimiter, end = ', ', ')'
        args.extend([key + '=' + value for key, value in self.kwargs.items()])
        return _re_invalid_relationship.sub('_', text + delimiter.join(args) + end)

    def make_backref(self, relationships, classes):
        """Generate a unique backref name based on source table and column role."""
        # Base backref from source class
        base_backref = _underscore(self.source_cls)  # e.g., 'pj_task' or 'assoc_rat_swarm'

        if 'primaryjoin' in self.kwargs and not self.kwargs.get('secondary'):  # Many-to-one
            # Extract FK column name from primaryjoin
            join_str = self.kwargs['primaryjoin'].strip("'")
            if ' == ' in join_str:
                fk_part = join_str.split(' == ')[0]
                col_name = fk_part.split('.')[-1]  # e.g., 'assigned_to_fk'
                role = col_name.replace('_fk', '').replace('id_', '')  # e.g., 'assigned_to'
                if role == 'parent':  # Self-referential
                    backref_name = 'subtasks'
                else:
                    # Combine source table and role for uniqueness
                    backref_name = f"{role}_{base_backref}s"  # e.g., 'assigned_to_pj_tasks'
            else:
                backref_name = f"{base_backref}_related"
        elif 'secondary' in self.kwargs:  # Many-to-many
            # Use secondary table name for context
            secondary_table = self.kwargs['secondary'].strip("'").split('.')[-1]
            backref_name = f"{base_backref}_{secondary_table}s"  # e.g., 'pj_task_assoc_table_items'
        else:
            backref_name = f"{base_backref}_related"

        # Check for conflicts with existing backrefs or attributes
        target_model = classes.get(self.target_cls)
        existing_names = {r.backref_name for r in relationships if r.target_cls == self.target_cls}
        if target_model:
            existing_names.update(target_model.attributes.keys())  # Include target’s columns/relationships

        original_backref = backref_name
        suffix = 0
        while backref_name in existing_names:
            suffix += 1
            backref_name = f"{original_backref}_{suffix}"

        self.backref_name = backref_name
        self.kwargs['backref'] = repr(backref_name)

class ManyToOneRelationship(Relationship):
    def __init__(self, source_cls, target_cls, constraint, inflect_engine):
        super(ManyToOneRelationship, self).__init__(source_cls, target_cls)
        self._codegen = constraint.table._codegen  # Attach codegen for prefix
        column_names = _get_column_names(constraint)
        colname = column_names[0]
        tablename = constraint.elements[0].column.table.name
        if not colname.endswith('_id'):
            self.preferred_name = inflect_engine.singular_noun(tablename) or tablename
        else:
            self.preferred_name = colname[:-3]
        self.backref_name = inflect_engine.plural_noun(self.backref_name)
        if any(isinstance(c, (PrimaryKeyConstraint, UniqueConstraint)) and
               set(col.name for col in c.columns) == set(column_names)
               for c in constraint.table.constraints):
            self.kwargs['uselist'] = 'False'
        if source_cls == target_cls:
            self.preferred_name = 'parent' if not colname.endswith('_id') else colname[:-3]
            pk_col_names = [col.name for col in constraint.table.primary_key]
            self.kwargs['remote_side'] = '[{0}]'.format(', '.join(pk_col_names))
        if len(constraint.elements) > 1:
            self.kwargs['primaryjoin'] = "'and_({0})'".format(', '.join(['{0}.{1} == {2}.{3}'.format(source_cls, k.parent.name, target_cls, k.column.name)
                        for k in constraint.elements]))
        else:
            self.kwargs['primaryjoin'] = "'{0}.{1} == {2}.{3}'".format(source_cls, column_names[0], target_cls,
                                                                       constraint.elements[0].column.name)


class ManyToManyRelationship(Relationship):
    def __init__(self, source_cls, target_cls, association_table, inflect_engine):
        super(ManyToManyRelationship, self).__init__(source_cls, target_cls)
        self._codegen = association_table._codegen  # Attach codegen for prefix
        prefix = association_table.schema + '.' if association_table.schema is not None else ''
        self.kwargs['secondary'] = repr(prefix + association_table.name)
        constraints = [c for c in association_table.constraints if isinstance(c, ForeignKeyConstraint)]
        constraints.sort(key=_get_constraint_sort_key)
        colname = _get_column_names(constraints[1])[0]
        tablename = constraints[1].elements[0].column.table.name
        self.preferred_name = tablename if not colname.endswith('_id') else colname[:-3] + 's'
        self.backref_name = inflect_engine.plural_noun(self.backref_name)
        if source_cls == target_cls:
            self.preferred_name = 'parents' if not colname.endswith('_id') else colname[:-3] + 's'
            pri_pairs = zip(_get_column_names(constraints[0]), constraints[0].elements)
            sec_pairs = zip(_get_column_names(constraints[1]), constraints[1].elements)
            pri_joins = ['{0}.{1} == {2}.c.{3}'.format(source_cls, elem.column.name, association_table.name, col)
                         for col, elem in pri_pairs]
            sec_joins = ['{0}.{1} == {2}.c.{3}'.format(target_cls, elem.column.name, association_table.name, col)
                         for col, elem in sec_pairs]
            self.kwargs['primaryjoin'] = (
                repr('and_({0})'.format(', '.join(pri_joins))) if len(pri_joins) > 1 else repr(pri_joins[0]))
            self.kwargs['secondaryjoin'] = (
                repr('and_({0})'.format(', '.join(sec_joins))) if len(sec_joins) > 1 else repr(sec_joins[0]))


class CodeGenerator(object):
    header = '# coding: utf-8'
    footer = ''

    def __init__(self, metadata, noindexes=False, noconstraints=False,
                 nojoined=False, noinflect=False, nobackrefs=False,
                 flask=False, ignore_cols=None, noclasses=False, nocomments=False, notables=False, dataclass=False):
        super(CodeGenerator, self).__init__()

        self.flask = flask
        if noinflect:
            inflect_engine = _DummyInflectEngine()
        else:
            import inflect
            inflect_engine = inflect.engine()

        _ignore_columns = ignore_cols or []
        self.nocomments = nocomments
        self.dataclass = dataclass
        if self.dataclass:
            global _dataclass
            _dataclass = True

        self.enum_registry = {}  # Maps (name, values) to generated name
        self.enum_counter = 0

        links = defaultdict(lambda: [])
        association_tables = set()
        for table in metadata.tables.values():
            fk_constraints = [constr for constr in table.constraints if isinstance(constr, ForeignKeyConstraint)]
            if len(fk_constraints) == 2 and all(col.foreign_keys for col in table.columns if col.name not in _ignore_columns):
                association_tables.add(table.name)
                tablename = sorted(fk_constraints, key=_get_constraint_sort_key)[0].elements[0].column.table.name
                links[tablename].append(table)

        self.models = []
        self.collector = ImportCollector()
        classes = {}
        for table in sorted(metadata.tables.values(), key=lambda t: (t.schema or '', t.name)):
            if table.name in ('alembic_version', 'migrate_version'):
                continue

            if noindexes:
                table.indexes.clear()

            if noconstraints:
                table.constraints = set([table.primary_key])
                table.foreign_keys.clear()
                for col in table.columns:
                    col.foreign_keys.clear()
            else:
                for constraint in table.constraints.copy():
                    if isinstance(constraint, CheckConstraint):
                        sqltext = _get_compiled_expression(constraint.sqltext)
                        match = _re_boolean_check_constraint.match(sqltext)
                        if match:
                            colname = _re_column_name.match(match.group(1)).group(3)
                            table.constraints.remove(constraint)
                            table.c[colname].type = Boolean()
                            continue
                        match = _re_enum_check_constraint.match(sqltext)
                        if match:
                            colname = _re_column_name.match(match.group(1)).group(3)
                            items = match.group(2)
                            if isinstance(table.c[colname].type, String):
                                table.constraints.remove(constraint)
                                if not isinstance(table.c[colname].type, Enum):
                                    options = _re_enum_item.findall(items)
                                    table.c[colname].type = Enum(*options, native_enum=False)
                                continue

            # Register enums for all columns
            for column in table.columns:
                if isinstance(column.type, Enum) and column.type.enums and column.type.name:
                    enum_key = (column.type.name, tuple(column.type.enums))
                    if enum_key not in self.enum_registry:
                        enum_name = column.type.name
                        if any(k[0] == enum_name and k[1] != enum_key[1] for k in self.enum_registry):
                            self.enum_counter += 1
                            enum_name = f"{enum_name}_{self.enum_counter}"
                        self.enum_registry[enum_key] = enum_name
                elif (isinstance(column.type, ARRAY) and isinstance(column.type.item_type, Enum) and
                      column.type.item_type.enums and column.type.item_type.name):
                    enum_key = (column.type.item_type.name, tuple(column.type.item_type.enums))
                    if enum_key not in self.enum_registry:
                        enum_name = column.type.item_type.name
                        if any(k[0] == enum_name and k[1] != enum_key[1] for k in self.enum_registry):
                            self.enum_counter += 1
                            enum_name = f"{enum_name}_{self.enum_counter}"
                        self.enum_registry[enum_key] = enum_name

            if notables:
                model = ModelClass(table, links[table.name], inflect_engine, not nojoined, self.collector, self)
                classes[model.name] = model
            elif not table.primary_key or table.name in association_tables or noclasses:
                model = ModelTable(table, self)
            elif not noclasses:
                model = ModelClass(table, links[table.name], inflect_engine, not nojoined, self.collector, self)
                classes[model.name] = model

            self.models.append(model)
            model.add_imports(self.collector)

        for model in classes.values():
            if model.parent_name not in ('Base', 'db.Model'):
                classes[model.parent_name].children.append(model)
                self.models.remove(model)

        if not nobackrefs:
            for model in classes.values():
                visited = []
                for relationship in model.attributes.values():
                    if isinstance(relationship, Relationship):
                        relationship.make_backref(visited, classes)
                        visited.append(relationship)

        if self.flask:
            self.collector.add_literal_import('flask_sqlalchemy', 'SQLAlchemy')
            for model in classes.values():
                if model.parent_name == 'Base':
                    model.parent_name = 'db.Model'
        else:
            self.collector.add_literal_import('sqlalchemy.ext.declarative', 'declarative_base')
            self.collector.add_literal_import('sqlalchemy', 'MetaData')
        if self.dataclass:
            self.collector.add_literal_import('dataclasses', 'dataclass')

    def render(self, outfile=sys.stdout):

        if self.enum_registry:
            for (enum_name, enum_values), generated_name in sorted(self.enum_registry.items()):
                for value in enum_values:
                    # Force variable name to UPPERCASE, sanitize spaces/hyphens
                    safe_name = value.replace(' ', '_').replace('-', '_').upper()
                    if safe_name[0].isdigit() or iskeyword(safe_name):
                        safe_name = '_' + safe_name

        if self.flask:
        else:
            if any(isinstance(model, ModelClass) for model in self.models):
            else:

        for model in self.models:

        if self.footer:

if __name__ == "__main__":
    from sqlalchemy import MetaData, Table, Column, Integer, String, DateTime, Numeric, Date
    metadata = MetaData()

    # Define sample tables to test PjTask-like scenario
    user_ext = Table('user_ext', metadata,
                     Column('id', Integer, primary_key=True))

    project = Table('project', metadata,
                    Column('id', Integer, primary_key=True))

    pj_tasks = Table('pj_tasks', metadata,
                     Column('task_id', Integer, primary_key=True, server_default=sqlalchemy.schema.FetchedValue()),
                     Column('project_id_fk', Integer, ForeignKey('project.id'), nullable=False),
                     Column('parent_task_id_fk', Integer, ForeignKey('pj_tasks.task_id')),
                     Column('task_name', String(100), nullable=False),
                     Column('description', String),
                     Column('status', Enum('Initiated', 'Planned', 'In_Progress', name='task_status'), nullable=False,
                            server_default='Initiated'),
                     Column('priority', Enum('Low', 'Medium', 'High', 'Critical', name='task_priority'),
                            server_default='Medium'),
                     Column('story_points', Integer),
                     Column('progress', Numeric(5, 2), server_default='0.00'),
                     Column('assigned_to_fk', Integer, ForeignKey('user_ext.id'), nullable=False),
                     Column('created_by_fk', Integer, ForeignKey('user_ext.id'), nullable=False),
                     Column('updated_by_fk', Integer, ForeignKey('user_ext.id')),
                     Column('start_date', Date),
                     Column('end_date', Date),
                     Column('actual_start_date', Date),
                     Column('actual_end_date', Date),
                     Column('created_at', DateTime, server_default=sqlalchemy.schema.FetchedValue()),
                     Column('updated_at', DateTime, server_default=sqlalchemy.schema.FetchedValue()))

    generator = CodeGenerator(metadata, flask=True)
    generator.render()
