#pragma GCC diagnostic ignored "-Wstrict-prototypes"

#include <Python.h> //This must be first include!
#include "structmember.h"
#include "yices_c.h"
#include <time.h>

#pragma GCC diagnostic warning "-Wstrict-prototypes"


//#define _DBG_MEM

#ifdef _DBG_MEM
#define _DBG_RET_OBJ(OBJECT) printf("%s returning pointer %p, refcount %d\n", __func__, OBJECT, (int) OBJECT->ob_refcnt);
#define Py_DECREF(OBJ) printf("skipped decref %p\n", OBJ)
#define free(OBJ) printf("skipped free %p\n", OBJ)
#else
#define _DBG_RET_OBJ(OBJECT)
#endif



#define _TIME_Y(ARG)           if(time_y)_time_y_start = clock();          ARG; if(time_y)yices_time += clock() - _time_y_start;
//#define _TIME_Y(ARG)           ARG;
/*
#define _TIME_Y_S(ARG, SUFFIX) clock_t _time_y_start_##SUFFIX = clock(); ARG; yices_time += clock() - _time_y_start_##SUFFIX;
#define _TIME_Y_S(ARG, SUFFIX) ARG;
*/

clock_t _time_y_start;
clock_t yices_time;
int time_y = 0;

typedef unsigned char ytype_t;
const ytype_t TYPE_BOOL = 0;
const ytype_t TYPE_REAL = 1;
const ytype_t TYPE_INT = 2;

unsigned int VAR_LIST_BLOCK_SIZE = 100; //TODO: try decreasing

static PyObject *YicesFullException;

//TODO: DECREF for GetAttr and GetAttrString

PyObject* mod_self;      // This module
PyObject* mod_builtin;   // The __builtin__ module
PyObject* mod_fractions; // The fractions module

/*******************************************************************************
*********************************** Helpers ************************************
*******************************************************************************/

PyObject* ybool2pybool(lbool arg)
{
	switch(arg) {
	case l_true:
		Py_RETURN_TRUE;
	case l_false:
		Py_RETURN_FALSE;
	case l_undef:
		Py_RETURN_NONE;
	default:
        PyErr_SetString(YicesFullException, "Unexpected argument!");
        return NULL;
	}
}

/*******************************************************************************
***************************** RetractableAssertion *****************************
*******************************************************************************/

static PyTypeObject yicesfull_RetractableAssertionType;

typedef struct {
    PyObject_HEAD
    yices_context context;
    assertion_id id;
    unsigned char retracted;
} RetractableAssertion;

static RetractableAssertion* new_ra(yices_context context, assertion_id id)//, unsigned int* pushlevel)
{
	RetractableAssertion* obj = PyObject_New(RetractableAssertion, &yicesfull_RetractableAssertionType);
	obj->context = context;
	obj->id = id;
	obj->retracted = 0;
	_DBG_RET_OBJ(obj)
	return obj;
}

static PyObject* RA_str(RetractableAssertion* self)
{
	PyObject* ret = PyString_FromFormat("RetractableAssertions(id:%d, ctx:%p)", self->id, self->context);
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* RA_hash(RetractableAssertion* self)
{
	PyObject* ret = Py_BuildValue("l", self->context + self->id);
	_DBG_RET_OBJ(ret)
	return ret;
}

static int RA_cmp(RetractableAssertion* a, RetractableAssertion* b)
{
	if(a->context < b->context)
		return -1;
	if(a->context > b->context)
		return 1;
	//Contexts same
	if(a->id < b->id)
		return -1;
	if(a->id > b->id)
		return 1;
	return 0;
}

static PyObject* RA_retract(RetractableAssertion* self)
{
	if(!self->retracted)
	{
		yices_retract(self->context, self->id);
		self->retracted = 1;
	}
	Py_RETURN_NONE;
}

static PyMethodDef RetractableAssertion_methods[] = {
    {"retract", (PyCFunction) RA_retract, METH_NOARGS,  "Retracts the assertion. May be called multiple times but not at the wrong pushlevel or after popping the assertion."},
    {NULL}  /* Sentinel */
};

static PyTypeObject yicesfull_RetractableAssertionType = {
    PyObject_HEAD_INIT(NULL)
    0,                                         /*ob_size*/
    "yicesfull.RetractableAssertion",          /*tp_name*/
    sizeof(RetractableAssertion),              /*tp_basicsize*/
    0,                                         /*tp_itemsize*/
    0,                                         /*tp_dealloc*/
    0,                                         /*tp_print*/
    0,                                         /*tp_getattr*/
    0,                                         /*tp_setattr*/
    (cmpfunc) RA_cmp,                          /*tp_compare*/
    0,                                         /*tp_repr*/
    0,                                         /*tp_as_number*/
    0,                                         /*tp_as_sequence*/
    0,                                         /*tp_as_mapping*/
    0,                                         /*tp_hash */
    0,                                         /*tp_call*/
    (reprfunc)RA_str,                          /*tp_str*/
    0,                                         /*tp_getattro*/
    0,                                         /*tp_setattro*/
    0,                                         /*tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                        /*tp_flags*/
    "Represents a retractable assertion",      /* tp_doc */
    0,                                         /* tp_traverse */
    0,                                         /* tp_clear */
    0,                                         /* tp_richcompare */
    0,                                         /* tp_weaklistoffset */
    0,                                         /* tp_iter */
    0,                                         /* tp_iternext */
    RetractableAssertion_methods,              /* tp_methods */
    0,                                         /* tp_members */
    0,                                         /* tp_getset */
    0,                                         /* tp_base */
    0,                                         /* tp_dict */
    0,                                         /* tp_descr_get */
    0,                                         /* tp_descr_set */
    0,                                         /* tp_dictoffset */
    0,                                         /* tp_init */
    0,                                         /* tp_alloc */
    0,                                         /* tp_new */
};


/*******************************************************************************
*************************** YicesInternalExpression ****************************
*******************************************************************************/

static PyTypeObject yicesfull_YicesInternalExpressionType;

typedef struct {
    PyObject_HEAD
    yices_context context;
    yices_expr    expression;
    int varid; // non-negative for variables, -1 for non-variables
} YicesInternalExpression;

static YicesInternalExpression* new_yix(yices_context context, yices_expr expression)
{
	_TIME_Y(YicesInternalExpression* obj = PyObject_New(YicesInternalExpression, &yicesfull_YicesInternalExpressionType);)
	obj->context = context;
	obj->expression = expression;
	obj->varid = -1; //TODO make accessible
	_DBG_RET_OBJ(obj)
	return obj;
}

static PyObject* YIX_str(YicesInternalExpression* self)
{
	PyObject* ret = PyString_FromFormat("Yices internal expression %p for context %p with varid %i", self->expression, self->context, self->varid);
	_DBG_RET_OBJ(ret)
    return ret;
}

//Operator macros
#define YIX_N_ARY_OP_REF(OP_NAME) {"mk_"#OP_NAME, (PyCFunction) YIX_op_##OP_NAME, METH_VARARGS, "Returns expression for ("#OP_NAME" self arg[0] arg[1] ...)"}
#define YIX_N_ARY_OP_DEF(OP_NAME) static PyObject* YIX_op_##OP_NAME(YicesInternalExpression* self, PyObject* args) \
{                                                                                                         \
	PyObject* arglist;                                                                                    \
	PyObject* cls = PyObject_GetAttrString(mod_builtin, "list");                                          \
	if(cls == NULL)	                                                                                      \
		return NULL;	                                                                                  \
	if (!PyArg_ParseTuple(args, "O!", cls, (PyObject**) &arglist))	                                      \
	{	                                                                                                  \
		Py_DECREF(cls);	                                                                                  \
		return NULL;                                                                                      \
	}	                                                                                                  \
	Py_DECREF(cls);                                                                                       \
	                                                                                                      \
	/*Allocate expression list*/                                                                          \
	unsigned n = (PyList_Size(arglist) + 1);                                                              \
	yices_expr* exprs = malloc(n * sizeof(yices_expr));                                                   \
	exprs[0] = self->expression;                                                                          \
	                                                                                                      \
	/*Fill expression list*/                                                                              \
	unsigned int i;                                                                                       \
	PyObject* obj = NULL;                                                                                 \
	for(i = 1; i < n; i++)                                                                                \
	{                                                                                                     \
		obj = PyList_GetItem(arglist, i-1);                                                               \
		if(obj == NULL)                                                                                   \
		{                                                                                                 \
			free(exprs);                                                                                  \
			return NULL;                                                                                  \
		}                                                                                                 \
		                                                                                                  \
		cls = PyObject_GetAttrString(mod_self, "YicesInternalExpression");                                \
		if(cls == NULL)                                                                                   \
		{                                                                                                 \
			free(exprs);                                                                                  \
			return NULL;                                                                                  \
		}                                                                                                 \
		if(!PyObject_IsInstance(obj, cls))                                                                \
		{                                                                                                 \
			PyErr_SetString(YicesFullException, "Invalid type -- expected list of expressions");          \
			free(exprs);                                                                                  \
			Py_DECREF(cls);                                                                               \
			return NULL;                                                                                  \
		}                                                                                                 \
		Py_DECREF(cls);                                                                                   \
		if(((YicesInternalExpression*) obj)->context != self->context) {                                  \
			PyErr_SetString(YicesFullException, "Expressions from different contexts");                   \
			free(exprs);                                                                                  \
			return NULL;                                                                                  \
		}                                                                                                 \
		                                                                                                  \
		exprs[i] = ((YicesInternalExpression*) obj)->expression;                                          \
	}                                                                                                     \
	                                                                                                      \
	/*Make new expression*/                                                                               \
	_TIME_Y(yices_expr yo = yices_mk_##OP_NAME(self->context, exprs, n))                                  \
	obj = (PyObject*) new_yix(self->context, yo);                                                         \
	                                                                                                      \
	/*Done*/                                                                                              \
	free(exprs);                                                                                          \
	                                                                                                      \
	_DBG_RET_OBJ(obj)                                                                                     \
	return obj;                                                                                           \
}

#define YIX_TERNARY_OP_REF(OP_NAME) {"mk_"#OP_NAME, (PyCFunction) YIX_op_##OP_NAME, METH_VARARGS, "Returns expression for ("#OP_NAME" self arg)"}

#define YIX_TERNARY_OP_DEF(OP_NAME) static PyObject* YIX_op_##OP_NAME(YicesInternalExpression* self, PyObject* args)                    \
{                                                                                                                                       \
	YicesInternalExpression* arg1 = NULL;                                                                                               \
	YicesInternalExpression* arg2 = NULL;                                                                                               \
	PyObject* to = PyObject_GetAttrString(mod_self, "YicesInternalExpression");                                                         \
	if(to == NULL)                                                                                                                      \
		return NULL;                                                                                                                    \
	if (!PyArg_ParseTuple(args, "O!O!", to, (PyObject**) &arg1, to, (PyObject**) &arg2))                                                \
	{                                                                                                                                   \
		Py_DECREF(to);                                                                                                                  \
		return NULL;                                                                                                                    \
	}                                                                                                                                   \
	Py_DECREF(to);                                                                                                                      \
		                                                                                                                                \
	if(arg1->context != self->context || arg2->context != self->context) {                                                              \
		PyErr_SetString(YicesFullException, "Expressions from different contexts");                                                     \
		return NULL;                                                                                                                    \
	}                                                                                                                                   \
	                                                                                                                                    \
	/*Make new expression*/                                                                                                             \
	_TIME_Y(yices_expr yo = yices_mk_##OP_NAME(self->context, self->expression, arg1->expression, arg2->expression))                    \
	PyObject* obj = (PyObject*) new_yix(self->context, yo);                                                                             \
	_DBG_RET_OBJ(obj)                                                                                                                   \
	return obj;                                                                                                                         \
}

#define YIX_BINARY_OP_REF(OP_NAME) {"mk_"#OP_NAME, (PyCFunction) YIX_op_##OP_NAME, METH_VARARGS, "Returns expression for ("#OP_NAME" self arg)"}

#define YIX_BINARY_OP_DEF(OP_NAME) static PyObject* YIX_op_##OP_NAME(YicesInternalExpression* self, PyObject* args)   \
{                                                                                                                     \
	YicesInternalExpression* arg = NULL;                                                                              \
	PyObject* cls = PyObject_GetAttrString(mod_self, "YicesInternalExpression");                                      \
	if(cls == NULL)                                                                                                   \
		return NULL;                                                                                                  \
	if (!PyArg_ParseTuple(args, "O!", cls, (PyObject**) &arg))                                                        \
	{                                                                                                                 \
		Py_DECREF(cls);                                                                                               \
		return NULL;                                                                                                  \
	}                                                                                                                 \
	Py_DECREF(cls);                                                                                                   \
		                                                                                                              \
	if(arg->context != self->context) {                                                                               \
		PyErr_SetString(YicesFullException, "Expressions from different contexts");                                   \
		return NULL;                                                                                                  \
	}                                                                                                                 \
	                                                                                                                  \
	/*Make new expression*/                                                                                           \
	_TIME_Y(yices_expr yo = yices_mk_##OP_NAME(self->context, self->expression, arg->expression))                     \
	PyObject* obj = (PyObject*) new_yix(self->context, yo);                                                           \
	_DBG_RET_OBJ(obj)                                                                                                 \
	return obj;                                                                                                       \
}

#define YIX_UNARY_OP_REF(OP_NAME) {"mk_"#OP_NAME, (PyCFunction) YIX_##OP_NAME, METH_NOARGS, "Returns expression for ("#OP_NAME" self)"}

#define YIX_UNARY_OP_DEF(OP_NAME) static PyObject* YIX_##OP_NAME(YicesInternalExpression* self)    \
{                                                                                                  \
	_TIME_Y(yices_expr yo = yices_mk_##OP_NAME(self->context, self->expression))                   \
	PyObject* obj = (PyObject*) new_yix(self->context, yo);                                        \
	_DBG_RET_OBJ(obj)                                                                              \
	return obj;                                                                                    \
}

YIX_UNARY_OP_DEF(not)
YIX_BINARY_OP_DEF(eq)
YIX_BINARY_OP_DEF(diseq)
YIX_BINARY_OP_DEF(lt)
YIX_BINARY_OP_DEF(le)
YIX_BINARY_OP_DEF(gt)
YIX_BINARY_OP_DEF(ge)
YIX_TERNARY_OP_DEF(ite)
YIX_N_ARY_OP_DEF(and)
YIX_N_ARY_OP_DEF(or)
YIX_N_ARY_OP_DEF(sum)
YIX_N_ARY_OP_DEF(sub)
YIX_N_ARY_OP_DEF(mul)

static PyMethodDef YicesInternalExpression_methods[] = {
	YIX_UNARY_OP_REF(not),
    YIX_BINARY_OP_REF(eq),
    YIX_BINARY_OP_REF(lt),
    YIX_BINARY_OP_REF(le),
    YIX_BINARY_OP_REF(gt),
    YIX_BINARY_OP_REF(ge),
    YIX_BINARY_OP_REF(diseq),
    YIX_TERNARY_OP_REF(ite),
    YIX_N_ARY_OP_REF(and),
    YIX_N_ARY_OP_REF(or),
	YIX_N_ARY_OP_REF(sum),
	YIX_N_ARY_OP_REF(sub),
	YIX_N_ARY_OP_REF(mul),
    {NULL}  /* Sentinel */
};


static PyMemberDef YicesInternalExpression_members[] = {
    {"varid", T_INT, offsetof(YicesInternalExpression, varid), 0, "Variable id but or -1 for non-variable expressions"},
    {NULL}  /* Sentinel */
};

static PyTypeObject yicesfull_YicesInternalExpressionType = {
    PyObject_HEAD_INIT(NULL)
    0,                                         /*ob_size*/
    "yicesfull.YicesInternalExpression",       /*tp_name*/
    sizeof(YicesInternalExpression),           /*tp_basicsize*/
    0,                                         /*tp_itemsize*/
    0,                                         /*tp_dealloc*/
    0,                                         /*tp_print*/
    0,                                         /*tp_getattr*/
    0,                                         /*tp_setattr*/
    0,                                         /*tp_compare*/
    0,                                         /*tp_repr*/
    0,                                         /*tp_as_number*/
    0,                                         /*tp_as_sequence*/
    0,                                         /*tp_as_mapping*/
    0,                                         /*tp_hash */
    0,                                         /*tp_call*/
    (reprfunc)YIX_str,                         /*tp_str*/
    0,                                         /*tp_getattro*/
    0,                                         /*tp_setattro*/
    0,                                         /*tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,                        /*tp_flags*/
    "Represents a internal yices expression",  /* tp_doc */
    0,                                         /* tp_traverse */
    0,                                         /* tp_clear */
    0,                                         /* tp_richcompare */
    0,                                         /* tp_weaklistoffset */
    0,                                         /* tp_iter */
    0,                                         /* tp_iternext */
    YicesInternalExpression_methods,           /* tp_methods */
    YicesInternalExpression_members,           /* tp_members */
    0,                                         /* tp_getset */
    0,                                         /* tp_base */
    0,                                         /* tp_dict */
    0,                                         /* tp_descr_get */
    0,                                         /* tp_descr_set */
    0,                                         /* tp_dictoffset */
    0,                                         /* tp_init */
    0,                                         /* tp_alloc */
    0,                                         /* tp_new */
};

/*******************************************************************************
********************************* YicesContext *********************************
*******************************************************************************/

typedef struct {
    PyObject_HEAD
    yices_context context;
    unsigned int pushes;
    int varcount;
    ytype_t* variable_types;
    yices_expr* variable_expressions;
    unsigned int varlist_size;
    yices_type booltype;
    yices_type realtype;
    yices_type nattype;
    yices_type inttype;
} YicesContext;

static int YicesContext_init(YicesContext *self, PyObject *args, PyObject *kwds)
{
	_TIME_Y(self->context = yices_mk_context();)
	self->pushes = 0;
	self->varcount = 0;
	self->realtype = yices_mk_type(self->context, "real");
	self->booltype = yices_mk_type(self->context, "bool");
	self->nattype  = yices_mk_type(self->context, "nat");
	self->inttype  = yices_mk_type(self->context, "int");
	
	self->variable_types       = malloc(sizeof(ytype_t)          * VAR_LIST_BLOCK_SIZE);
	self->variable_expressions = malloc(sizeof(yices_expr) * VAR_LIST_BLOCK_SIZE);
	self->varlist_size         = VAR_LIST_BLOCK_SIZE;
	
    return 0;
}

static int YicesContext_dealloc(YicesContext *self)
{
	_TIME_Y(yices_del_context(self->context);)
	free(self->variable_types);
	free(self->variable_expressions);
	return 0;
}

static PyObject* yc_helper_mk_var(YicesContext* self, PyObject* args, yices_type type, ytype_t type_id)
{
	if(self->pushes != 0)
	{
        PyErr_SetString(YicesFullException, "Can only make variables at push level 0.");
        return NULL;
    }
	int new_id = self->varcount;
	char* name = NULL;
	if(!PyArg_ParseTuple(args, "s", &name))
	{
		return NULL;
	}
	
	//Build expression
	_TIME_Y(yices_expr yo = yices_mk_var_from_decl(self->context, yices_mk_var_decl(self->context, name, type)))
	PyObject* ret = (PyObject*) new_yix(self->context, yo);
	
	//ID
	((YicesInternalExpression*) ret)->varid = new_id;
	self->varcount++;
	
	//Bookkeeping
	if(new_id >= self->varlist_size)
	{ //Increase size
		ytype_t* old_types          = self->variable_types;
		yices_expr* old_exprs = self->variable_expressions;
		self->variable_types        = malloc(sizeof(ytype_t)                   * (self->varlist_size + VAR_LIST_BLOCK_SIZE));
		self->variable_expressions  = malloc(sizeof(yices_expr)          * (self->varlist_size + VAR_LIST_BLOCK_SIZE));
		memcpy(self->variable_types,       old_types, sizeof(ytype_t)          * self->varlist_size);
		memcpy(self->variable_expressions, old_exprs, sizeof(yices_expr) * self->varlist_size);
		free(old_types);
		free(old_exprs);
		
		self->varlist_size          += VAR_LIST_BLOCK_SIZE;
	}
	self->variable_types[new_id]        = type_id;
	self->variable_expressions[new_id] = ((YicesInternalExpression*) ret)->expression;
	
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_mk_bool(YicesContext* self, PyObject* args)
{
	PyObject* ret = yc_helper_mk_var(self, args, self->booltype, TYPE_BOOL);
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_mk_real(YicesContext* self, PyObject* args)
{
	PyObject* ret = yc_helper_mk_var(self, args, self->realtype, TYPE_REAL);
	_DBG_RET_OBJ(ret)
	return ret; 
}

static PyObject* YicesContext_mk_nat(YicesContext* self, PyObject* args)
{
	PyObject* ret = yc_helper_mk_var(self, args, self->nattype, TYPE_INT);
	_DBG_RET_OBJ(ret)
	return ret;
}


static PyObject* YicesContext_mk_int(YicesContext* self, PyObject* args)
{
	PyObject* ret = yc_helper_mk_var(self, args, self->inttype, TYPE_INT);
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_mk_true(YicesContext* self)
{
	PyObject* ret = (PyObject*) new_yix(self->context, yices_mk_true(self->context)); //considered neglectible
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_mk_false(YicesContext* self)
{
	PyObject* ret = (PyObject*) new_yix(self->context, yices_mk_false(self->context)); //considered neglectible
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_mk_num(YicesContext* self, PyObject* args)
{
	long num;
	if (!PyArg_ParseTuple(args, "l", &num))
		return NULL;
	
	PyObject* ret = (PyObject*) new_yix(self->context, yices_mk_num (self->context, num)); //considered neglectible
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_assertion(YicesContext* self, PyObject* args)
{
	YicesInternalExpression* expr;
	
	if (!PyArg_ParseTuple(args, "O!", &yicesfull_YicesInternalExpressionType, (PyObject**) &expr))
		return NULL;
	
	if (expr->context != self->context) {
        PyErr_SetString(YicesFullException, "Expression from different context");
        return NULL;
	}
	
	_TIME_Y(yices_assert(self->context, expr->expression);)
	
	Py_RETURN_NONE;
}


static PyObject* YicesContext_retractable_assertion(YicesContext* self, PyObject* args)
{
	YicesInternalExpression* expr;
	
	if (!PyArg_ParseTuple(args, "O!", &yicesfull_YicesInternalExpressionType, (PyObject**) &expr))
		return NULL;
	
	if (expr->context != self->context) {
        PyErr_SetString(YicesFullException, "Expression from different context");
        return NULL;
	}
	
	_TIME_Y(assertion_id id = yices_assert_retractable(self->context, expr->expression);)
	
	RetractableAssertion* ret = new_ra(self->context, id);
	
	_DBG_RET_OBJ(ret)
	return (PyObject*) ret;
}

static PyObject* YicesContext_check(YicesContext* self)
{
	_TIME_Y(lbool lb = yices_check(self->context))
	PyObject* ret = ybool2pybool(lb);
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_unsat_core(YicesContext* self)
{
	//get unsat core
	_TIME_Y(unsigned sz = yices_get_unsat_core_size(self->context);)
	assertion_id* ids = malloc(sz * sizeof(assertion_id));
	_TIME_Y(yices_get_unsat_core(self->context, ids))
	
	//build return list
	PyObject* list = PyList_New(sz);
	if(list == NULL)
	{
		free(ids);
		return NULL;
	}
	
	PyObject* ni;
	Py_ssize_t i;
	for(i = 0; i < sz; i++)
	{
		ni = (PyObject*) new_ra(self->context, ids[i]);
		if(ni == NULL)
		{
			Py_DECREF(list);
			free(ids);
			return NULL;
		}
		if(PyList_SET_ITEM(list, i, ni) < 0)
		{
			Py_DECREF(list);
			Py_DECREF(ni);
			free(ids);
			return NULL;
		}
	}
	
	free(ids);
	_DBG_RET_OBJ(list)
	return list;
}

static PyObject* YicesContext_get_context(YicesContext* self)
{
	PyObject* ret = Py_BuildValue("i", self->context);
	_DBG_RET_OBJ(ret)
	return ret;
}

static PyObject* YicesContext_str(YicesContext* self)
{
	PyObject* ret = PyString_FromFormat("Yices context %p", self->context);
	_DBG_RET_OBJ(ret)
    return ret;
}

static PyObject* YicesContext_is_inconsistent(YicesContext* self)
{
	if(yices_inconsistent(self->context))
		Py_RETURN_TRUE;
	else
		Py_RETURN_FALSE;
}

static PyObject* YicesContext_get_model(YicesContext* self)
{
	//Obtain model
	_TIME_Y(yices_model model = yices_get_model(self->context);)
	if(model == 0)
	{
		Py_RETURN_NONE;
	}
	
	//Iterate over variables
	PyObject* ret = PyList_New(self->varcount);
	if(ret == NULL)
		return NULL;
	
	PyObject *val, *cls, *arg;
	int i, rval;
	yices_var_decl decl;
	long num, den;
	ytype_t type;
	for(i = 0; i < self->varcount; i++)
	{
		decl = yices_get_var_decl(self->variable_expressions[i]);
		
		//Get value and transform to python value
		rval = 1;
		val = NULL;
		type = self->variable_types[i];
		if(type == TYPE_BOOL)
		{
			val = ybool2pybool(yices_get_value(model, decl));
		}
		else if (type == TYPE_INT || type == TYPE_REAL)
		{
			rval = yices_get_arith_value(model, decl, &num, &den);
			if(den == -1)
			{
				num = -num;
				den = 1;
			}
			
			if(den == 1)
			{ // Make int / long
				val = Py_BuildValue("l", num);
				if(val == NULL)
					return NULL;
			}
			else
			{ // Make fractions.Fraction
				cls = PyObject_GetAttrString(mod_fractions, "Fraction");
				if(cls == NULL)
				{
					Py_DECREF(ret);
					return NULL;
				}
			
				arg = Py_BuildValue("ll", num, den);
				if(arg == NULL)
				{
					Py_DECREF(cls);
					Py_DECREF(ret);
					return NULL;
				}
			
				val = PyObject_Call(cls, arg, NULL);
				Py_DECREF(arg);
				Py_DECREF(cls);
				if(val == NULL)
				{
					Py_DECREF(ret);
					return NULL;
				}
			}
		}
		else
		{
		    PyErr_Format(YicesFullException, "Invalid variable type id: %i", self->variable_types[i]);
			Py_DECREF(ret);
			return NULL;
		}
			
		if(!rval || val == NULL) /* NOTE: !rval can mean (a) that the variable is
									not used anywhere or (b) denominator or numerator
									is too big to convert to long; To be safe we
									throw an exception even in (a) */
		{
		    PyErr_Format(YicesFullException, "Getting value failed for variable %d", i);
			Py_DECREF(ret);
			return NULL;
		}
				
		//Put into list
		PyList_SET_ITEM(ret, i, val);
	}
	
	_DBG_RET_OBJ(ret)
	return ret;
}
////////////////////////////////////////////////////////////////////////////////
static PyObject* YicesContext_push(YicesContext* self) /////////////////////////
{
	//Actual push
	_TIME_Y(yices_push(self->context);)
	self->pushes++;
	
	Py_RETURN_NONE;
}

////////////////////////////////////////////////////////////////////////////////
static PyObject* YicesContext_pop(YicesContext* self) //////////////////////////
{
	if(self->pushes > 0)
	{
		//Actual pop
		_TIME_Y(yices_pop(self->context);)
		self->pushes--;
				
		Py_RETURN_NONE;
	}
	else
	{
        PyErr_SetString(YicesFullException, "More pops than pushes");
		return NULL;
	}
}


static PyMethodDef YicesContext_methods[] = {
    {"assertion",             (PyCFunction) YicesContext_assertion,             METH_VARARGS, "Adds an assertion. Takes an Expression"},
    {"retractable_assertion", (PyCFunction) YicesContext_retractable_assertion, METH_VARARGS, "Adds a rectractable assertion. Takes an Expression. Returns a RetractableAssertion object"},
    {"unsat_core",            (PyCFunction) YicesContext_unsat_core,            METH_NOARGS,  "Returns a list containing the retractable assertions that are part of the unsatisfiable core."},
    {"check",                 (PyCFunction) YicesContext_check,                 METH_NOARGS,  "Checks the current assertions. Returns True, False or None for SAT, UNSAT and undecidable"},
    {"mk_bool",               (PyCFunction) YicesContext_mk_bool,               METH_VARARGS, "Makes a new boolean variable with the specified name. Note that no two variables should have the same name."},
    {"mk_real",               (PyCFunction) YicesContext_mk_real,               METH_VARARGS, "Makes a new real variable with the specified name. Note that no two variables should have the same name."},
    {"mk_nat",                (PyCFunction) YicesContext_mk_nat,                METH_VARARGS, "Makes a new natural value variable with the specified name. Note that no two variables should have the same name. Don't use in arithmetic only mode."},
    {"mk_int",                (PyCFunction) YicesContext_mk_int,                METH_VARARGS, "Makes a new integer value variable with the specified name. Note that no two variables should have the same name."},
    {"mk_false",              (PyCFunction) YicesContext_mk_false,              METH_NOARGS,  "Makes the constant \"false\""},
    {"mk_true",               (PyCFunction) YicesContext_mk_true,               METH_NOARGS,  "Makes the constant \"true\""},
    {"mk_num",                (PyCFunction) YicesContext_mk_num,                METH_VARARGS, "Makes an integer constant"},
    {"get_context",           (PyCFunction) YicesContext_get_context,           METH_NOARGS,  "Returns an integer representation of the context"},
    {"get_model",             (PyCFunction) YicesContext_get_model,             METH_NOARGS,  "Returns name -> value dictionary (both strings) if there currently is a model or None otherwise"},
    {"is_inconsistent",       (PyCFunction) YicesContext_is_inconsistent,       METH_NOARGS,  "Returns True if the context is inconsistent"},
    {"push",                  (PyCFunction) YicesContext_push,                  METH_NOARGS,  "Create a backtracking point"},
    {"pop",                   (PyCFunction) YicesContext_pop,                   METH_NOARGS,  "Backtracks"},
    {NULL}  /* Sentinel */
};

static PyMemberDef YicesContext_members[] = {
    {"varcount", T_INT,  offsetof(YicesContext, varcount), 0, "Number of variables"},
    {"pushes",   T_UINT, offsetof(YicesContext, pushes), 0, "Number of pushes minus number of pops"},
    {NULL}  /* Sentinel */
};

static PyTypeObject yicesfull_YicesContextType = {
    PyObject_HEAD_INIT(NULL)
    0,                                /*ob_size*/
    "yicesfull.YicesContext",         /*tp_name*/
    sizeof(YicesContext),             /*tp_basicsize*/
    0,                                /*tp_itemsize*/
    (destructor)YicesContext_dealloc, /*tp_dealloc*/
    0,                                /*tp_print*/
    0,                                /*tp_getattr*/
    0,                                /*tp_setattr*/
    0,                                /*tp_compare*/
    0,                                /*tp_repr*/
    0,                                /*tp_as_number*/
    0,                                /*tp_as_sequence*/
    0,                                /*tp_as_mapping*/
    0,                                /*tp_hash */ //    (hashfunc)YicesContext_hash,      /*tp_hash */
    0,                                /*tp_call*/
    (reprfunc)YicesContext_str,       /*tp_str*/
    0,                                /*tp_getattro*/
    0,                                /*tp_setattro*/
    0,                                /*tp_as_buffer*/
    Py_TPFLAGS_DEFAULT,               /*tp_flags*/
    "Yices C API object",             /* tp_doc */
    0,                                /* tp_traverse */
    0,                                /* tp_clear */
    0,                                /* tp_richcompare */
    0,                                /* tp_weaklistoffset */
    0,                                /* tp_iter */
    0,                                /* tp_iternext */
    YicesContext_methods,             /* tp_methods */
    YicesContext_members,             /* tp_members */
    0,                                /* tp_getset */
    0,                                /* tp_base */
    0,                                /* tp_dict */
    0,                                /* tp_descr_get */
    0,                                /* tp_descr_set */
    0,                                /* tp_dictoffset */
    (initproc)YicesContext_init,      /* tp_init */
    0,                                /* tp_alloc */
    0,                                /* tp_new */
};


/*******************************************************************************
****************************** Module level stuff ******************************
*******************************************************************************/

static PyObject* set_verbosity(PyObject *self, PyObject *args) {
	int val;
	if (!PyArg_ParseTuple(args, "i", &val))
		return NULL;
	
	yices_set_verbosity(val);
	
	Py_RETURN_NONE;
}


static PyObject* version(PyObject *self)
{
	PyObject* ret = Py_BuildValue("s", yices_version());
	_DBG_RET_OBJ(ret)
    return ret;
}

static PyObject* enable_type_checker(PyObject *self, PyObject *args)
{
	int val;
	if (!PyArg_ParseTuple(args, "i", &val))
		return NULL;
	
	yices_enable_type_checker(val);
	
	Py_RETURN_NONE;
}


static PyObject* set_arith_only(PyObject *self, PyObject *args)
{
	int val;
	if (!PyArg_ParseTuple(args, "i", &val))
		return NULL;
	
	yices_set_arith_only(val);

	Py_RETURN_NONE;
}


static PyObject* enable_log_file(PyObject *self, PyObject *args)
{
	char* fn;
	if (!PyArg_ParseTuple(args, "s", &fn))
		return NULL;
	
	yices_enable_log_file(fn);
	
	Py_RETURN_NONE;
}

static PyObject* duration(PyObject *self)
{
	PyObject* ret = Py_BuildValue("d", (double) yices_time / (double) CLOCKS_PER_SEC);
	_DBG_RET_OBJ(ret)
    return ret;
}

static PyObject* seed(PyObject *self, PyObject *args)
{
	unsigned long val;
	if (!PyArg_ParseTuple(args, "k", &val))
		return NULL;
	
	srand((unsigned int) val);
	
	Py_RETURN_NONE;
}

static PyObject* enable_time_measuring(PyObject *self, PyObject* args)
{
	if (!PyArg_ParseTuple(args, "i", &time_y))
		return NULL;	
	Py_RETURN_NONE;
}

static PyMethodDef yicesfull_methods[] = {
    {"get_version",            (PyCFunction) version,                METH_NOARGS,  "Returns the version of yices that is used."},
    {"set_verbosity",          (PyCFunction) set_verbosity,          METH_VARARGS, "Sets the verbosity -- note that this affects any YicesContext instance!"},
    {"enable_type_checker",    (PyCFunction) enable_type_checker,    METH_VARARGS, "En/disables type checker -- note that this affects any YicesContext instance!"},
    {"_enable_log_file",       (PyCFunction) enable_log_file,        METH_VARARGS, "For debugging"},
    {"set_arith_only",         (PyCFunction) set_arith_only,         METH_VARARGS, "Dis/Enables arithmetic only mode. Enabling does not work with nat variables (but with int)"},
    {"enable_time_measuring",  (PyCFunction) enable_time_measuring,  METH_VARARGS, "Enables time measuring for yices"},
    {"duration",               (PyCFunction) duration,               METH_NOARGS,  "Returns the total time used by all yices instances (in seconds) so far."},
    {"seed",                   (PyCFunction) seed,                   METH_VARARGS, "Sets the seed."},
    {NULL, NULL, 0, NULL}        /* Sentinel */
};

PyMODINIT_FUNC inityicesfull(void)
{
    PyObject* m;
    
	yicesfull_YicesContextType.tp_new = PyType_GenericNew;
    if (PyType_Ready(&yicesfull_YicesContextType) < 0)
        return;
    
    yicesfull_YicesInternalExpressionType.tp_new = PyType_GenericNew;
    if (PyType_Ready(&yicesfull_YicesInternalExpressionType) < 0)
        return;
    
	yicesfull_RetractableAssertionType.tp_new = PyType_GenericNew;
    if (PyType_Ready(&yicesfull_RetractableAssertionType) < 0)
        return;

    m = Py_InitModule3("yicesfull", yicesfull_methods, "Module for using the Yices C API");

    if (m == NULL)
      return;
	
    Py_INCREF(&yicesfull_YicesContextType);
    PyModule_AddObject(m, "YicesContext", (PyObject *)& yicesfull_YicesContextType);
    
    Py_INCREF(&yicesfull_YicesInternalExpressionType);
    PyModule_AddObject(m, "YicesInternalExpression", (PyObject *)& yicesfull_YicesInternalExpressionType);
    
    Py_INCREF(&yicesfull_RetractableAssertionType);
    PyModule_AddObject(m, "RetractableAssertion", (PyObject *)& yicesfull_RetractableAssertionType);
	
	//YicesFullException
    YicesFullException = PyErr_NewException("yicesfull.YicesFullException", NULL, NULL);
    Py_INCREF(YicesFullException);
    PyModule_AddObject(m, "YicesFullException", YicesFullException);
	
//	mod_self = m;
	mod_builtin = PyImport_ImportModule("__builtin__");
	mod_fractions = PyImport_ImportModule("fractions");
	mod_self = PyImport_ImportModule("yicesfull");
}

