#!/usr/bin/env python3
"""row_polymorphism - Row-polymorphic type system (structural typing for records).

Usage: python row_polymorphism.py [--demo]
"""

# Types
class TInt:
    def __repr__(self): return "Int"
class TBool:
    def __repr__(self): return "Bool"
class TStr:
    def __repr__(self): return "Str"
class TFun:
    def __init__(self, arg, ret): self.arg=arg; self.ret=ret
    def __repr__(self): return f"({self.arg} -> {self.ret})"
class TVar:
    _counter = 0
    def __init__(self, name=None):
        if name is None:
            TVar._counter += 1; name = f"t{TVar._counter}"
        self.name = name; self.bound = None
    def resolve(self):
        if self.bound: return self.bound.resolve() if isinstance(self.bound, TVar) else self.bound
        return self
    def __repr__(self): return str(self.resolve()) if self.bound else f"'{self.name}"
class TRecord:
    def __init__(self, fields, row=None):
        self.fields = dict(fields)  # name -> type
        self.row = row  # None = closed, TVar = open (row variable)
    def __repr__(self):
        fs = ", ".join(f"{k}: {v}" for k,v in sorted(self.fields.items()))
        tail = f" | {self.row}" if self.row else ""
        return "{" + fs + tail + "}"

# Unification
class UnificationError(Exception): pass

def occurs_in(tvar, ty):
    ty = ty.resolve() if isinstance(ty, TVar) else ty
    if isinstance(ty, TVar): return ty is tvar
    if isinstance(ty, TFun): return occurs_in(tvar, ty.arg) or occurs_in(tvar, ty.ret)
    if isinstance(ty, TRecord):
        return any(occurs_in(tvar, t) for t in ty.fields.values()) or \
               (ty.row and occurs_in(tvar, ty.row))
    return False

def unify(t1, t2):
    t1 = t1.resolve() if isinstance(t1, TVar) else t1
    t2 = t2.resolve() if isinstance(t2, TVar) else t2
    if isinstance(t1, TVar):
        if t1 is t2: return
        if occurs_in(t1, t2): raise UnificationError(f"Infinite type: {t1} ~ {t2}")
        t1.bound = t2; return
    if isinstance(t2, TVar):
        return unify(t2, t1)
    if type(t1) == type(t2):
        if isinstance(t1, (TInt, TBool, TStr)): return
        if isinstance(t1, TFun):
            unify(t1.arg, t2.arg); unify(t1.ret, t2.ret); return
        if isinstance(t1, TRecord):
            # Row polymorphism: unify common fields, handle row variables
            for name in t1.fields:
                if name in t2.fields:
                    unify(t1.fields[name], t2.fields[name])
                elif t2.row:
                    pass  # Field exists in open row
                else:
                    raise UnificationError(f"Field {name} not in {t2}")
            for name in t2.fields:
                if name not in t1.fields:
                    if t1.row:
                        pass
                    else:
                        raise UnificationError(f"Field {name} not in {t1}")
            if t1.row and t2.row:
                unify(t1.row, t2.row)
            return
    raise UnificationError(f"Cannot unify {t1} with {t2}")

# Type checker
class Expr:
    pass
class EInt(Expr):
    def __init__(self, v): self.v=v
class EBool(Expr):
    def __init__(self, v): self.v=v
class EStr(Expr):
    def __init__(self, v): self.v=v
class EVar(Expr):
    def __init__(self, n): self.n=n
class ELam(Expr):
    def __init__(self, p, b): self.p=p; self.b=b
class EApp(Expr):
    def __init__(self, f, a): self.f=f; self.a=a
class ERec(Expr):
    def __init__(self, fields): self.fields=fields  # [(name, expr)]
class EAccess(Expr):
    def __init__(self, rec, field): self.rec=rec; self.field=field
class EExtend(Expr):
    def __init__(self, rec, name, val): self.rec=rec; self.name=name; self.val=val

def infer(expr, env=None):
    if env is None: env = {}
    if isinstance(expr, EInt): return TInt()
    if isinstance(expr, EBool): return TBool()
    if isinstance(expr, EStr): return TStr()
    if isinstance(expr, EVar):
        if expr.n not in env: raise UnificationError(f"Unbound: {expr.n}")
        return env[expr.n]
    if isinstance(expr, ELam):
        arg_t = TVar()
        new_env = dict(env); new_env[expr.p] = arg_t
        ret_t = infer(expr.b, new_env)
        return TFun(arg_t, ret_t)
    if isinstance(expr, EApp):
        fn_t = infer(expr.f, env)
        arg_t = infer(expr.a, env)
        ret_t = TVar()
        unify(fn_t, TFun(arg_t, ret_t))
        return ret_t.resolve() if isinstance(ret_t, TVar) else ret_t
    if isinstance(expr, ERec):
        fields = {}
        for name, val_expr in expr.fields:
            fields[name] = infer(val_expr, env)
        return TRecord(fields)
    if isinstance(expr, EAccess):
        rec_t = infer(expr.rec, env)
        result_t = TVar()
        row = TVar()
        expected = TRecord({expr.field: result_t}, row)
        unify(rec_t, expected)
        return result_t.resolve() if isinstance(result_t, TVar) else result_t
    if isinstance(expr, EExtend):
        rec_t = infer(expr.rec, env)
        val_t = infer(expr.val, env)
        row = TVar()
        unify(rec_t, TRecord({}, row))
        new_fields = {}
        if isinstance(rec_t, TRecord):
            new_fields.update(rec_t.fields)
        new_fields[expr.name] = val_t
        return TRecord(new_fields, row)
    raise UnificationError(f"Unknown expr: {expr}")

def main():
    print("=== Row-Polymorphic Type System ===\n")
    tests = [
        ("42", EInt(42)),
        ("{x: 1, y: true}", ERec([("x", EInt(1)), ("y", EBool(True))])),
        ("{name: \"hi\"}.name", EAccess(ERec([("name", EStr("hi"))]), "name")),
        ("λr. r.x", ELam("r", EAccess(EVar("r"), "x"))),
        ("(λr. r.x) {x: 42, y: true}", EApp(ELam("r", EAccess(EVar("r"), "x")),
                                              ERec([("x", EInt(42)), ("y", EBool(True))]))),
    ]
    for name, expr in tests:
        try:
            t = infer(expr)
            print(f"  {name:40s} : {t}")
        except UnificationError as e:
            print(f"  {name:40s} : ERROR: {e}")

    # Row polymorphism: function works on any record with field x
    print(f"\nRow polymorphism demo:")
    get_x = ELam("r", EAccess(EVar("r"), "x"))
    t = infer(get_x)
    print(f"  λr. r.x : {t}")
    print(f"  (works on ANY record with an 'x' field)")

    # Type error
    print(f"\nType error:")
    try:
        infer(EApp(ELam("x", EAccess(EVar("x"), "missing")),
                    ERec([("other", EInt(1))])))
    except UnificationError as e:
        print(f"  {e}")

if __name__ == "__main__":
    main()
