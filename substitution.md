This module is needed because the Haskell backend does not support `SUBSTITUTION`

```k
module BOOGIE-SUBSTITUTION
    imports BOOGIE-RULE-SYNTAX
    imports ID
```

```k
    syntax Expr ::= substitute(Expr, vars: IdList, for: ExprList) [function, functional]
    rule substitute(Expr, Vars, For) => substitute(Expr, Vars, For, 0)
```

```k
    syntax Expr ::= substitute(Expr, vars: IdList, for: ExprList, fresh: Int) [function, functional]
    rule substitute(E, .IdList, .ExprList, Fresh) => E
    rule substitute(E, (Var, Vars), (For, Fors), Fresh)
      => substituteSingle( substitute( substituteSingle(E, Var, freshId(Fresh))
                                     , Vars
                                     , Fors
                                     , Fresh +Int 1
                                     )
                         , freshId(Fresh)
                         , For
                         )
```

```k
    syntax Expr ::= substituteSingle(Expr, Id, Expr) [function, functional]
    rule substituteSingle(X:Id,   X  , For) => For
    rule substituteSingle(X:Id,   Var, For) => X     requires X =/=K Var
    rule substituteSingle(B:Bool, Var, For) => B
    rule substituteSingle(I:Int,  Var, For) => I
    rule substituteSingle(old(E), Var, For) => old(substituteSingle(E, Var, For))

    // MapOp
    rule substituteSingle(E [ Keys ] , Var, For) => substituteSingle(E  , Var, For) [ substituteSingle(E, Var, For) ]
    rule substituteSingle(E [ Keys := Val ] , Var, For)
      => substituteSingle(E  , Var, For) [ substituteSingle(Keys, Var, For) := substituteSingle(Val, Var, For) ]

    rule substituteSingle(Op:UnOp E, Var, For) => Op substituteSingle(E, Var, For)
    rule substituteSingle( E1 Op:MulOp   E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:AddOp   E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:RelOp   E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:OrOp    E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:AndOp   E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:ImplOp  E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
    rule substituteSingle( E1 Op:EquivOp E2, Var, For ) => substituteSingle(E1, Var, For) Op substituteSingle(E2, Var, For)
```

```k
    syntax ExprList ::= substituteSingle(ExprList, Id, Expr) [function, functional]
    rule substituteSingle(.ExprList, Vars, Fors) => .ExprList
    rule substituteSingle((Expr, Exprs), Vars, Fors)
      => substituteSingle(Expr, Vars, Fors), substituteSingle(Exprs, Vars, Fors)
```

```k
endmodule
```
