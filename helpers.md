Helpers
-------

```k
module BOOGIE-HELPERS
    imports BOOGIE-RULE-SYNTAX
    imports syntax DEFAULT-CONFIGURATION
    imports BOOL
    imports INT
```

```k
    syntax LocalVarDeclList ::= makeDecls(IdsTypeWhereList) [function]
    rule makeDecls(.IdsTypeWhereList) => .LocalVarDeclList
    rule makeDecls(X : Type, Ids)
      => var .AttributeList X : Type ; makeDecls(Ids)
```

```k
    syntax StmtList ::= StmtList "++StmtList" StmtList [function, left, avoid]
    rule (S1 S1s) ++StmtList S2s => S1 (S1s ++StmtList S2s)
    rule .StmtList ++StmtList S2s => S2s
```

```k
    syntax LocalVarDeclList ::= LocalVarDeclList "++LocalVarDeclList" LocalVarDeclList [function, left, avoid]
    rule (S1 S1s) ++LocalVarDeclList S2s => S1 (S1s ++LocalVarDeclList S2s)
    rule .LocalVarDeclList ++LocalVarDeclList S2s => S2s
```

```k
    syntax ExprList ::= ExprList "++ExprList" ExprList [function, left, avoid]
    rule (X1, X1s) ++ExprList X2s => X1, (X1s ++ExprList X2s)
    rule .ExprList ++ExprList X2s => X2s
```

```k
    syntax IdList ::= IdList "++IdList" IdList [function, left, avoid]
    rule (X1, X1s) ++IdList X2s => X1, (X1s ++IdList X2s)
    rule .IdList ++IdList X2s => X2s
```

```k
    syntax Bool ::= Id "in" IdList [function]
    rule X in .IdList => false
    rule X in (X, Ys) => true
    rule X in (Y, Ys) => X in Ys requires Y =/=K X
```

```k
    syntax ExprList ::= IdListToExprList(IdList) [function]
    rule IdListToExprList(.IdList) => .ExprList
    rule IdListToExprList(X, Xs) => X, IdListToExprList(Xs)
```

```k
    syntax IdList ::= IdsTypeWhereListToIdList(IdsTypeWhereList) [function]
    rule IdsTypeWhereListToIdList(.IdsTypeWhereList) => .IdList
    rule IdsTypeWhereListToIdList(Xs : T            , Rest) => Xs ++IdList IdsTypeWhereListToIdList(Rest)
    rule IdsTypeWhereListToIdList((Xs : T where Exp), Rest) => Xs ++IdList IdsTypeWhereListToIdList(Rest)
```

```k
    syntax ExprList ::= IdsTypeWhereListToExprList(IdsTypeWhereList) [function]
    rule IdsTypeWhereListToExprList(.IdsTypeWhereList) => .ExprList
    rule IdsTypeWhereListToExprList(Xs : T            , Rest) => Xs ++ExprList IdsTypeWhereListToExprList(Rest)
    rule IdsTypeWhereListToExprList((Xs : T where Exp), Rest) => Xs ++ExprList IdsTypeWhereListToExprList(Rest)
```

```k
    syntax IdList ::= LocalVarDeclListToIdList(LocalVarDeclList) [function]
    rule LocalVarDeclListToIdList(.LocalVarDeclList) => .IdList
    rule LocalVarDeclListToIdList(var _:AttributeList Vs; Rest) => IdsTypeWhereListToIdList(Vs) ++IdList LocalVarDeclListToIdList(Rest)
```

```k
endmodule
```
