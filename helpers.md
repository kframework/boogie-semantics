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
    syntax StmtList ::= makeAssignments(IdList, ExprList) [function]
    rule makeAssignments(.IdList, .ExprList) => .StmtList
    rule makeAssignments((X , Xs), (V, Vs))
      => X := V, .ExprList ; makeAssignments(Xs, Vs)
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
    syntax IdsTypeList ::= IdsTypeList "++IdsTypeList" IdsTypeList [function, left, avoid]
    rule (X1, X1s) ++IdsTypeList X2s => X1, (X1s ++IdsTypeList X2s)
    rule .IdsTypeList ++IdsTypeList X2s => X2s
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
    syntax IdList ::= IdsTypeListToIdList(IdsTypeList) [function]
    rule IdsTypeListToIdList(.IdsTypeList) => .IdList
    rule IdsTypeListToIdList(Xs : T, Rest) => Xs, IdsTypeListToIdList(Rest)
```

```k
    syntax IdList ::= IdsTypeWhereListToIdList(IdsTypeWhereList) [function]
    rule IdsTypeWhereListToIdList(.IdsTypeWhereList) => .IdList
    rule IdsTypeWhereListToIdList(Xs : T            , Rest) => Xs, IdsTypeWhereListToIdList(Rest)
    rule IdsTypeWhereListToIdList((Xs : T where Exp), Rest) => Xs, IdsTypeWhereListToIdList(Rest)
```

```k
    syntax IdsTypeWhereList ::= IdsTypeListToIdsTypeWhereList(IdsTypeList) [function]
    rule IdsTypeListToIdsTypeWhereList(.IdsTypeList) => .IdsTypeWhereList
    rule IdsTypeListToIdsTypeWhereList(Xs : T            , Rest) => Xs : T, IdsTypeListToIdsTypeWhereList(Rest)
```

```k
    syntax ExprList ::= IdsTypeWhereListToExprList(IdsTypeWhereList) [function]
    rule IdsTypeWhereListToExprList(.IdsTypeWhereList) => .ExprList
    rule IdsTypeWhereListToExprList(Xs : T            , Rest) => Xs ++ExprList IdsTypeWhereListToExprList(Rest)
    rule IdsTypeWhereListToExprList((Xs : T where Exp), Rest) => Xs ++ExprList IdsTypeWhereListToExprList(Rest)
```

```k
    syntax IdsTypeList ::= IdsTypeWhereListToIdsTypeList(IdsTypeWhereList) [function]
    rule IdsTypeWhereListToIdsTypeList(.IdsTypeWhereList) => .IdsTypeList
    rule IdsTypeWhereListToIdsTypeList(Xs : T            , Rest) => Xs : T ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rest)
    rule IdsTypeWhereListToIdsTypeList((Xs : T where Exp), Rest) => Xs : T ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rest)
```

```k
    syntax IdList ::= LocalVarDeclListToIdList(LocalVarDeclList) [function]
    rule LocalVarDeclListToIdList(.LocalVarDeclList) => .IdList
    rule LocalVarDeclListToIdList(var _:AttributeList Vs; Rest) => IdsTypeWhereListToIdList(Vs) ++IdList LocalVarDeclListToIdList(Rest)
```

```k
    syntax LhsList ::= LhsList "++LhsList" LhsList [function, left, avoid]
    rule (X1, X1s) ++LhsList X2s => X1, (X1s ++LhsList X2s)
    rule .LhsList ++LhsList X2s => X2s
```

```k
    syntax LhsList ::= IdListToLhsList(IdList) [function]
    rule IdListToLhsList(.IdList) => .LhsList
    rule IdListToLhsList(X, Rest) => X ++LhsList IdListToLhsList(Rest)
```

```k
endmodule
```
