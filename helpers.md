Nothing
-------

Quite a few Boogie contructs have, often multiple, "optional" parts. The
`Nothing` modules below make using the empty token in these productions easier,
with a different syntax for parsing programs and for parsing rules.

```k
module NOTHING-COMMON-SYNTAX
    syntax Nothing
endmodule

module NOTHING-PROGRAM-SYNTAX
    imports NOTHING-COMMON-SYNTAX
    syntax Nothing ::= "" [klabel(Nothing), symbol]
endmodule

module NOTHING-RULE-SYNTAX
    imports NOTHING-COMMON-SYNTAX
    syntax Nothing ::= ".Nothing" [klabel(Nothing), symbol]
endmodule
```

Other Helpers
-------------

```k
module BOOGIE-HELPERS
    imports BOOGIE-RULE-SYNTAX
    imports BOOL
    imports INT
    imports K-EQUAL
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
    // Not defined when lists are of different lengths.
```

```k
    syntax StmtList ::= StmtList "++StmtList" StmtList [function, total, left, avoid]
    rule (S1 S1s) ++StmtList S2s => S1 (S1s ++StmtList S2s)
    rule .StmtList ++StmtList S2s => S2s
```

```k
    syntax LocalVarDeclList ::= LocalVarDeclList "++LocalVarDeclList" LocalVarDeclList [function, total, left, avoid]
    rule (S1 S1s) ++LocalVarDeclList S2s => S1 (S1s ++LocalVarDeclList S2s)
    rule .LocalVarDeclList ++LocalVarDeclList S2s => S2s
```

```k
    syntax DeclList ::= DeclList "++DeclList" DeclList [function, total, left, avoid]
    rule (S1 S1s) ++DeclList S2s => S1 (S1s ++DeclList S2s)
    rule .DeclList ++DeclList S2s => S2s
```

```k
    syntax ExprList ::= ExprList "++ExprList" ExprList [function, total, left, avoid]
    rule (X1, X1s) ++ExprList X2s => X1, (X1s ++ExprList X2s)
    rule .ExprList ++ExprList X2s => X2s
```

```k
    syntax IdList ::= IdList "++IdList" IdList [function, total, left, avoid]
    rule (X1, X1s) ++IdList X2s => X1, (X1s ++IdList X2s)
    rule .IdList ++IdList X2s => X2s
```

```k
    syntax IdsTypeList ::= IdsTypeList "++IdsTypeList" IdsTypeList [function, total, left, avoid]
    rule (X1, X1s) ++IdsTypeList X2s => X1, (X1s ++IdsTypeList X2s)
    rule .IdsTypeList ++IdsTypeList X2s => X2s
```

```k
    syntax Bool ::= Id "in" IdList [function, total]
    rule _ in .IdList => false
    rule X in (X,_Ys) => true
    rule X in (Y, Ys) => X in Ys requires Y =/=K X
```

```k
    syntax ExprList ::= IdListToExprList(IdList) [function, total]
    rule IdListToExprList(.IdList) => .ExprList
    rule IdListToExprList(X, Xs) => X, IdListToExprList(Xs)
```

```k
    syntax LhsList ::= IdListToLhsList(IdList) [function, total]
    rule IdListToLhsList(.IdList) => .LhsList
    rule IdListToLhsList(X, Xs) => X, IdListToLhsList(Xs)
```

```k
    syntax IdList ::= IdsTypeListToIdList(IdsTypeList) [function, total]
    rule IdsTypeListToIdList(.IdsTypeList) => .IdList
    rule IdsTypeListToIdList(Xs : _, Rest) => Xs ++IdList  IdsTypeListToIdList(Rest)
```

```k
    syntax TypeList ::= IdsTypeListToTypeList(IdsTypeList) [function, total]
    rule IdsTypeListToTypeList(.IdsTypeList) => .TypeList
    rule IdsTypeListToTypeList((_, Xs) : T, Rest) => T, IdsTypeListToTypeList(Xs : T, Rest)
    rule IdsTypeListToTypeList(.IdList : _, Rest) => IdsTypeListToTypeList(Rest)
```

```k
    syntax IdList ::= IdsTypeWhereListToIdList(IdsTypeWhereList) [function, total]
    rule IdsTypeWhereListToIdList(.IdsTypeWhereList) => .IdList
    rule IdsTypeWhereListToIdList(Xs:IdList  : _         , Rest) => Xs ++IdList IdsTypeWhereListToIdList(Rest)
    rule IdsTypeWhereListToIdList((Xs:IdList : _ where _), Rest) => Xs ++IdList IdsTypeWhereListToIdList(Rest)
```

```k
    syntax IdsTypeWhereList ::= IdsTypeListToIdsTypeWhereList(IdsTypeList) [function, total]
    rule IdsTypeListToIdsTypeWhereList(.IdsTypeList) => .IdsTypeWhereList
    rule IdsTypeListToIdsTypeWhereList(Xs : T , Rest) => Xs : T, IdsTypeListToIdsTypeWhereList(Rest)
```

```k
    syntax ExprList ::= IdsTypeWhereListToExprList(IdsTypeWhereList) [function, total]
    rule IdsTypeWhereListToExprList(.IdsTypeWhereList) => .ExprList
    rule IdsTypeWhereListToExprList(Xs : _          , Rest) => IdListToExprList(Xs) ++ExprList IdsTypeWhereListToExprList(Rest)
    rule IdsTypeWhereListToExprList((Xs : _ where _), Rest) => IdListToExprList(Xs) ++ExprList IdsTypeWhereListToExprList(Rest)
```

```k
    syntax IdsTypeList ::= IdsTypeWhereListToIdsTypeList(IdsTypeWhereList) [function, total]
    rule IdsTypeWhereListToIdsTypeList(.IdsTypeWhereList) => .IdsTypeList
    rule IdsTypeWhereListToIdsTypeList(Xs : T          , Rest) => Xs : T ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rest)
    rule IdsTypeWhereListToIdsTypeList((Xs : T where _), Rest) => Xs : T ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rest)
```

```k
    syntax IdList ::= LocalVarDeclListToIdList(LocalVarDeclList) [function, total]
    rule LocalVarDeclListToIdList(.LocalVarDeclList) => .IdList
    rule LocalVarDeclListToIdList(var _:AttributeList Vs; Rest) => IdsTypeWhereListToIdList(Vs) ++IdList LocalVarDeclListToIdList(Rest)
```

```k
    syntax LhsList ::= LhsList "++LhsList" LhsList [function, total, left, avoid]
    rule (X1, X1s) ++LhsList X2s => X1, (X1s ++LhsList X2s)
    rule .LhsList ++LhsList X2s => X2s
```

```k
    syntax LhsList ::= IdListToLhsList(IdList) [function, total]
    rule IdListToLhsList(.IdList) => .LhsList
    rule IdListToLhsList(X, Rest) => X ++LhsList IdListToLhsList(Rest)
```

```k
    syntax LocationExprList ::= List{LocationExpr, ","} [klabel(LocationExprList)]
    syntax Location ::= "{" String "," Int "," Int "}"
    syntax LocationExpr ::= Location Expr

    syntax LocationExprList ::= LocationExprList "++LocationExprList" LocationExprList [function, total, left, avoid]
    rule (E1, E1s) ++LocationExprList E2s => E1, (E1s ++LocationExprList E2s)
    rule .LocationExprList ++LocationExprList E2s => E2s
```

```k
    syntax OptionalLabel ::= Nothing | Label
```

```k
    syntax Stmt ::= LoopInvariant
    syntax StmtList ::= LoopInvariantListToStmtList(LoopInvariantList) [function, total]
    rule LoopInvariantListToStmtList(.LoopInvariantList) => .StmtList
    rule LoopInvariantListToStmtList(Invariant Rest) => Invariant LoopInvariantListToStmtList(Rest)
```

```k
endmodule
```
