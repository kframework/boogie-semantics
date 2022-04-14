Boogie Semantics
================

```k
requires "helpers.md"
requires "procedures.md"
requires "quantification.md"
requires "runtime.md"
requires "syntax.md"

module BOOGIE-FRESH-COUNTER
    imports INT-SYNTAX
    configuration <freshCounter> 0 </freshCounter>
endmodule

module BOOGIE-TYPES
    imports BOOGIE-RULE-SYNTAX
    configuration <types>
                    <type multiplicity="*" type="Map">
                        <typeName> #token("TypeName", "Id"):Type </typeName>
                        <synonym multiplicity="?">  #token("TypeName", "Id"):Type </synonym>
                        <uniques> .IdList </uniques>
                    </type>
                  </types>
endmodule

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-FRESH-COUNTER
    imports BOOGIE-TYPES
    imports BOOGIE-PROCEDURES
    imports BOOGIE-RUNTIME
    imports BOOGIE-QUANTIFIERS-OBJECT
    imports BOOGIE-HELPERS
    imports INT
    imports MAP

    configuration <boogie>
                    <k> #initTypes ~> $PGM:Program ~> .DeclList ~> #start </k>
                    <types/>
                    <runtime/>
                    <procs/>
                    <freshCounter/>
                  </boogie>
```

```k
    rule <k> (D Decls):DeclList => D ~> Decls ... </k>
    rule <k> .DeclList => .K ... </k>
```

2 Types
-------

```k
    syntax KItem ::= "#initTypes"
    rule <k> #initTypes => #declareTypes ... </k>
         <types> .Bag
              => <type> <typeName> int  </typeName> ... </type>
                 <type> <typeName> bool </typeName> ... </type>
                 ...
         </types>
```

```k
    syntax KItem ::= "#declareTypes"
    rule <k> #declareTypes ~> TyD:TypeDecl Ds:DeclList
          => TyD ~> #declareTypes ~> Ds
             ...
         </k>
    rule <k> #declareTypes ~> D Ds:DeclList ~> NonTyDs:DeclList
          => #declareTypes ~> Ds            ~> NonTyDs ++DeclList D
             ...
         </k>
      requires notBool isTypeDecl(D)
    rule <k> #declareTypes ~> .DeclList => .K ... </k>
```

Type declarations:

```k
    rule <k> type Attrs T:Id,Ts ; => type Attrs Ts ; ... </k>
         <types> .Bag
              => <type> <typeName> T </typeName> ... </type>
                 ...
         </types>
    rule <k> type Attrs T:Id,Ts ; => type Attrs Ts ; ... </k>
         <typeName> T </typeName>
    rule <k> type _Attrs .IdList ; => . ... </k>
```

Type aliases:

```k
    rule <k> type _Attrs T:Id = T2 ; => .K ... </k>
         <types> .Bag
              => <type>
                   <typeName> T </typeName>
                   <synonym> T2 </synonym>
                   ...
                 </type>
                 ...
         </types>
```


3 Constants and functions
-------------------------

When we first encounter a type , we create an entry in the list of types.
Since `<type>` has `multiplicity="Map"` and the key for maps (i.e. the `<typeName>`)
must be unique, multiple entries aren't created for each type.

```k
    rule <k> const Attrs OptionalUnique X, Xs : T ;
          => const Attrs OptionalUnique X  : T ;
          ~> const Attrs OptionalUnique Xs : T ;
             ...
         </k>
      requires notBool Xs ==K .IdList
```

```k
    rule <k> const _:AttributeList .Nothing X, .IdList : T ; => X := inhabitants(T), .ExprList ; ... </k>
         <globals> (.Map => X:Id |-> value("undefined", T, true)) Rho </globals>
       requires notBool(X in_keys(Rho))
```

Functions are lambdas:

```k
    rule <k> function Attrs F (IdsTypeList) : TR { Expr }
          => function Attrs F (IdsTypeList) : TR ;
          ~> F := (lambda IdsTypeList :: Expr), .ExprList ;
             ...
         </k>
    rule <k> function Attrs F (IdsTypeList) : TR ;
          => const Attrs .Nothing (F, .IdList) : ([IdsTypeListToTypeList(IdsTypeList)]TR):Type ;
             ...
         </k>
    rule <k> function Attrs F (TypeList) : TR ;
          => const Attrs .Nothing (F, .IdList) : ([TypeList]TR):Type ;
             ...
         </k>
```

Function application is map lookup:

```k
    rule <k> (F:Id (Args:ExprList) => F[Args]):Expr ... </k>
```

### `unique`

The `<uniques>` cell maintains a list of `unique` constants that are `assumed`
distinct.

```k
    rule <k> const AttributeList (unique => .Nothing)  X:Id : T ;
          ~> (.K => assume .AttributeList #distinct(X, Uniques) ;)
             ...
         </k>
         <typeName> T </typeName>
         <uniques> Uniques => X, Uniques </uniques>
```

```k
    syntax Expr ::= #distinct(Id, IdList)
    // TODO: Should be `#distinct(Expr, ExprList)`; blocked on https://github.com/kframework/kore/issues/1817
    rule <k> #distinct(L, (R, Rs)) => L != R && #distinct(L, Rs) ... </k>
    rule <k> #distinct(L, .IdList) => true ... </k>
```

6 Axiom
-------

```k
    rule <k> axiom Attrs Expr ; ~> Ds:DeclList
          => Ds ~> axiom Attrs Expr ;
             ...
         </k>
    rule <k> axiom Attrs Expr ; => assume Attrs Expr ; ... </k> [owise]
```

9.0 Implementation Body
-----------------------

```k
    syntax KItem ::= "#start"
```

In the case of the verification semantics, we verify all procedures:

```verification
    rule <k> #start
          => #pause
          ~> makeDecls(IArgs) ~> makeDecls(IRets) ~> VarDeclList
          ~> havoc IdsTypeWhereListToIdList(IArgs) ++IdList IdsTypeWhereListToIdList(IRets) ++IdList LocalVarDeclListToIdList(VarDeclList);
          ~> assume .AttributeList (lambda IdsTypeWhereListToIdsTypeList(PArgs) :: Requires)[IdsTypeWhereListToExprList(IArgs)] ;
          ~> #collectLabels(StmtList)
         </k>
         (.CurrentImplCell => <currentImpl> N </currentImpl>)
         <globals> Globals </globals>
         <olds> .Map => Globals </olds>
         <procName> ProcedureName </procName>
         <args> PArgs </args>
         <rets> PRets </rets>
         <pres> Requires </pres>
         <impl>
            <implId> N </implId>
            <iargs> IArgs </iargs>
            <irets> IRets </irets>
            <body> { VarDeclList StmtList } </body>
         </impl>
```

`#collectLabels` splits procedure bodies into labeled blocks, and populates the
`<labels>` cell with a map from labels to their bodies.

```k
    syntax KItem ::= #collectLabels(StmtList)
    syntax Id ::= "$start" [token]
    rule <k> #collectLabels((_:Stmt _) #as StmtList)
          => #collectLabels($start : StmtList)
             ...
         </k>

    rule <k> #collectLabels(StartLabel:Id : StmtList)
          => #collectLabels(StartLabel, .StmtList, StmtList)
          ~> goto StartLabel;
             ...
         </k>

    syntax KItem ::= #collectLabels(currLabel: Id, block: StmtList, rest: StmtList)
    rule <k> #collectLabels(L, S1s, S2:Stmt S2s:StmtList)
          => #collectLabels(L, S1s ++StmtList S2 .StmtList, S2s)
             ...
         </k>
    rule <k> #collectLabels(L1, S1s,       L2: S2s:StmtList)
          => #collectLabels(L2, .StmtList, S2s:StmtList)
             ...
         </k>
         <labels> (.Map => L1 |-> S1s ++StmtList return;) Labels </labels>
    rule <k> #collectLabels(L, S1s, .StmtList)
          => .K
             ...
         </k>
         <labels> (.Map => L |-> S1s ++StmtList return;) Labels </labels>
```

We use `boogie` to infer invaraints and cutpoints.
We rearrange the generated `assume`s to work with cutpoints.

```k
    syntax Id ::= "inferred" [token]
    rule <k> #collectLabels(_L, _S1s,
                             ( ( assert { :inferred .AttrArgList } Inferred ;
                                 assert _:AttributeList Invariant ;
                                 S2s:StmtList
                               )
                            => ( assert { :code "Inferred" } { :source "???", 0 } Inferred; // This should never fail
                                 assert { :code "BP5004" } { :source "???", 0 } Invariant;
                                 cutpoint(!_:Int) ;
                                 assume .AttributeList Inferred;
                                 assume .AttributeList Invariant;
                                 S2s:StmtList
                           ) ) )
             ...
         </k> [priority(48)]

    rule <k> #collectLabels(_L, _S1s,
               assert { :inferred .AttrArgList } Inferred;
               ( (S2 S2s:StmtList)
              => ( assert .AttributeList true ;
                   S2 S2s:StmtList
             ) ) )
             ...
         </k>
      requires assert _:AttributeList _ ; :/=K  S2 [priority(48)]
```

```k
   rule <k> .LocalVarDeclList => .K ... </k>

   rule <k> var Attrs IdsTypeWhere, Rest:IdsTypeWhereList ; Vs:LocalVarDeclList
         => var Attrs IdsTypeWhere; var Attrs Rest; Vs
            ...
        </k>
     requires Rest =/=K .IdsTypeWhereList

   rule <k> var Attrs Xs : T            ; Vs:LocalVarDeclList
         => var Attrs Xs : T where true ; Vs
            ...
        </k>

   rule <k> var .AttributeList X:Id, Xs : T where Where; Vs:LocalVarDeclList
         => var .AttributeList       Xs : T where Where; Vs
            ...
        </k>
        <locals> (.Map => X:Id |-> value("undefined", T, Where)) Rho </locals>
     requires notBool( X in_keys(Rho) )

   rule <k> var .AttributeList X:Id, Xs : T where Where; Vs:LocalVarDeclList
         => var .AttributeList       Xs : T where Where; Vs
            ...
        </k>
        <locals> X |-> (_ => value("undefined", T, Where)) ... </locals>

   rule <k> var .AttributeList .IdList : T where Where; Vs:LocalVarDeclList
         => Vs
            ...
        </k>
```

```k
endmodule
```
