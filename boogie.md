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

```k
    rule <k> type _Attrs T:Id ; ... </k>
         <types> .Bag
              => <type>
                   <typeName> T </typeName>
                   ...
                 </type>
                 ...
         </types>

    rule <k> type _Attrs T:Id ; => .K ... </k>
         <typeName> T </typeName>
```

3 Constants and functions
-------------------------

When we first encounter a type , we create an entry in the list of types.
Since `<type>` has `multiplicity="Map"` and the key for maps (i.e. the `<typeName>`)
must be unique, multiple entries aren't created for each type.

3 Constants and functions
-------------------------

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

Functions are constant maps:

```k
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
          ~> #collectLabel(StartLabel, .StmtList) ~> StmtList
          ~> goto StartLabel;
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
            <body> { VarDeclList StartLabel: StmtList } </body>
         </impl>
```

This is used to reduce RAM usage by taking only one branch at a time (see driver.md)

```k
    syntax KItem ::= "#pause" [symbol, klabel(pause)]
```

```k
   rule <k> .LocalVarDeclList => .K ... </k>

   rule <k> var .AttributeList X:Id : T           ; Vs:LocalVarDeclList
         => var .AttributeList X:Id : T where true; Vs
            ...
        </k>

   rule <k> var .AttributeList X:Id : T where Where; Vs:LocalVarDeclList
         => Vs
            ...
        </k>
        <locals> (.Map => X:Id |-> value("undefined", T, Where)) Rho </locals>
     requires notBool( X in_keys(Rho) )

   rule <k> var .AttributeList X:Id : T where Where; Vs:LocalVarDeclList
         => Vs
            ...
        </k>
        <locals> X |-> (_ => value("undefined", T, Where)) ... </locals>
```

```k
endmodule
```
