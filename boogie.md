Boogie Semantics
================

```k
requires "syntax.md"
requires "procedures.md"
requires "runtime.md"
requires "helpers.md"

module BOOGIE-FRESH-COUNTER
    imports INT-SYNTAX
    configuration <freshCounter> 0 </freshCounter>
endmodule

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-FRESH-COUNTER
    imports BOOGIE-PROCEDURES
    imports BOOGIE-RUNTIME
    imports BOOGIE-HELPERS
    imports INT
    imports MAP

    configuration <boogie>
                    <k> $PGM:Program ~> #start </k>
                    <runtime/>
                    <types>
                      <type multiplicity="*" type="Map">
                          <typeName> #token("TypeName", "Id"):Type </typeName>
                          <uniques> .IdList </uniques>
                      </type>
                    </types>
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

TODO: We do not check if a type has been declared before being used yet.

```k
    rule <k> type _Attrs _T:Id ; => .K ... </k>
```

When we first encounter a type , we create an entry in the list of types.
Since `<type>` has `multiplicity="Map"` and the key for maps (i.e. the `<typeName>`)
must be unique, multiple entries aren't created for each type.

```k
    rule <k> (const _:AttributeList _:OptionalUnique _:IdList : T:Type ;) ... </k>
         <types> .Bag
              => <type> <typeName> T </typeName> ... </type>
                 ...
         </types>
```

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
    rule <k> const _:AttributeList .Nothing X, .IdList : T ; => .K ... </k>
         <typeName> T </typeName>
         <globals> (.Map => X:Id |-> value(inhabitants(T, FreshInt), T, true)) Rho </globals>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
       requires notBool( X in_keys(Rho) )
```

Functions are constant maps:

```k
    rule <k> function Attrs F (X:Id : TX:Type, .IdsTypeList) : TR ;
          => const Attrs .Nothing (F, .IdList) : ([TX]TR):Type ;
             ...
         </k>
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
    rule <k> axiom Attrs Expr ; => assume Attrs Expr ; ... </k>
```

9.0 Implementation Body
-----------------------

```k
    syntax KItem ::= "#start"
```

In the case of the verification semantics, we verify all procedures:

```verification
    rule <k> #start
          => makeDecls(IArgs) ~> makeDecls(IRets) ~> VarDeclList
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

However, in the operational semantics we only execute the main procedure:

```operational
    syntax Id ::= "main" [token]
    rule <k> #start => #call main(.ExprList) ... </k>
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
        <locals> (.Map => X:Id |-> value(inhabitants(T, Loc), T, Where)) Rho </locals>
        <freshCounter> Loc  => Loc  +Int 1 </freshCounter>
     requires notBool( X in_keys(Rho) )
     
   rule <k> var .AttributeList X:Id : T where Where; Vs:LocalVarDeclList
         => Vs
            ...
        </k>
        <locals> X |-> (_ => value(inhabitants(T, Loc), T, Where)) ... </locals>
        <freshCounter> Loc  => Loc  +Int 1 </freshCounter>
```

```k
endmodule
```
