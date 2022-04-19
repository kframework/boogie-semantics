Boogie Semantics
================

```k
requires "helpers.md"
requires "quantification.md"
requires "syntax.md"

module BOOGIE-FRESH-COUNTER
    imports UNSIGNED-INT-SYNTAX
    configuration <freshCounter> 0 </freshCounter>
endmodule

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-FRESH-COUNTER
    imports BOOGIE-HELPERS
    imports INT
    imports MAP
    imports LIST
    imports STRING
    imports ID

    configuration <boogie>
                    <k> #initTypes ~> $PGM:Program ~> .DeclList ~> #start </k>
                    <types>
                      <type multiplicity="*" type="Map">
                          <typeName> #token("TypeName", "Id"):Type </typeName>
                          <synonym multiplicity="?">  #token("TypeName", "Id"):Type </synonym>
                          <uniques> .IdList </uniques>
                      </type>
                    </types>
                    <runtime>
                      <locals> .Map </locals>
                      <globals> .Map </globals>
                      <olds> .Map </olds>
                      <cutpoints> .List </cutpoints>
                      <currentImpl multiplicity="?"> -1 </currentImpl>
                      <freshVars> .K </freshVars>
                    </runtime>
                    <procs>
                      <proc multiplicity="*" type="Map">
                        <procName> #token("ProcedureName", "Id") </procName>
                        <args> .IdsTypeWhereList </args>
                        <rets> .IdsTypeWhereList </rets>
                        <pres> true:Expr </pres>   // requires
                        <posts> true:Expr </posts> // ensures
                        <mods> .IdList </mods>   // modifies
                        <impls>
                          <impl multiplicity="*" type="Map">
                            <implId> -1 </implId>
                            <labels> .Map </labels>
                            <iargs> .IdsTypeWhereList </iargs>
                            <irets> .IdsTypeWhereList </irets>
                            <vars>  .LocalVarDeclList </vars>
                          </impl>
                        </impls>
                      </proc>
                    </procs>
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

4 Expressions
-------------

```k
    syntax KResult ::= ValueExpr
    syntax Expr ::= ValueExpr
    syntax ValueExpr ::= FreshValue
    rule isKResult(E, Es:ExprList) => isKResult(E) andBool isKResult(Es)
    rule isKResult(.ExprList) => true
    syntax FreshValue ::= Bool | Int | String

    rule <k> X:Id => value(lookupVariable(X)) ... </k>

    context HOLE _:RelOp _RHS
    context _LHS:ValueExpr _:RelOp HOLE

    rule <k> LHS:ValueExpr == RHS:ValueExpr => LHS ==K RHS ... </k>
      requires notBool(isMapValue(LHS)      orBool isMapValue(RHS)
                   orBool isLambdaExpr(LHS) orBool isLambdaExpr(RHS))
    rule <k> LHS:ValueExpr != RHS:ValueExpr => LHS =/=K RHS ... </k>
      requires notBool(isMapValue(LHS)      orBool isMapValue(RHS)
                   orBool isLambdaExpr(LHS) orBool isLambdaExpr(RHS))

    rule <k> *:Expr => true  ... </k>
    rule <k> *:Expr => false ... </k>

    rule <k> LHS <  RHS => LHS  <Int RHS ... </k>
    rule <k> LHS >  RHS => LHS  >Int RHS ... </k>
    rule <k> LHS <= RHS => LHS <=Int RHS ... </k>
    rule <k> LHS >= RHS => LHS >=Int RHS ... </k>

    context HOLE _:AddOp _E2
    context _:ValueExpr _:AddOp HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
    rule <k> V1 - V2 => V1 -Int V2 ... </k>

    context HOLE _:MulOp _E2
    context _:ValueExpr _:MulOp HOLE
    rule <k> V1 * V2 => V1 *Int V2 ... </k>

    context HOLE || _E2
    rule <k> true  || _   => true  ... </k>
    rule <k> false || RHS => RHS   ... </k>

    context HOLE && _E2
    rule <k> true  && RHS  => RHS   ... </k>
    rule <k> false && _RHS => false ... </k>

    context (HOLE:Expr ==> _E2:Expr):Expr
    rule <k> false ==> _ => true  ... </k>
    rule <k> true  ==> B => B     ... </k>

    context (HOLE:Expr <==> _E2:Expr):Expr
    context _:ValueExpr <==> HOLE
    rule <k> B:Bool <==> B  => true  ... </k>
    rule <k> B1     <==> B2 => false ... </k>
      requires B1 =/=Bool B2

    context _:UnOp HOLE
    rule <k> ! B => notBool(B) ... </k>
    rule <k> - I:Int => 0 -Int I ... </k>

    context if HOLE then _ else _
    rule <k> if true  then True  else _     => True  ... </k>
    rule <k> if false then _     else False => False ... </k>
```

Coersions are ignored for now:

```k
    rule <k> E:Expr : _:Type => E ... </k>
```

### Variable lookup

```k
    syntax Value ::= value(value: ValueExpr, type: Type, where: Expr)
                   | "#undefined"

    syntax Value ::= lookupVariable(Id) [function]
    rule [[ lookupVariable(X:Id) => V ]]
         <locals> X |-> V:Value ... </locals>

    rule [[ lookupVariable(X:Id) => V ]]
         <locals> Env </locals>
         <globals> X |-> V:Value ... </globals>
      requires notBool X in_keys(Env)
```

### 4.1 Map selection and update

####  Selection

```k
    syntax ValueExpr ::= MapValue
    syntax FreshMapValue ::= map(Int, Type)
    syntax FreshValue ::= FreshMapValue
    syntax MapValue ::= FreshMapValue
                      | update(key: ExprList, value: ValueExpr, mapx: MapValue)
    syntax Expr      ::= select(ExprList, MapValue)

    context (HOLE [ _ ]):Expr
    context (_:MapValue [ HOLE ]):Expr

    rule <k> (Map:MapValue [ Key ]):Expr => select(Key, Map) ...  </k> requires isKResult(Key)
    rule <k> select(S, update(Key, Val, Map)) => Val ...            </k> requires Key  ==K S
    rule <k> select(S, update(Key, _, Map))   => select(S, Map) ... </k> requires Key =/=K S

    rule <k> select(.ExprList,     map(Id, [ArgT]RetT)) => intToT(RetT, lookupMap0(Id))                                              ... </k>
    rule <k> select(S,             map(Id, [ArgT]RetT)) => intToT(RetT, lookupMap1(Id, TToInt(S)))                                   ... </k>
    rule <k> select((S1,S2),       map(Id, [ArgT]RetT)) => intToT(RetT, lookupMap2(Id, TToInt(S1),TToInt(S2)))                       ... </k>
    rule <k> select((S1,S2,S3),    map(Id, [ArgT]RetT)) => intToT(RetT, lookupMap3(Id, TToInt(S1),TToInt(S2),TToInt(S3)))            ... </k>
    rule <k> select((S1,S2,S3,S4), map(Id, [ArgT]RetT)) => intToT(RetT, lookupMap4(Id, TToInt(S1),TToInt(S2),TToInt(S3),TToInt(S4))) ... </k>

    // Uninterpreted function
    syntax Int ::= lookupMap0(mapId: Int)                            [function, functional, smtlib(lookupMap0), no-evaluators]
    syntax Int ::= lookupMap1(mapId: Int, keys: Int)                 [function, functional, smtlib(lookupMap1), no-evaluators]
    syntax Int ::= lookupMap2(mapId: Int, keys: Int, Int)            [function, functional, smtlib(lookupMap2), no-evaluators]
    syntax Int ::= lookupMap3(mapId: Int, keys: Int, Int, Int)       [function, functional, smtlib(lookupMap3), no-evaluators]
    syntax Int ::= lookupMap4(mapId: Int, keys: Int, Int, Int, Int)  [function, functional, smtlib(lookupMap4), no-evaluators]
```

#### Update

```k
    rule <k> X:Id [ Key ], .LhsList := Value, .ExprList ; => X := X [ Key := Value ], .ExprList ; ... </k>

    context HOLE [ _ := _ ]
    context Map:MapValue [ HOLE := _Value ]
    context Map:MapValue [ Key := HOLE ] requires isKResult(Key)
    rule <k> Map:MapValue [ Key := Value ] => update(Key, Value, Map) ... </k> requires isKResult(Key)
```

```k
    context (HOLE, _):ExprList
    context (_:ValueExpr, HOLE):ExprList
```

### Lambdas

```k
    context _:LambdaExpr [ HOLE ]
    syntax ValueExpr ::= LambdaExpr
    rule <k> (lambda Bound :: Exp)[Vals]
          => makeDecls(IdsTypeListToIdsTypeWhereList(Bound))
          ~> makeAssignments(IdsTypeListToIdList(Bound), Vals)
          ~> Exp
          ~> #restoreLocals(Locals)
             ...
         </k>
         <locals> Locals </locals>
      requires isKResult(Vals)
```

```k
    syntax KItem ::= "#restoreLocals" "(" Map ")"
    rule <k> V:ValueExpr ~> (#restoreLocals(Locals) => .K) ... </k>
         <locals> _ => Locals </locals>
```

### 4.3 Old expressions

```k
    rule <k> old(E) => E ~> #restoreGlobals(Globals) ... </k>
         <globals> Globals => Olds </globals>
         <olds> Olds </olds>

    syntax KItem ::= "#restoreGlobals" "(" Map ")"
    rule <k> E:ValueExpr ~> (#restoreGlobals(Globals) => .K) ... </k>
         <globals> _ => Globals </globals>
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

7 Mutable Variables, states, and execution traces
-------------------------------------------------

```k
  rule <k> var Attrs X,Xs : T:Type ;:Decl
        => var Attrs X    : T:Type ;:Decl
        ~> var Attrs Xs   : T:Type ;:Decl
           ...
       </k>
    requires notBool Xs ==K .IdList

  rule <k> var .AttributeList X:Id : T:Type ;:Decl
        => X := inhabitants(T), .ExprList ;
           ...
       </k>
       <globals> (.Map => X:Id |-> value("undefined", T, true)) Rho </globals>
     requires notBool( X in_keys(Rho) )
```

8 Procedures and implementations
--------------------------------

```k

```

Split procedures with a body into a procedure and an implementation:

```k
    rule <k> (procedure Attrs:AttributeList
                ProcedureName PSig:PSig SpecList
                Body):Decl
          => procedure Attrs:AttributeList
               ProcedureName PSig ; SpecList
          ~> implementation Attrs ProcedureName PSig
               Body
             ...
         </k>
```

```k
    rule <k> procedure      _:AttributeList _ProcedureName .Nothing ( _Args ) (.Nothing => returns (.IdsTypeWhereList)) ; _SpecList            ... </k>
    rule <k> implementation _:AttributeList _ProcedureName .Nothing ( _Args ) (.Nothing => returns (.IdsTypeWhereList)) { _VarList _StmtList } ... </k>
```

```k
    syntax KItem ::= "#populateProcedure"
    rule <k> (.K => #populateProcedure)
          ~> procedure _:AttributeList ProcedureName _TypeArgs ( Args ) returns ( Rets ) ; _SpecList
             ...
         </k>
         <procs> .Bag =>
           <proc>
             <procName> ProcedureName </procName>
             <args> Args </args>
             <rets> Rets </rets>
             ...
           </proc>
           ...
         </procs>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (.Nothing requires NewReq ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <pres> Reqs => Reqs && NewReq </pres>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (.Nothing ensures NewEnsures ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <posts> Ensures => Ensures && NewEnsures </posts>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (modifies Modifies ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <mods> .IdList => Modifies </mods>

    rule <k> ( #populateProcedure ~> procedure _:AttributeList _ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
               ; .SpecList
             )
          => .K
             ...
         </k>
```

```k
    rule <k> implementation Attrs:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets ) { VarDeclList StmtList }
          => #preprocess(N, StmtList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <impls> .Bag
              => <impl>
                   <implId> N </implId>
                   <iargs> IArgs </iargs>
                   <irets> IRets </irets>
                   <vars> VarDeclList </vars>
                   <labels> .Map </labels>
                 </impl>
                 ...
         </impls>
         <freshCounter> N => N +Int 1 </freshCounter>
```

`#preprocess` splits implementation bodies into labeled blocks, and populates the
`<labels>` cell with a map from labels to their bodies.

```k
    syntax KItem ::= #preprocess(implId: Int, StmtList)
    syntax KItem ::= #preprocess(implId: Int, currLabel: Id, block: StmtList, rest: StmtList)
```

Ensure that the label `$start` is the initial label.

```k
    syntax Id ::= "$start" [token]
    rule <k> #preprocess(Id, (Label : _) #as StmtList) => #preprocess(Id, $start, goto Label; .StmtList , StmtList) ... </k>
    rule <k> #preprocess(Id, (_:Stmt _)  #as StmtList) => #preprocess(Id, $start,             .StmtList,  StmtList) ... </k>
    rule <k> #preprocess(Id, (.StmtList) #as StmtList) => #preprocess(Id, $start,             .StmtList,  StmtList) ... </k>
```

Collect statements into blocks until we encounter the next label:

```k
    rule <k> #preprocess(Id, L, S1s, S2:Stmt S2s:StmtList)
          => #preprocess(Id, L, S1s ++StmtList S2 .StmtList, S2s)
             ...
         </k>
    rule <k> #preprocess(Id, L1, S1s,       L2: S2s:StmtList)
          => #preprocess(Id, L2, .StmtList, S2s:StmtList)
             ...
         </k>
         <implId> Id </implId>
         <labels> (.Map => L1 |-> S1s ++StmtList #location( return;, "boogie.md", 0, 0, 0, 0)) Labels </labels>
    rule <k> #preprocess(Id, L, S1s, .StmtList)
          => .K
             ...
         </k>
         <implId> Id </implId>
         <labels> (.Map => L |-> S1s ++StmtList #location( return;, "boogie.md", 0, 0, 0, 0)) Labels </labels>
```

We use `boogie` to infer invaraints and cutpoints.
We rearrange the generated `assume`s to work with cutpoints.

```k
    syntax Id ::= "inferred" [token]
    rule <k> #preprocess(_Id, _L, _S1s,
                          ( ( #location(assert { :inferred .AttrArgList } Inferred  ;, File1, Line1, Col1, _, _)
                              #location(assert _:AttributeList            Invariant ;, File2, Line2, Col2, _, _)
                              S2s:StmtList
                            )
                         => ( #assert(File1, Line1, Col1, "BAD INVARIANT INFERRED!") Inferred; // This should never fail
                              #assert(File2, Line2, Col2, "Error BP500{4,5}: This loop invariant might not hold.") Invariant;
                              cutpoint(!_:Int) ;
                              assume .AttributeList Inferred;
                              assume .AttributeList Invariant;
                              S2s:StmtList
                        ) ) )
             ...
         </k> [priority(48)]
```

If an invariant is not specified, we take it to be `true`:

```k
    rule <k> #preprocess(_Id, _L, _S1s,
               #location(assert { :inferred .AttrArgList } Inferred  ;, File, SLine, SCol, ELine, ECol)
               ( (S2 S2s:StmtList)
              => ( #location(assert .AttributeList true ;, File, SLine, SCol, ELine, ECol)
                   S2 S2s:StmtList
             ) ) )
             ...
         </k>
      requires #location(assert _:AttributeList _ ;, _, _, _, _, _) :/=K  S2 [priority(48)]
```

9 Statements
------------

```k
   rule <k> S Ss:StmtList => S ~> Ss ... </k>
   rule <k> .StmtList => .K ... </k>
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
          ~> goto $start;
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
            <vars> VarDeclList </vars>
            ...
         </impl>
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

9.2 Assertions and assumptions
------------------------------

We annotate assertions with location and type information.
The location information is placed using K's `[locations]` annotation.
(Note: We use a hack in [driver/driver] to get this to work with the Haskell backend)

```k
    rule <k> #location(assert _ Expr; , File, StartLine, StartCol, _EndLine, _EndCol):KItem
          => #assert(File, StartLine, StartCol, "Error BP5001: This assertion might not hold.") Expr ;
             ...
         </k>
    rule <k> #location(Stmt, File, StartLine, StartCol, _EndLine, _EndCol):KItem
          => Stmt
             ...
         </k> [owise]
```

```k
    syntax Stmt ::= #location(Stmt, String, Int, Int, Int, Int) [symbol]
    syntax KItem ::= "#failure" "(" String ")" [klabel(#failure), symbol]
    syntax Stmt ::= "#assert" "("file: String "," line: Int "," col: Int "," message: String ")" Expr  ";"
    context  #assert(_, _, _, _) HOLE ;
    rule <k> #assert(_, _, _, _) true ; => .K ... </k>
    rule <k> #assert(File, Line, Col, Message) false ;
          => #failure(File +String "(" +String Int2String(Line) +String
                                   "," +String Int2String(Col) +String "): " +String Message)
             ...
         </k>
```

```k
    context assume _ HOLE ;
    rule <k> assume _ true ; => .K      ... </k>
//    rule <k> assume _ false; => #Bottom ... </k>
    rule <k> assume _ false; ~> K => .K </k>
         <locals> _ => .Map </locals>
```

9.3 Assignments
---------------

```k
    context _:LhsList := HOLE ;
    rule <k> .LhsList := .ExprList ; => .K ... </k>
    rule <k> (X, Xs:LhsList) := (V:ValueExpr, Vs:ExprList) ;
          => X := V, .ExprList ;
          ~> Xs := Vs ;
             ...
         </k>
      requires isKResult(Vs) andBool Xs =/=K .LhsList
```

```k
    rule <k> X, .LhsList := V:ValueExpr, .ExprList ; => .K ... </k>
         <locals> X |-> value(... value: _ => V) ... </locals>
    rule <k> X, .LhsList := V:ValueExpr, .ExprList ; => .K ... </k>
         <locals> Env </locals>
         <globals> X |-> value(... value: _ => V) ... </globals>
         <currentImpl> CurrentImpl </currentImpl>
         <implId> CurrentImpl </implId>
         <mods> Modifies </mods>
      requires notBool X in_keys(Env)
       andBool         X in Modifies

    rule <k> X, .LhsList := V:ValueExpr, .ExprList ; => .K ... </k>
         <locals> Env </locals>
         <globals> X |-> value(... value: _ => V) ... </globals>
      requires notBool X in_keys(Env)
```

9.4 Havoc
---------

```k
    rule <k> havoc .IdList ; => .K ... </k>
    rule <k> havoc X, Xs ;
          => freshen(X)
          ~> havoc Xs;
          ~> assume .AttributeList where(lookupVariable(X)) ;
             ...
         </k>
```

Update an variable to store an *unconstrained* sybmolic value of the appropriate
type.

```k
    syntax KItem ::= freshen(IdList)
    rule <k> freshen(.IdList) => .K ... </k>
    rule <k> freshen(X:Id, Xs:IdList)
          => X, .LhsList := inhabitants(type(lookupVariable(X))), .ExprList ;
          ~> freshen(Xs)
             ...
         </k>
```

9.5 Label Statements and jumps
------------------------------

Non-deterministically transition to all labels

```k
    rule <k> (goto L, Ls ; ~> _) => (Stmts) </k>
         <labels> L |-> Stmts ... </labels>
         <currentImpl> Impl </currentImpl>
         <implId>      Impl </implId>
    rule <k> goto L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .IdList
```

```k
    context  if (HOLE)  { _:StmtList } else { _:StmtList }:Stmt
    // TODO: the LHS of the rewrite arrow was parsed as a StmtList,
    // so needed the KItem to force the correct disabiguation.
    // test2/BadLineNumber.bpl failed.
    rule <k> (if (true)  { Ss:StmtList } else { _           }):KItem => Ss:StmtList ... </k>
    rule <k> (if (false) { _           } else { Ss:StmtList }):KItem => Ss:StmtList ... </k>
```

### Extension: Cutpoints


See [note below](#where-cutpoint-interactions) about the interaction between `where` clauses and loops.

When we reach a particular cutpoint the first time, we treat it as an abstraction point
and replace modifiable variables with fresh symbolic values.

```k
    syntax Stmt ::= "cutpoint" "(" Int ")" ";"
```

```verification
    rule <k> cutpoint(I) ; => #generalize(envToIds(Rho) ++IdList Modifiable) ... </k>
         <locals> Rho </locals>
         <mods> Modifiable </mods>
         <cutpoints> (.List => ListItem(I)) Cutpoints </cutpoints>
      requires notBool I in Cutpoints
```

When we reach it a second time we can prune this execution branch, because the
assert/assume structure ensures that our current program state is a subset of
the states when we first encountered the cutpoint (modulo `free invariant`s and
`where` clauses.)

```verification
    rule <k> cutpoint(I) ; => assume .AttributeList (false); ... </k>
         <cutpoints> Cutpoints </cutpoints>
      requires I in Cutpoints
```

When executing concretely, cutpoints are simply a no-op.

```k
    syntax KItem ::= "#generalize" "(" IdList ")"
    rule <k> #generalize(.IdList) => .K ... </k>
    rule <k> #generalize(X, Rest) => freshen(X) ~> #generalize(Rest) ... </k>
```

```k
    syntax IdList ::= envToIds(Map) [function]
    rule envToIds(.Map) => .IdList
    rule envToIds(X:Id |-> Val Rho) => (X, envToIds(Rho))
```

#### `where`-cutpoint interactions

`where` clauses may be added to variable declarations, both globally and locally, as well as in implementation arguments.
e.g.:

```
var x : int : where x < y ;
var y : int : where y > 100 ;
```

[This is Boogie 2] describes its semantics as follows:

Page 19:

>  At times in an execution trace when the value of the variable is chosen arbitarily, the value is chosen to satisfy *WhereClause*

Page 30:

> Note that where clauses do not play a role  for assignemnt statements
> *Where* clauses apply only in places where a variable gets an arbitary value

Page 24:

> *Where* clauses are like free preconditions and (for out-parameters and modified global variables only) free postconditions

A free precondition is a requires clause for a procedure that is checked assumed
for "free" when checking the procedure's implementations but not checked when
calling the procedure.

Not mentioned in [This is Boogie 2], it also appears to behave as a free
invariant in while loops. i.e., the following program is verified successfully:

```
procedure P()
{
  var x: int where 0 <= x;
  x := 0 ;
  while (*) { x := x - 1; }
  assert 0 <= x;
}
```

Surprisingly, this also works once the while loop has been desugared. This also works:

```
procedure P();
implementation P()
{
  var x: int where 0 <= x;
  anon0:
    x := 0;
    goto anon3_LoopHead;
  anon3_LoopHead: // cut point
    assume {:inferred} x < 1;
    goto anon3_LoopDone, anon3_LoopBody;
  anon3_LoopBody:
    x := x - 1;
    goto anon3_LoopHead;
  anon3_LoopDone:
    assert {:source "y.bpl", 6} {:code "BP5001"} 0 <= x;
    return;
}
```

Even more surprisingly, only the `where` clauses of variables whose values have changed are applied:

```
procedure P();
implementation P() {
    var x : int where x == 6 ;
    x := 7;
    while (*) { }
    assert x == 7 ; // succeeds
}

implementation P() {
    var x : int where x == 6 ;
    x := 7;
    while (*) { x := x ; }
    assert x == 7 ; // fails
}
```

Another surprising program from Boogie's test suite is:

```
procedure R2()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  y := 10;
  while (*) {
    w := w + 1;
    assert w == 6;
    y := y + 2;
    assert 7 <= y;
  }
  assert x == 5 && 0 <= y - w;
  assert y == 10;  // error
}
```

and another:

```
procedure P()
{
  var x: int where 0 <= x;
  x := -1 ;
  while (*) { x := x; }
  assert 0 <= x; //succeed
  x := x - 1;
  while (*) {  }
  assert 0 <= x; // should fail
}
```

9.6 Return statements
---------------------

When returning, we first `assert` that the post condition holds:

```k
    syntax Stmt ::= "#return" ExprList ";"
    rule <k> #location(return ;, File, Line, Col, _, _):KItem
          => #assert (File, Line, Col, "Error BP5003: A postcondition might not hold on this return path.")
                   (lambda IdsTypeWhereListToIdsTypeList(PArgs) ++IdsTypeList IdsTypeWhereListToIdsTypeList(PRets)
                        :: Ensures
                   ) [ IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets) ] ;
             #return IdsTypeWhereListToExprList(IRets) ;
             ...
         </k>
         <currentImpl> CurrentImpl </currentImpl>
         <procName> CurrentProc </procName>
         <iargs> IArgs </iargs>
         <irets> IRets </irets>
         <implId> CurrentImpl </implId>
         <posts> Ensures </posts>
         <args> PArgs </args>
         <rets> PRets </rets>
```

```verification
    rule <k> (#return Rets ; ~> K:K) => .K </k>
```

9.7 If statements
-----------------

9.8 While loops
---------------

9.9 Call statements
-------------------

```k
    rule <k> #location( call ProcedureName:Id(ArgVals) ;
                     => call .IdList := ProcedureName:Id(ArgVals) ;
                      , _, _, _, _, _):KItem
             ...
         </k>
```

```verification
    context #location(call X:IdList := ProcedureName:Id(HOLE) ;, _, _, _, _, _)
    rule <k> #location(call X:IdList := ProcedureName:Id(ArgVals) ;, File, Line, Col, _, _):KItem
          => #assert(File, Line, Col, "Error BP5002: A precondition for this call might not hold.")
               (lambda IdsTypeWhereListToIdsTypeList(Args) :: Requires)[ArgVals];
          ~> freshen(X ++IdList Mods)
          ~> assume .AttributeList ( lambda IdsTypeWhereListToIdsTypeList(Args) ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rets)
                                         :: Ensures )
                                   [ ArgVals ++ExprList IdListToExprList(X) ] ;
             ...
         </k>
         <procName> ProcedureName </procName>
         <args> Args </args>
         <rets> Rets </rets>
         <pres> Requires </pres>
         <posts> Ensures </posts>
         <mods> Mods </mods>
      requires isKResult(ArgVals)
```

Inhabitants
-----------

`inhabitants(T)` represents the inhabitants of a type. Semantically, this is
similar to matching logic's `[[ Sort ]]` (also pronounced "inhabitants").

Note: The Haskell backend alpha-renames variables in some situations. The
`<freshVars>` cell is used to keep track of the original names while evaluating
quantifiers.

```k
    syntax Expr ::= inhabitants(Type)
 // ------------------------------------------------------
    rule <k> inhabitants(T)  => intToT(T, ?V:Int) ... </k>
         <freshVars> K:K => (K ~> ?V) </freshVars>

    syntax Expr ::= intToT(Type, Int)
 // -------------------------------------------------
    rule <k> intToT(int,  I) => I            ... </k>
    rule <k> intToT(bool, I) => intToBool(I) ... </k>
    rule <k> intToT([A]R, I) => map(I, [A]R) ... </k>
    rule <k> intToT(T, I)    => I            ... </k>
         <type>
           <typeName> T:Id </typeName>
           <uniques> _ </uniques>
        // No SynonymCell
         </type>
    rule <k> intToT(T, I) => intToT(S, I) ... </k>
         <typeName> T </typeName>
         <synonym> S </synonym>

    syntax Int ::= TToInt(ValueExpr) [function]
 // --------------------------------------------------------------------
    rule TToInt(B:Bool)    => #if B #then 0 #else 1 #fi [simplification]
    rule TToInt(I:Int)     => I                         [simplification]
    rule TToInt(map(I, _)) => I                         [simplification]

    syntax Bool ::= intToBool(Int)               [function, functional, smtlib(intToBool), no-evaluators]
```

```k
endmodule
```
