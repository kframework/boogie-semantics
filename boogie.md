Boogie Semantics
================

```k
requires "syntax.md"
requires "substitution.md"
requires "quantifiable-builtins.md"

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-SUBSTITUTION
    imports ID
    imports QUANTIFIABLE-BUILTINS
    imports MAP
    imports STRING

    configuration <boogie>
                    <k> $PGM:Program ~> #start </k>
                    <env> .Map </env>
                    <globals> .Map </globals>
                    <olds> .Map </olds>
                    <store> .Map </store>
                    <labels> .Map </labels>
                    <cutpoints> .List </cutpoints>
                    <currentImpl multiplicity="?"> -1 </currentImpl>
                    <types>
                      <type multiplicity="*" type="Map">
                          <typeName> #token("TypeName", "Id") </typeName>
                          <uniques> .IdList </uniques>
                      </type>
                    </types>
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
                            <body> { .LocalVarDeclList .StmtList } </body>
                            <iargs> .IdsTypeWhereList </iargs>
                            <irets> .IdsTypeWhereList </irets>
                          </impl>
                        </impls>
                      </proc>
                    </procs>
                    <freshCounter> 0 </freshCounter>
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
    rule <k> type Attrs T:Id ; => .K ... </k>
```

When we first encounter a type , we create an entry in the list of types.
Since `<type>` has `multiplicity="Map"` and the key for maps (i.e. the `<typeName>`)
must be unique, multiple entries aren't created for each type.

```k
    rule <k> const Attrs OptionalUnique _:Id : T ; ... </k>
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
    rule isKResult(E, Es:ExprList) => isKResult(E) andBool isKResult(Es)
    rule isKResult(.ExprList) => true
    syntax ValueExpr ::= QBool | QInt | String

    rule <k> X:Id => V ... </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> value(... value: V) ... </store>

    rule <k> X:Id => V ... </k>
         <env> Env </env>
         <globals> X |-> value(... value: V) ... </globals>
      requires notBool X in_keys(Env)

    context HOLE _:RelOp _RHS
    context _LHS:ValueExpr _:RelOp HOLE

    rule <k> LHS:ValueExpr == RHS:ValueExpr => LHS ==K RHS ... </k>
    rule <k> LHS:ValueExpr != RHS:ValueExpr => LHS =/=K RHS ... </k>

    rule <k> LHS <  RHS => LHS  <Int RHS ... </k>
    rule <k> LHS >  RHS => LHS  >QInt RHS ... </k>
    rule <k> LHS <= RHS => LHS <=Int RHS ... </k>
    rule <k> LHS >= RHS => LHS >=Int RHS ... </k>

    context HOLE _:AddOp _E2
    context _:ValueExpr _:AddOp HOLE
    rule <k> V1 + V2 => V1 +QInt V2 ... </k>
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
```

### 4.1 Map selection and update

####  Selection

```k
    syntax ValueExpr ::= MapValue
    syntax MapValue ::= map(Int)
                      | update(key: ExprList, value: ValueExpr, mapx: MapValue)
    syntax Expr      ::= select(ExprList, MapValue)

    context (HOLE [ _ ]):Expr
    context (_:MapValue [ HOLE ]):Expr

    rule <k> (Map:MapValue [ Key ]):Expr => select(Key, Map) ...  </k> requires isKResult(Key)

    rule <k> select(Key, update(Key, Val, Map)) => Val ... </k>
    rule <k> select(S, update(Key, _, Map)) =>  select(S, Map) ... </k> requires Key =/=K S
    rule <k> select(S, map(Id)) => lookupMap(Id, S) ... </k>

    // Uninterpreted function
    syntax Int ::= lookupMap(mapId: Int, key: ExprList) [function, functional, smtlib(lookupMap), no-evaluators]
```

#### Update

```k
    rule <k> X:Id [ Key ] := Value ; => X := X [ Key := Value ] ; ... </k>

    context HOLE [ _ := _ ]
    context Map:MapValue [ HOLE := _Value ]
    context Map:MapValue [ Key := HOLE ] requires isKResult(Key)
    rule <k> Map:MapValue [ Key := Value ] => update(Key, Value, Map) ... </k> requires isKResult(Key)
```

```k
    context (HOLE, _):ExprList
    context (_:ValueExpr, HOLE):ExprList
```

### 4.3 Old expressions

```k
    rule <k> old(E) => E ~> #endOld(Globals) ... </k>
         <globals> Globals => Olds </globals>
         <olds> Olds </olds>

    syntax KItem ::= "#endOld" "(" Map ")"
    rule <k> E:ValueExpr ~> (#endOld(Globals) => .K) ... </k>
         <globals> _ => Globals </globals>
```

### 4.4 Logical quantifiers

In denotational semantics:

`[[ forall X . E ]] \sigma =  \forall x . ( [[ E ]] \sigma[X/x] )`

where $\forall$ is the matching logic forall.
I.e. if, for all values of `X` the denotation of `E` agrees, then `forall X . E` has that denotation.
Otherwise `forall X . E` denotes bottom.

In a big step semantics:

```
 forall x \in inhabitants(T)   (E ~> K, sigma[ X / x]) => V
----------------------------------------------------------------
       ( forall X : T . E ~> K , sigma ) =>  V
```

The expression `forall X : T . E` reaches a value `V`, iff for all values of `X`
the evaluation of `E` reaches `V`.


```k
    syntax Expr ::= "#hole"
    rule <k> (#forall X : T :: Expr ) => substitute(Expr, X, bound(X)) ~> (#forall X : T :: #hole) ... </k> requires notBool isKResult(Expr)
    rule <k> B:QBool ~> (#forall X : T :: #hole)
          => (#forall X : T :: B)
             ...
         </k>

    syntax Bool ::= smtforall(Id, QBool) [function, functional, no-evaluators, smt-hook((forall ((#1 Int)) #3))]
    rule <k> (#forall X : int :: Expr) => smtforall(X , Int, Expr) ... </k>
```

7 Mutable Variables, states, and execution traces
-------------------------------------------------

```k
  rule <k> var .AttributeList X:Id : T ;:Decl => .K ... </k>
       <globals> (.Map => X:Id |-> value(inhabitants(T, FreshInt), T, true)) Rho </globals>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
     requires notBool( X in_keys(Rho) )
```

8 Procedures and implementations
--------------------------------

Split procedures with a body into a procedure and an implementation:

```k
    rule <k> (procedure Attrs:AttributeList
                ProcedureName .Nothing ( Args ) returns ( Rets ) SpecList
                Body):Decl
          => procedure Attrs:AttributeList
               ProcedureName .Nothing ( Args ) returns ( Rets ) ; SpecList
          ~> implementation Attrs ProcedureName .Nothing ( Args ) returns ( Rets )
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
    rule <k> implementation Attrs:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets ) Body
          => .K
             ...
         </k>
         <procName> ProcedureName </procName>
         <impls> .Bag
              => <impl>
                   <implId> N </implId>
                   <body> Body </body>
                   <iargs> IArgs </iargs>
                   <irets> IRets </irets>
                 </impl>
                 ...
         </impls>
         <freshCounter> N => N +Int 1 </freshCounter>
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

    rule <k> #start
          => makeDecls(IArgs) ++LocalVarDeclList
             makeDecls(IRets) ++LocalVarDeclList
             VarList
          ~> havoc .IdList ;
          ~> assume .AttributeList substitute(Requires, IdsTypeWhereListToIdList(PArgs), IdsTypeWhereListToExprList(IArgs) ) ;
          ~> StartLabel: StmtList
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
            <body> { VarList StartLabel: StmtList } </body>
         </impl>
```

```k
   rule <k> .LocalVarDeclList => .K ... </k>

   rule <k> var .AttributeList X:Id : T           ; Vs:LocalVarDeclList
         => var .AttributeList X:Id : T where true; Vs
            ...
        </k>

   syntax Value ::= value(value: ValueExpr, type: Type, where: Expr)
   rule <k> ( var .AttributeList X:Id : T where Where; Vs:LocalVarDeclList
           ~> havoc Xs ;
            )
         => Vs
         ~> havoc Xs ++IdList X ;
            ...
        </k>
        <env> (.Map => X:Id |-> Loc) Rho </env>
        <store> .Map => Loc:Int |-> value(inhabitants(T, Loc), T, Where) ... </store>
        <freshCounter> Loc  => Loc  +Int 1 </freshCounter>
     requires notBool( X in_keys(Rho) )
```

9.2 Assertions and assumptions
------------------------------

```k
    syntax KItem ::= "#failure" "(" String ")" [klabel(#failure), symbol]
    syntax KItem ::= "#failure" "(" AttributeList "," String ")"
    syntax Id ::= "source" [token] | "code"   [token] | "procedure" [token]
    rule #failure(.AttributeList, Message)
      => #failure(Message)
    rule #failure({ :source File, Line, .AttrArgList } Attrs, Message)
      => #failure(Attrs, File +String "(" +String Int2String(Line) +String ",00): " +String Message)
    rule #failure({ :code Code, .AttrArgList } Attrs, Message)
      => #failure(Attrs, Message +String "Error " +String Code +String ": ")
    rule #failure({ :procedure Procedure, .AttrArgList } Attrs, Message)
      => #failure(Attrs, Message +String " " +String Id2String(Procedure))
```

```k
    context assert Attributes HOLE ;
    rule <k> assert Attributes true ; => .K ... </k>
    rule <k> (.K => #failure(Attributes, ""))
          ~> assert Attributes false;
             ...
         </k>
```

```k
    context assume _ HOLE ;
    rule <k> assume _ true ;      => .K ... </k>
    rule <k> assume _ false; ~> K => .K </k>
         <store> _ => .Map </store>
```

9.3 Assignments
---------------

TODO: This needs to work over lists of expressions and identifiers

```k
    context _X:Id := HOLE ;
    rule <k> X := V:ValueExpr ; => .K ... </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> value(... value: _ => V) ... </store>

    rule <k> X := V:ValueExpr ; => .K ... </k>
         <env> Env </env>
         <globals> X |-> value(... value: _ => V) ... </globals>
         <currentImpl> CurrentImpl </currentImpl>
         <implId> CurrentImpl </implId>
         <mods> Modifies </mods>
      requires notBool X in_keys(Env)
       andBool         X in Modifies
```

9.4 Havoc
---------

```k
    rule <k> havoc .IdList ; => .K ... </k>
    rule <k> havoc X, Xs ;
          => freshen(X)
          ~> havoc Xs;
          ~> assume .AttributeList Where ;
             ...
         </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> value(... where: Where) ... </store>
```

9.5 Label Statements and jumps
------------------------------

`#collectLabel` splits procedure bodies into labeled blocks, and populates the
`<label>` cell with a map from labels to their bodies.

```k
    syntax KItem ::= #collectLabel(Id, StmtList)
    rule <k> Id:  => #collectLabel(Id, .StmtList) ... </k>
    rule <k> (#collectLabel(L, S1s) ~> S2:Stmt S2s:StmtList)
          => (#collectLabel(L, S1s ++StmtList S2 .StmtList) ~> S2s)
             ...
         </k>
      requires S2 =/=K cutpoint;
    rule <k> (#collectLabel(L, S1s) => .K)
          ~> (L2: _S2 _S2s:StmtList) #Or .StmtList
             ...
         </k>
         <labels> (.Map => L |-> S1s) Labels </labels>
```

Non-deterministically transition to all labels

```k
    rule <k> (goto L, Ls ; ~> _) => Stmts </k>
         <labels> L |-> Stmts ... </labels>
    rule <k> goto L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .IdList
```

### Extension: Cutpoints

We use `boogie` to infer invaraints and cutpoints.
Boogie marks labels that are cutpoints with the comment `// cut point`.
We preprocess this comment into a `Stmt` "`cutpoint;`" that we handle.

See [note below](#where-cutpoint-interactions) about the interaction between `where` clauses and loops.

Boogie does not place the `cutpoint` mark, the inferred invariants and the loop
invariant assertsions in the "right" order. The following code rearranges them
into an order that makes more sense for us. In particular, we must `assert` all
invariants (inferred or annotated) before the cutpoint, replace the store with
fresh symbolic values `<store>` and finally `assume` the invariants.

We also need to be able to distinguish between different cutpoints.
Ideally, \K would mark this with source line information but it does not.
So we mark them with fresh integers in this preprocessing pass.

```k
    syntax Id ::= "inferred" [token]
    rule <k> #collectLabel(_L, _S1s)
          ~> ( ( cutpoint;
                 assume { :inferred .AttrArgList } Inferred;
                 assert .AttributeList Invariant ;
                 S2s:StmtList
               )
            => ( assert { :code "Inferred" } { :source "???", 0 } Inferred; // This should never fail
                 assert { :code "BPInvariant" } { :source "???", 0 } Invariant;
                 cutpoint(!_:Int) ;
                 assume { :inferred .AttrArgList } Inferred;
                 assume .AttributeList Invariant;
                 S2s:StmtList
             ) )
             ...
         </k>
```

If a while loop doesn't have an invariant specified, then there is no
`assert` statement following the `assume` after the `cutpoint`. This rule
add one there so that the previous rule may fire.

```k
    rule <k> #collectLabel(_L, _S1s)
          ~> cutpoint;
             assume { :inferred .AttrArgList } Inferred;
             ( (S2 S2s:StmtList)
            => ( assert .AttributeList true ;
                 S2 S2s:StmtList
               )
             )

             ...
         </k>
      requires assert .AttributeList _ ; :/=K  S2
```

When we reach a paticular cutpoint the first time, we treat it as an abstraction point
and replace all values in the `<store>` with fresh symbolic values.

```k
    syntax Stmt ::= "cutpoint" "(" Int ")" ";"
    rule <k> cutpoint(I) ; => #generalize(keys_list(Rho)) ... </k>
         <env> Rho </env>
         <cutpoints> (.List => ListItem(I)) Cutpoints </cutpoints>
      requires notBool I in Cutpoints
```

When we reach it a second time we can prune this execution branch, because the
assert/assume structure ensures that our current program state is a subset of
the states when we first encountered the cutpoint (modulo `free invariant`s and
`where` clauses.)

```k
    rule <k> cutpoint(I) ; => assume .AttributeList (false); ... </k>
         <cutpoints> Cutpoints </cutpoints>
      requires I in Cutpoints
```

```k
    syntax KItem ::= "#generalize" "(" List ")"
    rule <k> #generalize(.List) => .K ... </k>
    rule <k> #generalize(ListItem(X:Id) Rest) => freshen(X) ~> #generalize(Rest) ... </k>
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

```k
    rule <k> return ; ~> _
          => assert { :code "BP5003" } { :source "???", 0 } { :procedure CurrentProc }
                     substitute( Ensures
                               , IdsTypeWhereListToIdList(PArgs) ++IdList IdsTypeWhereListToIdList(PRets)
                               , IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets)
                               ) ;
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

9.7 If statements
-----------------

9.8 While loops
---------------

9.9 Call statements
-------------------

```k
    rule <k> call X:Id := ProcedureName:Id(ArgVals) ;
          => assert { :code "BPRequires" } { :source "???", 0 }
               substitute(Requires, IdsTypeWhereListToIdList(Args), ArgVals) ;
          ~> freshen(X)
          ~> assume .AttributeList substitute( Ensures
                                             , IdsTypeWhereListToIdList(Args) ++IdList IdsTypeWhereListToIdList(Rets)
                                             , ArgVals ++ExprList X
                                             ) ;
             ...
         </k>
         <procName> ProcedureName </procName>
         <args> Args </args>
         <rets> Rets </rets>
         <pres> Requires </pres>
         <posts> Ensures </posts>
```

Helpers
-------

`inhabitants(T)` represents the inhabitants of a type.

Semantically, this is similar to matching logic's `[[ Sort ]]` (also pronounced "inhabitants").

The Haskell backend does not allow `[anywhere]` rules (or equations) to use existential variables.
This *cannot* be a function. Functions must return a single value, whereas here we return the set of all possible values of a type.
Hence, we use a macro.

```k
    syntax ValueExpr ::= inhabitants(Type, Int)
    rule inhabitants(T, FreshInt)
      => #if T ==K int    #then ?_:Int               #else
         #if T ==K bool   #then ?_:Bool              #else
         #if isMapType(T) #then map(FreshInt)        #else
         ?_:ValueExpr // TODO: Do we need something more structured?
         #fi #fi #fi
      [macro]
```

Update an variable to store an *unconstrained* sybmolic value of the appropriate
type.

TODO: Take types into account.

```k
    syntax KItem ::= freshen(IdList)
    rule <k> freshen(.IdList) => .K ... </k>
    rule <k> freshen(X, Xs)
          => X := inhabitants(Type, FreshInt) ;
          ~> freshen(Xs)
             ...
         </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> value(... type: Type) ... </store>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
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

Verification syntax
-------------------

```k
    syntax Id ::= "inc" [token] | "main" [token]
```

```k
endmodule
```
