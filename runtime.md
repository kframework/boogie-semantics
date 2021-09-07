```k
module BOOGIE-RUNTIME
    imports DEFAULT-CONFIGURATION
    imports BOOGIE-FRESH-COUNTER
    imports BOOGIE-PROCEDURES
    imports BOOGIE-TYPES
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-HELPERS
    imports MAP
    imports LIST
    imports INT
    imports ID
    imports STRING
    imports K-EQUAL
```

```verification
    configuration <runtime>
                    <locals> .Map </locals>
                    <globals> .Map </globals>
                    <olds> .Map </olds>
                    <labels> .Map </labels>
                    <cutpoints> .List </cutpoints>
                    <currentImpl multiplicity="?"> -1 </currentImpl>
                    <freshVars> .K </freshVars>
                  </runtime>
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
          ~> restoreLocals(Locals)
             ...
         </k>
         <locals> Locals </locals>
      requires isKResult(Vals)
```

```k
    syntax KItem ::= restoreLocals(Map)
    rule <k> (V:ValueExpr ~> restoreLocals(Locals)) => V ... </k>
         <locals> _ => Locals </locals>
```

### 4.3 Old expressions

```k
    rule <k> old(E) => E ~> restoreGlobals(Globals) ... </k>
         <globals> Globals => Olds </globals>
         <olds> Olds </olds>

    syntax KItem ::= restoreGlobals(Map)
    rule <k> E:ValueExpr ~> (restoreGlobals(Globals) => .K) ... </k>
         <globals> _ => Globals </globals>
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

9 Statements
------------

```k
   rule <k> S Ss:StmtList => S ~> Ss ... </k>
   rule <k> .StmtList => .K ... </k>
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
    rule #failure({ :procedure Procedure, Implementation, .AttrArgList } Attrs, Message)
      => #failure(Attrs, Message +String " " +String Id2String(Procedure) +String Int2String(Implementation))
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
    rule <k> (goto L, Ls ; ~> _) => (#pause ~> Stmts) </k>
         <labels> L |-> Stmts ... </labels>
    rule <k> goto L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .IdList
```

`#pause` is a hack used to reduce RAM usage by taking only one branch at a time (see driver.md)

```k
    syntax KItem ::= "#pause" [symbol, klabel(pause)]
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
    syntax KItem ::= "#return" ExprList
    rule <k> return ; ~> _
          => assert { :code "BP5003" } { :source "???", 0 } { :procedure CurrentProc, CurrentImpl }
                     (lambda IdsTypeWhereListToIdsTypeList(PArgs) ++IdsTypeList IdsTypeWhereListToIdsTypeList(PRets)
                          :: Ensures
                     ) [ IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets) ] ;
          ~> #return IdsTypeWhereListToExprList(IRets)
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
    rule <k> (#return Rets ~> K:K) => .K </k>
```

9.7 If statements
-----------------

9.8 While loops
---------------

9.9 Call statements
-------------------

```k
    rule <k> call ProcedureName:Id(ArgVals) ;
          => call .IdList := ProcedureName:Id(ArgVals) ;
             ...
         </k>
```

```verification
    context call X:IdList := ProcedureName:Id(HOLE) ;
    rule <k> call X:IdList := ProcedureName:Id(ArgVals) ;
          => assert { :code "BP5002" } { :source "???", 0 }
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
