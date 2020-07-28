```k
module BOOGIE-RUNTIME
    imports syntax DEFAULT-CONFIGURATION
    imports syntax BOOGIE-FRESH-COUNTER
    imports syntax BOOGIE-PROCEDURES
    imports BOOGIE-RULE-SYNTAX
    imports BOOGIE-HELPERS
    imports MAP
    imports INT
    imports ID
    imports STRING
```

```k
    configuration <runtime>
                    <locals> .Map </locals>
                    <globals> .Map </globals>
                    <olds> .Map </olds>
                    <labels> .Map </labels>
                    <cutpoints> .List </cutpoints>
                    <currentImpl multiplicity="?"> -1 </currentImpl>
                  </runtime>
```

4 Expressions
-------------

```k
    syntax KResult ::= ValueExpr
    syntax Expr ::= ValueExpr
    rule isKResult(E, Es:ExprList) => isKResult(E) andBool isKResult(Es)
    rule isKResult(.ExprList) => true
    syntax ValueExpr ::= Bool | Int | String

    rule <k> X:Id => value(lookupVariable(X)) ... </k>

    context HOLE _:RelOp _RHS
    context _LHS:ValueExpr _:RelOp HOLE

    rule <k> LHS:ValueExpr == RHS:ValueExpr => LHS ==K RHS ... </k>
    rule <k> LHS:ValueExpr != RHS:ValueExpr => LHS =/=K RHS ... </k>

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

### Variable lookup

```k
    syntax Value ::= value(value: ValueExpr, type: Type, where: Expr)

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

### Lambdas

```k
    context _:LambdaExpr [ HOLE ]
    syntax ValueExpr ::= LambdaExpr
    rule <k> (lambda Bound :: Exp)[Vals]
          => makeDecls(IdsTypeListToIdsTypeWhereList(Bound))
          ~> makeAssignments(IdsTypeListToIdList(Bound), Vals)
          ~> restoreLocals(Exp, Locals)
             ...
         </k>
         <locals> Locals </locals>
      requires isKResult(Vals)
```

TODO: Done in this strange way because of https://github.com/kframework/kore/issues/2023

```k
    syntax KItem ::= restoreLocals(Expr, Map) [strict(1)]
    rule <k> restoreLocals(E:ValueExpr, Locals) => E ... </k>
         <locals> _ => Locals </locals>
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

TODO: HACK: WARNING: This is only sound when used in the context of a post condition.
It is unsound when used in an assume statement.
We alpha-rename the quantified variable with a fresh one.

```k
    rule <k> (#forall X : T :: Expr)
          => (lambda X : T :: Expr)[ inhabitants(T, FreshInt) ]
             ...
         </k>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
```

7 Mutable Variables, states, and execution traces
-------------------------------------------------

```k
  rule <k> var .AttributeList X:Id : T ;:Decl => .K ... </k>
       <globals> (.Map => X:Id |-> value(inhabitants(T, FreshInt), T, true)) Rho </globals>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
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
    rule <k> assume _ true ;      => .K ... </k>
    rule <k> assume _ false; ~> K => .K </k>
         <locals> _ => .Map </locals>
```

9.3 Assignments
---------------

TODO: This needs to work over lists of expressions and identifiers

```k
    context _X:Id := HOLE ;
    rule <k> X := V:ValueExpr ; => .K ... </k>
         <locals> X |-> value(... value: _ => V) ... </locals>

    rule <k> X := V:ValueExpr ; => .K ... </k>
         <locals> Env </locals>
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
          ~> assume .AttributeList where(lookupVariable(X)) ;
             ...
         </k>
```

Update an variable to store an *unconstrained* sybmolic value of the appropriate
type.

```k
    syntax KItem ::= freshen(IdList)
    rule <k> freshen(.IdList) => .K ... </k>
    rule <k> freshen(X, Xs)
          => X := inhabitants(type(lookupVariable(X)), FreshInt) ;
          ~> freshen(Xs)
             ...
         </k>
         <freshCounter> FreshInt => FreshInt +Int 1 </freshCounter>
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
invariants (inferred or annotated) before the cutpoint, replace local variables
and global variables with fresh symbolic values and finally `assume` the
invariants.

We also need to be able to distinguish between different cutpoints.
Ideally, \K would mark this with source line information but it does not.
So we mark them with fresh integers in this preprocessing pass.

```k
    syntax Id ::= "inferred" [token]
    rule <k> #collectLabel(_L, _S1s)
          ~> ( ( cutpoint;
                 assume { :inferred .AttrArgList } Inferred;
                 assert _:AttributeList Invariant ;
                 S2s:StmtList
               )
            => ( assert { :code "Inferred" } { :source "???", 0 } Inferred; // This should never fail
                 assert { :code "BP5004" } { :source "???", 0 } Invariant;
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
      requires assert _:AttributeList _ ; :/=K  S2
```

When we reach a particular cutpoint the first time, we treat it as an abstraction point
and replace modifiable variables with fresh symbolic values.

```k
    syntax Stmt ::= "cutpoint" "(" Int ")" ";"
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

```k
    rule <k> cutpoint(I) ; => assume .AttributeList (false); ... </k>
         <cutpoints> Cutpoints </cutpoints>
      requires I in Cutpoints
```

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

```k
    rule <k> return ; ~> _
          => assert { :code "BP5003" } { :source "???", 0 } { :procedure CurrentProc, CurrentImpl }
                     (lambda IdsTypeWhereListToIdsTypeList(PArgs) ++IdsTypeList IdsTypeWhereListToIdsTypeList(PRets)
                          :: Ensures
                     ) [ IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets) ] ;
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
    rule <k> call .Nothing ProcedureName:Id(ArgVals) ;
          => call .IdList := ProcedureName:Id(ArgVals) ;
             ...
         </k>

    rule <k> call X:IdList := ProcedureName:Id(ArgVals) ;
          => assert { :code "BP5002" } { :source "???", 0 }
               (lambda IdsTypeWhereListToIdsTypeList(Args) :: Requires)[ArgVals];
          ~> freshen(X)
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
```

Inhabitants
-----------

`inhabitants(T)` represents the inhabitants of a type.

Semantically, this is similar to matching logic's `[[ Sort ]]` (also pronounced
"inhabitants").

The Haskell backend does not allow `[anywhere]` rules (or equations) to use
existential variables. This *cannot* be a function. Functions must return a
single value, whereas here we return the set of all possible values of a type.
Hence, we use a macro.

TODO: Is there some more modular way we could implement this? This really
belongs where we define each data type.

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


```k
endmodule
```
