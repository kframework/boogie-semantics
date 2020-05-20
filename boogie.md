Boogie Semantics
================

```k
requires "syntax.k"
requires "fresh-generator.k"

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports MAP
    imports INT
    imports FRESH-GENERATOR

    configuration <boogie>
                    <k> $PGM:Program ~> #start </k>
                    <env> .Map </env>
                    <store> .Map </store>
                    <labels> .Map </labels>
                    <procs>
                      <proc multiplicity="*" type="Set">
                        <signature> .K </signature>
                        <impls>
                          <impl multiplicity="*" type="Set">
                            .K
                          </impl>
                        </impls>
                      </proc>
                    </procs>
                    <exit-code exit=""> 1 </exit-code>
                    <freshCounter> 0 </freshCounter>
                  </boogie>
```

When the `<k>` cell is empty, the program succeeds.

```k
    rule <k> .K </k>
         <exit-code> 1 => 0 </exit-code>
```

```k
    rule <k> (D Decls):DeclList => D ~> Decls ... </k>
    rule <k> .DeclList => .K ... </k>
```

4 Expressions
-------------

```k
    syntax KResult ::= ValueExpr
                     | ValueList

    syntax ValueList ::= List{ValueExpr, ","} [klabel(ExprList)]
    syntax Expr ::= ValueExpr
    syntax ValueExpr ::= Bool | Int | String

    rule <k> X => V ... </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> V ... </store>

    context HOLE _:RelOp RHS
    context LHS:ValueExpr _:RelOp HOLE

    rule <k> LHS:ValueExpr == RHS:ValueExpr => LHS ==K RHS ... </k>
    rule <k> LHS:ValueExpr != RHS:ValueExpr => LHS =/=K RHS ... </k>

    rule <k> LHS <  RHS => LHS  <Int RHS ... </k>
    rule <k> LHS >  RHS => LHS  >Int RHS ... </k>
    rule <k> LHS <= RHS => LHS <=Int RHS ... </k>
    rule <k> LHS >= RHS => LHS >=Int RHS ... </k>

    context HOLE _:AddOp E2
    context V1:ValueExpr _:AddOp HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
    rule <k> V1 - V2 => V1 -Int V2 ... </k>

    context HOLE _:MulOp E2
    context V1:ValueExpr _:MulOp HOLE
    rule <k> V1 * V2 => V1 *Int V2 ... </k>

    context HOLE || E2
    rule <k> true  || RHS => true  ... </k>
    rule <k> false || RHS => RHS   ... </k>

    context HOLE && E2
    rule <k> true  && RHS => RHS   ... </k>
    rule <k> false && RHS => false ... </k>

    context _:UnOp HOLE
    rule <k> ! B => notBool(B) ... </k>
```

8 Procedures and implementations
--------------------------------

```k
    rule <k> (procedure Attrs:AttributeList
                ProcedureName .Nothing ( Args ) returns ( Rets ) SpecList
                { VarList StmtList }):Decl
          => procedure Attrs:AttributeList
               ProcedureName .Nothing ( Args ) returns ( Rets ) ; SpecList
          ~> implementation Attrs ProcedureName .Nothing ( Args ) returns ( Rets )
               { VarList StmtList }
             ...
         </k>

    rule <k> procedure Attrs:AttributeList
                ProcedureName .Nothing ( Args ) returns ( Rets ) ;
                  ( .SpecList
                 => .Nothing requires true ;
                    .Nothing ensures  true ;
                    .SpecList
                  )
             ...
         </k>

    rule <k> procedure Attrs:AttributeList
                ProcedureName .Nothing ( Args ) returns ( Rets ) ;
                    .Nothing requires Requires ;
                    .Nothing ensures  Ensures ;
          => .K
             ...
         </k>
         <procs> .Bag =>
           <proc>
             <signature>
               procedure Attrs:AttributeList
                 ProcedureName .Nothing ( Args ) returns ( Rets ) ;
                    .Nothing requires Requires ;
                    .Nothing ensures  Ensures ;
             </signature>
             ...
           </proc>
           ...
         </procs>

    rule <k> implementation Attrs:AttributeList ProcedureName .Nothing ( Args ) returns ( Rets )
                { VarList StmtList }
         => .K
            ...
         </k>
         <procs>
          <proc>
            <signature>
              procedure _:AttributeList ProcedureName _:PSig ; _:SpecList
            </signature>
            <impls>
              .Bag => <impl>
                implementation Attrs:AttributeList ProcedureName .Nothing ( Args ) returns ( Rets )
                { VarList StmtList } </impl>
              ...
            </impls>
          </proc>
          ...
         </procs>
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
    syntax Id ::= "$start"  [token]
                | "$return" [token]
    rule <k> #start
          => makeDecls(IArgs)
          ~> makeDecls(IRets)
          ~> assume Attrs Requires;
          ~> VarList
          ~> $start:
               transform(.Map, StmtList , .FreshGenerator ) ++StmtList
               goto $return;
             $return :
               assert { :code "BP5003" } { :source 0 } Ensures ;
             .StmtList
           ~> goto $start;
         </k>
         <impls>
           <impl>
               implementation Attrs:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets )
               { VarList StmtList }
           </impl>
          ...
         </impls>
        <signature>
          procedure _:AttributeList ProcedureName .Nothing ( PArgs ) returns ( PRets ) ;
            .Nothing requires Requires ;
            .Nothing ensures Ensures ;
            .SpecList
        </signature>
      requires PArgs ==K IArgs andBool PRets ==K IRets
      // TODO: `hook(SUBSTITUTION.substMany)` is not supported on the Haskell backend
```

```k
   rule <k> V Vs:LocalVarDeclList => V ~> Vs ... </k>
   rule <k> .LocalVarDeclList => .K ... </k>

   rule <k> (var .AttributeList X:Id : T ;):LocalVarDecl => .K ... </k>
        <env> (.Map => X:Id |-> Loc) Rho </env>
        <store> (.Map => Loc:Int |-> ?_:Int) ... </store>
        <freshCounter> Loc  => Loc  +Int 1 </freshCounter>
     requires notBool( X in_keys(Rho) )
```

9.2 Assertions and assumptions
------------------------------

```k
    syntax KItem ::= "#failure" "(" String ")"
    syntax KItem ::= "#failure" "(" AttributeList "," String ")"
    syntax Id ::= "source" [token]
    rule #failure( { : source File, Line, .AttrArgList }, Message )
      => #failure(File +String "(" +String Int2String(Line) +String "): " +String Message)
```

```k
    context assert Attributes HOLE ;
    rule <k> assert Attributes true ; => .K ... </k>
    rule <k> (.K => #failure(Attributes, "Error BP5001: This assertion might not hold."))
          ~> assert Attributes false;
             ...
         </k>
```

```k
    context assume .AttributeList HOLE ;
    rule <k> assume .AttributeList true ;      => .K ... </k>
    rule <k> assume .AttributeList false; ~> K => .K </k>
         <store> _ => .Map </store>
```

9.3 Assignments
---------------

TODO: This needs to work over lists of expressions and identifiers

```k
    context X := HOLE ;
    rule <k> X := V:ValueExpr ; => .K ... </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> (_ => V) Rho </store>
```

9.4 Havoc
---------

Desugaring a list of Ids to seperate havoc statements seems like a sensible
desugaring, but the spec is not clear if this is semantically equivalent.
TODO: verify this is legit.
TODO add assume statements corresponding to the where clause in X's declaration.

```k
    rule <k> havoc X ; => freshen(X) ... </k>
```

9.5 Label Statements and jumps
------------------------------

TODO: "This is Boogie 2" is extremely unclear about what happens here.
This is best-effort attempt to translate their definition.

```k
    syntax StmtList ::= transform(nu: Map, stmts: StmtList, freshCounter: FreshGenerator)
      [function, functional]
    rule transform(Nu, S Ss:StmtList, FreshGenerator)
      => transform(Nu, S,  next(FreshGenerator, 0)) ++StmtList
         transform(Nu, Ss, next(FreshGenerator, 1))
    rule transform(_, .StmtList, _) => .StmtList

    syntax StmtList ::= transform(nu: Map, stmt: LabelOrStmt, freshCounter: FreshGenerator)
      [function, functional]
    rule transform(Nu:Map, lstmt(L:, S), FreshGenerator)
      => ( goto L;
           L: transform( (Nu (L |-> id("Done", FreshGenerator)))
                       , S
                       , next(FreshGenerator, 1)
                       )
         )
         ++StmtList
         goto id("Done", FreshGenerator) ;
         id("Done", FreshGenerator)  :
         .StmtList
    rule transform(Nu, S:SimpleStmt, FreshGenerator)
      => S .StmtList
    rule transform(Nu, goto Ls;, FreshGenerator)
      => goto Ls;
         id("Unreachable", FreshGenerator) :
         .StmtList
```

```k
    syntax KItem ::= #collectLabel(Id, StmtList)
    rule <k> Id:  => #collectLabel(Id, .StmtList) ... </k>
    rule <k> (#collectLabel(L, S1s) ~> S2:Stmt S2s:StmtList)
          => (#collectLabel(L, S1s ++StmtList S2 .StmtList) ~> S2s)
             ...
         </k>
    rule <k> (#collectLabel(L, S1s) => .K)
          ~> (L2: S2 S2s:StmtList) #Or .StmtList
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

9.6 Return statements
---------------------

```k
    rule transform(Nu, return;, FreshGenerator)
      => goto $return ;
         id("Unreachable", FreshGenerator) :
         .StmtList
```

9.7 If statements
-----------------

While not in the grammar, the implementations of `if` and `while` statements
benefit from the following:

```k
    syntax Stmt ::= Else
    rule transform(Nu, { Ss }, FreshGenerator)
      => transform(Nu,   Ss,   FreshGenerator)
```

```k
    rule transform(Nu, if (E) THEN, FreshGenerator)
      => transform(Nu, if (E) THEN else { .StmtList }, FreshGenerator)

    rule transform(Nu, if (E) THEN else ELSE , FreshGenerator)
      => goto id("then", FreshGenerator), id("else", FreshGenerator);
         id("then", FreshGenerator):
            assume .AttributeList E;
            transform(Nu, THEN, next(FreshGenerator, 0)) ++StmtList
         (  goto id("Done", FreshGenerator);
         id("else", FreshGenerator):
            assume .AttributeList ! E;
            transform(Nu, ELSE, next(FreshGenerator, 1)) ) ++StmtList
            goto id("Done", FreshGenerator);
         id("Done", FreshGenerator):
         .StmtList
```

```k
    rule transform(Nu, if (*) THEN else ELSE , FreshGenerator)
      => goto id("then", FreshGenerator), id("else", FreshGenerator);
         id("then", FreshGenerator):
            transform(Nu, THEN, next(FreshGenerator, 0)) ++StmtList
         (  goto id("Done", FreshGenerator);
         id("else", FreshGenerator):
            transform(Nu, ELSE, next(FreshGenerator, 1)) ) ++StmtList
            goto id("Done", FreshGenerator);
         id("Done", FreshGenerator):
         .StmtList
```

9.8 While loops
---------------

```k
    rule transform(Nu, while (E) Invariants { Body }, FreshGenerator)
      => goto id("Head", FreshGenerator);
         id("Head", FreshGenerator):
            transformInvariants(Invariants) ++StmtList
         (  goto id("Body", FreshGenerator), id("GuardedDone", FreshGenerator) ;
         id("Body", FreshGenerator):
            assume .AttributeList E;
            transform( Nu[ "*" <- id("Done", FreshGenerator)]
                     , Body
                     , next(FreshGenerator, 0)
                     ) ) ++StmtList
            goto id("Head", FreshGenerator) ;
         id("GuardedDone", FreshGenerator):
            assume .AttributeList ! E;
            goto id("Done", FreshGenerator) ;
         id("Done", FreshGenerator):
         .StmtList
```

```k
    rule transform(Nu, while (*) Invariants { Body }, FreshGenerator)
      => goto id("Head", FreshGenerator);
         id("Head", FreshGenerator):
            transformInvariants(Invariants) ++StmtList
         (  goto id("Body", FreshGenerator), id("Done", FreshGenerator) ;
         id("Body", FreshGenerator):
            transform( Nu[ "*" <- id("Done", FreshGenerator)]
                     , Body
                     , next(FreshGenerator, 0)
                     ) ) ++StmtList
            goto id("Head", FreshGenerator) ;
         id("Done", FreshGenerator):
         .StmtList
```

```k
    syntax StmtList ::= transformInvariants(LoopInvList) [function, functional]
    rule transformInvariants(.LoopInvList) => .StmtList
    rule transformInvariants(invariant Attrs E; Invs)
      => assert Attrs E; transformInvariants(Invs)
    rule transformInvariants(free invariant Attrs E; Invs)
      => assume Attrs E; transformInvariants(Invs)
```

9.9 Call statements
-------------------

```k
    rule <k> call X:Id := ProcedureName:Id(ArgVals) ;
          => assert .AttributeList Requires ;
          ~> freshen(X)
          ~> assume .AttributeList Ensures ;
             ...
         </k>
         <signature>
           procedure Attrs:AttributeList
             ProcedureName .Nothing ( Args ) returns ( Rets ) ;
                .Nothing requires Requires ;
                .Nothing ensures Ensures ;
         </signature>
```

Helpers
-------

Update an variable to store an *unconstrained* sybmolic value of the appropriate
type.

TODO: Take types into account.

```k
    syntax KItem ::= freshen(IdList)
    rule <k> freshen(.IdList) => .K ... </k>
    rule <k> freshen(X, Xs) => X := ?V:Int ; ~> freshen(Xs) ... </k>
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

Verification syntax
-------------------

```k
    syntax Id ::= "inc" [token] | "main" [token]
```

```k
endmodule
```
