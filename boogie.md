```k
requires "syntax.k"

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports MAP
    imports INT
    imports ID

    configuration <k> $PGM:Program </k>
                  <env> .Map </env>
                  <store> .Map </store>
                  <labels> .Map </labels>
                  <exit-code exit=""> 1 </exit-code>
```

When the `<k>` cell is empty, the program succeeds.

```k
//    rule <k> .K </k>
//         <exit-code> 1 => 0 </exit-code>
```

```k
    rule <k> (D Decls):DeclList => D ~> Decls ... </k>
    rule <k> .DeclList => .K ... </k>
```

4 Expressions
=============

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
    rule <k> LHS < RHS => LHS <Int RHS ... </k>
    rule <k> LHS > RHS => LHS >Int RHS ... </k>

    context HOLE _:AddOp E2
    context V1:ValueExpr _:AddOp HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
    rule <k> V1 - V2 => V1 -Int V2 ... </k>

    context HOLE _:MulOp E2
    context V1:ValueExpr _:MulOp HOLE
    rule <k> V1 * V2 => V1 *Int V2 ... </k>
 context _:UnOp HOLE
    rule <k> ! B => notBool(B) ... </k>
```

9 Statements
============

```k
   rule <k> S Ss:StmtList => S ~> Ss ... </k>
   rule <k> .StmtList => .K ... </k>
```

9.0 Implementation Body
-----------------------

For now, we assume that the program contains only a single procedure, called `main`.

```k
    syntax Id ::= "main" [token]
    syntax Id ::= "start" [token]
    rule <k> procedure _:AttributeList
                main .Nothing ( .IdsTypeWhereList ) returns ( .IdsTypeWhereList ) .SpecList
                { VarList StmtList }
          => VarList
          ~> (start: transform(.Map, StmtList, !FreshCounter)) ++StmtList return ; .StmtList
          ~> goto start;
             ...
         </k>
```

```k
   rule <k> V Vs:LocalVarDeclList => V ~> Vs ... </k>
   rule <k> .LocalVarDeclList => .K ... </k>

   rule <k> (var .AttributeList X:Identifier : T ;):LocalVarDecl => .K ... </k>
        <env> (.Map => X:Identifier |-> !Loc) Rho </env>
        <store> (.Map => !Loc:Int |-> ?_:Int) ... </store>
     requires notBool( X in_keys(Rho) )
```

9.2 Assertions and assumptions
------------------------------

```k
    syntax KItem ::= "#success" | "#failure"
```

```k
    context assert .AttributeList HOLE ;
    rule <k> assert .AttributeList true ; => .K ... </k>
    rule <k> (.K => #failure) ~> assert .AttributeList false; ... </k>
```

```k
    context assume .AttributeList HOLE ;
    rule <k> assume .AttributeList true ;      => .K ... </k>
    rule <k> assume .AttributeList false; ~> K => #success </k>
```

9.3 Assignments
---------------

TODO: This needs to work over lists of expressions and identifiers

```k
    context X := HOLE ;
    rule <k> X := V ; => .K ... </k>
         <env> X |-> Loc ... </env>
         <store> Rho => Rho[ Loc <- V ] </store>
```

9.5 Label Statements and jumps
------------------------------

TODO: "This is Boogie 2" is extremely unclear about what happens here.
This is best-effort attempt to translate their definition.
TODO: Using fresh Ids in functions doesn't seem to work well in the Haskell
backend.

```k
    syntax StmtList ::= transform(nu: Map, stmts: StmtList, freshCounter: Int) [function]
    rule transform(Nu, S Ss:StmtList, FreshCounter)
      => transform(Nu, S, FreshCounter) ++StmtList
         transform(Nu, Ss, FreshCounter +Int 100) // TODO: This is a hack
    rule transform(_, .StmtList, _) => .StmtList

    syntax Identifier ::= label(String, Int)

    syntax StmtList ::= transform(nu: Map, stmt: LabelOrStmt, freshCounter: Int) [function]
    rule transform(Nu:Map, lstmt(L:, S), FreshCounter)
      => ( goto L;
           L: transform( (Nu (L |-> label("Done", FreshCounter)))
                       , S
                       , FreshCounter +Int 1
                       )
         )
         ++StmtList
         goto label("Done", FreshCounter) ;
         label("Done", FreshCounter)  :
         .StmtList
    rule transform(Nu, S:SimpleStmt, FreshCounter)
      => S .StmtList
    rule transform(Nu, goto Ls;, FreshCounter)
      => goto Ls;
         label("Unreachable", FreshCounter) :
         .StmtList
```

```k
    syntax KItem ::= #collectLabel(Identifier, StmtList)
    rule <k> Identifier:  => #collectLabel(Identifier, .StmtList) ... </k>
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
    rule <k> goto L, Ls ; => Stmts ... </k>
         <labels> L |-> Stmts ... </labels>
    rule <k> goto L, .IdList ; => Stmts ... </k>
         <labels> L |-> Stmts ... </labels>
```

9.6 Return statements
---------------------

```k
    rule <k> return ; ~> _ => .K </k>
```

9.7 If statements
-----------------

While not in the grammar, the implementations of `if` and `while` statements
benefit from the following:

```k
    syntax Stmt ::= Else
    rule transform(Nu, { Ss }, FreshCounter)
      => transform(Nu, Ss, FreshCounter)
```

```k
    rule transform(Nu, if (E) THEN, FreshCounter)
      => transform(Nu, if (E) THEN else { .StmtList }, FreshCounter)
      
    rule transform(Nu, if (E) THEN else ELSE , FreshCounter)
      => goto label("then", FreshCounter), label("else", FreshCounter);
         label("then", FreshCounter):
            assume .AttributeList E;
            transform(Nu, THEN, !FreshCounter) ++StmtList
         (  goto label("Done", FreshCounter);
         label("else", FreshCounter):
            assume .AttributeList ! E;
            transform(Nu, THEN, FreshCounter +Int 30) ) ++StmtList // TODO: Hack
            goto label("Done", FreshCounter);
         label("Done", FreshCounter):
         .StmtList
```

9.8 While loops
---------------

```k
    rule transform(Nu, while (E) Invariants { Body }, FreshCounter)
      => goto label("Head", FreshCounter);
         label("Head", FreshCounter):
            transformInvariants(Invariants) ++StmtList
         (  goto label("Body", FreshCounter), label("GuardedDone", FreshCounter) ;
         label("Body", FreshCounter):
            assume .AttributeList E;
            transform( Nu[ "*" <- label("Done", FreshCounter)]
                     , Body
                     , FreshCounter +Int 1
                     ) ) ++StmtList
            goto label("GuardedDone", FreshCounter) ;
         label("GuardedDone", FreshCounter):
            assume .AttributeList ! E;
            goto label("Done", FreshCounter) ;
         label("Done", FreshCounter):
         .StmtList

    syntax StmtList ::= transformInvariants(LoopInvList) [function]
    rule transformInvariants(.LoopInvList) => .StmtList
    rule transformInvariants(invariant Attrs E; Invs)
      => assert Attrs E; transformInvariants(Invs)
    rule transformInvariants(free invariant Attrs E; Invs)
      => assume Attrs E; transformInvariants(Invs)
```

Helper Functions
================

```k
    syntax StmtList ::= StmtList "++StmtList" StmtList [function, left, avoid]
    rule (S1 S1s) ++StmtList S2s => S1 (S1s ++StmtList S2s)
    rule .StmtList ++StmtList S2s => S2s
```

```k
endmodule
```
