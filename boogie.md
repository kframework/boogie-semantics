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

    context HOLE _:AddOp E2
    context V1:ValueExpr _:AddOp HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
    rule <k> V1 - V2 => V1 -Int V2 ... </k>
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
          ~> (start: transform(.Map, StmtList, !FreshCounter)) ++StmtList return ;
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
    syntax OptionalLabel ::= Nothing | Identifier
    syntax StmtList ::= transform(nu: Map, stmts: StmtList, freshCounter: Int) [function]
    rule transform(Nu, Ss, FreshCounter) => transform(Nu, .Nothing, Ss, FreshCounter)

    syntax Identifier ::= label(String, Int)

    syntax StmtList ::= transform(nu: Map, doneLabel: OptionalLabel, stmts: StmtList, freshCounter: Int) [function]
    rule transform(Nu, .Nothing, L: Ss, FreshCounter)
      => goto L;
         L: transform( (Nu L |-> label("Done", FreshCounter))
                     , label("Done", FreshCounter)
                     , Ss
                     , FreshCounter +Int 1
                     )
    rule transform(Nu, Done, L: Ss, FreshCounter)
      => goto Done;
         Done:
         transform(Nu, .Nothing, L: Ss, FreshCounter)
    rule transform(Nu, Done, .StmtList, FreshCounter)
      => goto Done;
         Done:
    rule transform(Nu, Done, S:SimpleStmt Ss, FreshCounter)
      => S transform(Nu, Done, Ss, FreshCounter)
    rule transform(Nu, Done, S:SimpleStmt Ss, FreshCounter)
      => S transform(Nu, Done, Ss, FreshCounter)
    rule transform(Nu, _, goto Ls; Ss, FreshCounter)
      => goto Ls;
         label("Unreachable", FreshCounter) :
            transform(Nu, Ss, FreshCounter +Int 1)

    rule transform(_, _, .StmtList, _) => .StmtList
```

```k
    syntax KItem ::= #collectLabel(Identifier, StmtList)
    rule <k> Identifier:  => #collectLabel(Identifier, .StmtList) ... </k>
    rule <k> (#collectLabel(L, S1s) ~> S2:Stmt S2s:StmtList)
          => (#collectLabel(L, S1s ++StmtList S2) ~> S2s)
             ...
         </k>
    rule <k> (#collectLabel(L, S1s) => .K)
          ~> (L2: S2s) #Or .StmtList
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

9.8 While loops
---------------

// ```k
//     rule transform(Nu, _, while (E) Invariants Body Ss, FreshCounter)
//       => goto label("Head", FreshCounter);
//          label("Head", FreshCounter):
//             transformInvariants(Invariants)
//             goto label("Body", FreshCounter), label("Done", FreshCounter) ;
//          label("Body", FreshCounter):
// ```

Helper Functions
================

```k
    syntax StmtList ::= StmtList "++StmtList" StmtList [function, left]
    rule (S1 S1s) ++StmtList S2s => S1 (S1s ++StmtList S2s)
    rule .StmtList ++StmtList S2s => S2s
```

```k
endmodule
```
