```k
requires "syntax.k"

module BOOGIE
    imports BOOGIE-RULE-SYNTAX
    imports MAP

    configuration <k> $PGM:BoogieProgram </k>
                  <env>   .Map </env>
                  <store> .Map </store>
                  <labels> .Map </labels>
                  <exit-code exit=""> 1 </exit-code>
```

When the `<k>` cell is empty, the program succeeds.

```k
    rule <k> .K </k>
         <exit-code> 1 => 0 </exit-code>
```

```k
    rule <k> D Decls:Decls => D ~> Decls ... </k>
    rule <k> .Decls => .K ... </k>
```

4 Expressions
=============

```k
    syntax KResult ::= ValueExpr
    syntax AtomExpr ::= ValueExpr
    syntax ValueExpr ::= Bool | Int | String

    rule <k> X => V ... </k>
         <env> X |-> Loc ... </env>
         <store> Loc |-> V ... </store>

    context HOLE == RHS
    context LHS:ValueExpr == HOLE
    rule <k> LHS:ValueExpr == RHS:ValueExpr
          => LHS ==K RHS
             ...
         </k>

    context HOLE Op:AddOp E2
    context V1:ValueExpr Op:AddOp HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
```

9 Statements
============

```k
   rule <k> V Vs:LocalVarsList => V ~> Vs ... </k>
   rule <k> .LocalVarsList => .K ... </k>

   rule <k> S Ss:StmtList => S ~> Ss ... </k>
   rule <k> .StmtList => .K ... </k>
```

9.0 Implementation Body
-----------------------

For now, we assume that the program contains only a single procedure, called `main`.

```k
    syntax Id ::= "main" [token]
    syntax Id ::= "start" [token]
    rule <k> ( procedure
                  _:Attrs
                  main _:MaybeTypeParams ( .AttrTypedIdentsWheres )
                      returns ( .AttrTypedIdentsWheres ):ProcReturn
                      .Specs
                  { VarList StmtList }
             ):ProcDecl
          => VarList
          ~> start: ++StmtList transform(.Map, StmtList) ++StmtList return ;
          ~> goto start;
             ...
         </k>
```

```k
   rule <k> var .Attrs X:Ident : T ;:LocalVars => .K ... </k>
        <env> (.Map => X:Ident |-> !Loc) Rho </env>
        <store> (.Map => !Loc:Int |-> ?_:Int) ... </store>
     requires notBool( X in_keys(Rho) )
```

9.2 Assertions and assumptions
------------------------------

```k
    syntax KItem ::= "#success" | "#failure"
```

```k
    context assert .Attrs HOLE ;
    rule <k> assert .Attrs true ; => .K       ... </k>
    rule <k> assert .Attrs false; => #failure ... </k>
```

```k
    context assume .Attrs HOLE ;
    rule <k> assume .Attrs true ;      => .K ... </k>
    rule <k> assume .Attrs false; ~> K => #success </k>
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

TODO: This this is a stub.

```k
    syntax StmtList ::= transform(Map, StmtList) [function]
    rule transform(_, Ss) => Ss
```

```k
    syntax KItem ::= #collectLabel(Label, StmtList)
    rule <k> L:Label => #collectLabel(L, .StmtList) ... </k>
    rule <k> (#collectLabel(L, S1s) ~> S2 S2s)
          => (#collectLabel(L, S1s ++StmtList S2) ~> S2s)
             ...
         </k>
      requires notBool isLabel(S2)

    rule <k> (#collectLabel(L, S1s) => .K)
          ~> ( (_:Label _) #Or .StmtList )
             ...
         </k>
         <labels> (.Map => L |-> S1s) Labels </labels>
```

Non-deterministically transition to all labels

```k
   rule <k> goto L, Ls; => Stmts ... </k>
        <labels> L |-> Stmts ... </labels>
   rule <k> goto L, Ls; => goto Ls; ... </k>
   rule <k> goto .Idents; => .K ... </k>
```

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
