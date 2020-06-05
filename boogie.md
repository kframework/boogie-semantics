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
                    <cutpoints> .List </cutpoints>
                    <currentProc multiplicity="?"> main </currentProc>
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

Split procedures with a body into a procedure and an implementation:

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
```

```k
    rule <k> procedure Attrs:AttributeList ProcedureName .Nothing ( Args ) .Nothing ; SpecList
          => procedure Attrs:AttributeList ProcedureName .Nothing ( Args ) returns (.IdsTypeWhereList) ; SpecList
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
```

```k
    rule <k> implementation Attrs:AttributeList ProcedureName .Nothing ( Args ) (.Nothing => returns (.IdsTypeWhereList)) { VarList StmtList }
             ...
         </k>
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
    rule <k> #start
          => makeDecls(IArgs)
          ~> makeDecls(IRets)
          ~> assume Attrs Requires;
          ~> VarList
          ~> StartLabel: StmtList
          ~> goto StartLabel;
         </k>
         (.Bag => <currentProc> ProcedureName </currentProc>)
         <impls>
           <impl>
               implementation Attrs:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets )
               { VarList StartLabel: StmtList }
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
    syntax KItem ::= "#failure" "(" String ")" [klabel(#failure), symbol]
    syntax KItem ::= "#failure" "(" AttributeList "," String ")"
    syntax Id ::= "source" [token] | "code"   [token]
    rule #failure(.AttributeList, Message)
      => #failure(Message)
    rule #failure({ :source Line, .AttrArgList } Attrs, Message)
      => #failure(Attrs, "??.bpl(" +String Int2String(Line) +String ",00): " +String Message)
    rule #failure({ :code Code, .AttrArgList } Attrs, Message)
      => #failure(Attrs, Message +String "Error " +String Code +String ": ")
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

### Extension: Cutpoints

We use `boogie` to infer invaraints and cutpoints.
Boogie marks labels that are cutpoints with the comment `// cut point`.
We preprocess this comment into a `Stmt` "`cutpoint;`" that we handle.

Boogie does not place the `cutpoint` mark, the inferred invariants and
the loop invariant assertsions in the right order.
The following code rearranges them into an order that makes more sense for us.

We also need to be able to distinguish between different cutpoints.
Ideally, \K would mark this with source line information but it does not.
So we mark them with fresh integers in this preprocessing pass.

```k
    syntax Id ::= "inferred" [token]
    rule <k> #collectLabel(L, S1s)
          ~> ( ( cutpoint;
                 assume { :inferred .AttrArgList } Inferred;
                 assert .AttributeList Invariant ;
                 S2s:StmtList
               )
            => ( assert { :code "Inferred" } { :source 0 } Inferred; // This should never fail
                 assert { :code "BPInvariant" } { :source 0 } Invariant;
                 cutpoint(!_:Int) ;
                 assume { :inferred .AttrArgList } Inferred;
                 assume .AttributeList Invariant;
                 S2s:StmtList
             ) )
             ...
         </k>
```

When we reach a paticular cutpoint the first time, we treat it as an abstraction point
and replace all values in the `<store>` with fresh symbolic values.

```k
    syntax Stmt ::= "cutpoint" "(" Int ")" ";"
    rule <k> cutpoint(I) ; => #abstract(Rho) ... </k>
         <env> Rho </env>
         <cutpoints> (.List => ListItem(I)) Cutpoints </cutpoints>
      requires notBool I in Cutpoints

    rule <k> cutpoint(I) ; => assume .AttributeList (false); ... </k>
         <cutpoints> Cutpoints </cutpoints>
      requires I in Cutpoints

    syntax KItem ::= "#abstract" "(" Map ")"
    rule <k> #abstract(.Map) => .K ... </k>
    rule <k> #abstract((X:Id |-> Loc) Rho) => freshen(X) ... </k>
```

9.6 Return statements
---------------------

```k
    rule <k> return ; ~> _
          => assert { :code "BP5003" } { :source 0 } Ensures ;
         </k>
         <currentProc> CurrentProc </currentProc>
         <signature> procedure _:AttributeList ProcedureName _ ( _ ) _ ;
                        .Nothing requires _ ;
                        .Nothing ensures Ensures ;
         </signature>
```

9.7 If statements
-----------------

9.8 While loops
---------------

9.9 Call statements
-------------------

```k
    rule <k> call X:Id := ProcedureName:Id(ArgVals) ;
          => assert { :code "BPRequires" } { :source 0 } Requires ;
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
