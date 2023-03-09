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
    imports K-LOCATIONS

    configuration <boogie>
                    <k> #initTypes ~> $PGM:Program ~> .DeclList ~> #start </k>
                    <preprocess multiplicity="?">
                        <pp> .K </pp>
                        <ppCurrImpl> -1 </ppCurrImpl>
                        <currLabel> .Nothing:OptionalLabel </currLabel>
                        <currBlock> .StmtList </currBlock>
                        <loopStack> .ExprList </loopStack>
                    </preprocess>
                    <types>
                      <type multiplicity="*" type="Map">
                          <typeName> #token("TypeName", "Id"):Type </typeName>
                          <synonym multiplicity="?">  #token("TypeName", "Id"):Type </synonym>
                          <uniques> .IdList </uniques>
                      </type>
                    </types>
                    <runtime>
                      <globals> .Map </globals>
                      <stack>
                      <stackFrame multiplicity="*" type="List">
                        <currImpl> -1 </currImpl>
                        <locals> .Map </locals>
                        <olds> .Map </olds>
                        <continuation> .K </continuation>
                      </stackFrame>
                      </stack>
                    </runtime>
                    <procs>
                      <proc multiplicity="*" type="Map">
                        <procName> #token("ProcedureName", "Id") </procName>
                        <args> .IdsTypeWhereList </args>
                        <returns> .IdsTypeWhereList </returns>
                        <requires> true:Expr </requires>
                        <freeRequires> true:Expr </freeRequires>
                        <ensures> true:Expr </ensures>
                        <freeEnsures> true:Expr </freeEnsures>
                        <modifies> .IdList </modifies>
                        <impls>
                          <impl multiplicity="*" type="Map">
                            <implId> -1 </implId>
                            <labels> .Map </labels>
                            <iargs> .IdsTypeWhereList </iargs>
                            <ireturns> .IdsTypeWhereList </ireturns>
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
    rule <k> const _:AttributeList .Nothing X, .IdList : T ; => .K ... </k>
         <globals> (.Map => X:Id |-> value(#undefined, T, true)) Rho </globals>
       requires notBool(X in_keys(Rho))
```

If a constant is marked "unique" it is assumed distinct from all other constants of that type:

```k
    rule <k> const _:AttributeList (unique => .Nothing)  X:Id : T ;
          ~> (.K => assume .AttributeList #distinct(X, Uniques) ;)
             ...
         </k>
         <typeName> T </typeName>
         <uniques> Uniques => X, Uniques </uniques>
    syntax Expr ::= #distinct(Id, IdList)
    // TODO: Should be `#distinct(Expr, ExprList)`; blocked on https://github.com/kframework/kore/issues/1817
    rule <k> #distinct(L, (R, Rs)) => L != R && #distinct(L, Rs) ... </k>
    rule <k> #distinct(_, .IdList) => true ... </k>
```


Functions desugar to lambdas:

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

4 Expressions
-------------

```k
    syntax KResult ::= ValueExpr
    syntax Expr ::= ValueExpr
    syntax ValueExpr ::= FreshValue
    rule isKResult(E, Es:ExprList) => isKResult(E) andBool isKResult(Es)
    rule isKResult(.ExprList) => true
    syntax FreshValue ::= Bool | Int | String
    context <k> HOLE , _:ExprList ... </k>
    context <k> _:ValueExpr , HOLE:ExprList ... </k>

    rule <k> X:Id => value(lookupVariable(X)) ... </k>

    context HOLE _:RelOp _RHS
    context _LHS:ValueExpr _:RelOp HOLE

    rule <k> LHS == RHS => LHS ==Int  RHS ... </k>
    rule <k> LHS != RHS => LHS =/=Int RHS ... </k>
    rule <k> LHS <  RHS => LHS  <Int  RHS ... </k>
    rule <k> LHS >  RHS => LHS  >Int  RHS ... </k>
    rule <k> LHS <= RHS => LHS <=Int  RHS ... </k>
    rule <k> LHS >= RHS => LHS >=Int  RHS ... </k>

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

In certain conditions the value of a variable may be undefined, e.g when
uninitiallized, or after the `havoc` call.
For the sake of concrete execution, we currently assume some default value.

```k
    syntax ValueExpr ::= "#undefined" [macro]
    rule #undefined => 0
```

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
    rule <k> _:ValueExpr ~> (#restoreLocals(Locals) => .K) ... </k>
         <locals> _ => Locals </locals>
```

### 4.3 Old expressions

```k
    rule <k> old(E) => E ~> #restoreGlobals(Globals) ... </k>
         <globals> Globals => Olds </globals>
         <olds> Olds </olds>

    syntax KItem ::= "#restoreGlobals" "(" Map ")"
    rule <k> _:ValueExpr ~> (#restoreGlobals(Globals) => .K) ... </k>
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

  rule <k> var .AttributeList X:Id : T:Type ;:Decl => .K ... </k>
       <globals> (.Map => X:Id |-> value(#undefined, T, true)) Rho </globals>
     requires notBool( X in_keys(Rho) )
```

8 Procedures and implementations
--------------------------------

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
    syntax KItem ::= "#populateProcedure" "(" Id "," SpecList ")"
    rule <k> procedure _:AttributeList ProcedureName _TypeArgs ( Args ) returns ( Rets ) ; SpecList
          => #populateProcedure(ProcedureName, SpecList) ... </k>
         <procs> .Bag =>
           <proc>
             <procName> ProcedureName </procName>
             <args> Args </args>
             <returns> Rets </returns>
             ...
           </proc>
           ...
         </procs>

    rule <k> #populateProcedure(ProcedureName, .Nothing requires NewReq ; SpecList => SpecList) ... </k>
         <procName> ProcedureName </procName>
         <requires> Reqs => Reqs && NewReq </requires>
    rule <k> #populateProcedure(ProcedureName, free requires NewRequires ; SpecList => SpecList) ... </k>
         <procName> ProcedureName </procName>
         <freeRequires> Requires => Requires && NewRequires </freeRequires>

    rule <k> #populateProcedure(ProcedureName, .Nothing ensures NewEnsures ; SpecList => SpecList) ... </k>
         <procName> ProcedureName </procName>
         <ensures> Ensures => Ensures && NewEnsures </ensures>
    rule <k> #populateProcedure(ProcedureName, free ensures NewEnsures ; SpecList => SpecList) ... </k>
         <procName> ProcedureName </procName>
         <freeEnsures> Ensures => Ensures && NewEnsures </freeEnsures>

    rule <k> #populateProcedure(ProcedureName,  modifies Modifies ; SpecList => SpecList) ... </k>
         <procName> ProcedureName </procName>
         <modifies> .IdList => Modifies </modifies>

    rule <k> #populateProcedure(_, .SpecList) => .K ... </k>
```

```k
    rule <k> implementation _:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets ) { VarDeclList StmtList }
          => #preprocess
             ...
         </k>
         <procName> ProcedureName </procName>
         <impls> .Bag
              => <impl>
                   <implId> !N:Int </implId>
                   <iargs> IArgs </iargs>
                   <ireturns> IRets </ireturns>
                   <vars> VarDeclList </vars>
                   <labels> .Map </labels>
                 </impl>
                 ...
         </impls>
         (.PreprocessCell =>
           <preprocess> <pp> #addStartLabel(StmtList) </pp> <ppCurrImpl> !N:Int </ppCurrImpl> ... </preprocess>)
```


Location Information
--------------------

Assertions are annotated with their location information:

```k
    rule <pp> #location(assert _ Expr  ;, File, Line, Col, _, _)
           => #assert {File, Line, Col} Expr ;
              ...
         </pp> [priority(51)]
```

Using `OptionalFree` at the begining of a production in the main syntax messes up line numbering.

```k
    rule <pp> #location(     call Ids := ProcId(Args);, File, Line, Col, _, _) => (IdListToLhsList(Ids)  := #call {File,Line,Col} .Nothing ProcId(Args);):Stmt ... </pp>
    rule <pp> #location(free call Ids := ProcId(Args);, File, Line, Col, _, _) => (IdListToLhsList(Ids)  := #call {File,Line,Col} free     ProcId(Args);):Stmt ... </pp>
    rule <pp> #location(     call        ProcId(Args);, File, Line, Col, _, _) => .LhsList               := #call {File,Line,Col} .Nothing ProcId(Args);       ... </pp>
    rule <pp> #location(free call        ProcId(Args);, File, Line, Col, _, _) => .LhsList               := #call {File,Line,Col} free     ProcId(Args);       ... </pp>
```

```k
    rule <pp> #location(return ;, File, Line, Col, _, _) => #return {File, Line, Col} ; ... </pp>
```

Other statements don't need location information:

```k
    rule <pp> #location(Stmt, _File, _StartLine, _StartCol, _EndLine, _EndCol) => Stmt:Stmt ... </pp> [priority(52)]
```


Preprocessing
-------------

### Converting complex control structures to `goto`s

`#preprocess` splits an implementation body into labeled blocks,
populates the `<labels>` cell with a map from labels to their bodies.
It also desugars `while` loops and `if` statements into `goto` statements.

```k
    syntax KItem ::= "#preprocess"
```

First, we ensure that the label `$start` is the initial label.
If the implementation body already has an initial label, the synthesised `$start` label
redirects to that one. Otherwise, we insert it as a new label.

```k
    syntax Id ::= "$start" [token]
    syntax StmtList ::= #addStartLabel(StmtList) [function, total]
    rule #addStartLabel((Label : _):StmtList #as Ss) => $start: goto Label; Ss
    rule #addStartLabel((_:Stmt _):StmtList  #as Ss) => $start:             Ss
    rule #addStartLabel((.StmtList):StmtList #as Ss) => $start:             Ss
```

Next, we preprocess each statement one at a time.

```k
    rule <pp> Stmt Stmts:StmtList => Stmt ~> Stmts ... </pp>
    rule <pp> .StmtList => .K ... </pp>
    rule (<preprocess> <pp> .K </pp> <currLabel> .Nothing </currLabel> ... </preprocess> => .PreprocessCell)
         <k> #preprocess => .K ... </k>
```

Most statements need no processing, and we simply accumulate the statements in `<currBlock>`:

```k
    rule <pp> S:Stmt => .K ... </pp>
         <currBlock> Ss => Ss ++StmtList S </currBlock> [owise]
```

`if` statements are desugared to `goto` statements.
Note that `if (*)` desugars to a non-deterministic `goto`.

```k
    syntax Label ::= done(Int)
    syntax Label ::= condTrue(Int) | condFalse(Int)
    rule if (_) _ (.Nothing => else { .StmtList }) [anywhere]
    rule if (_) _ else (if (_) _ _ #as Else => { Else .StmtList }) [anywhere]
    rule <pp> if (*) { BlockTrue } else { BlockFalse }
           => goto condTrue(!I:Int), condFalse(!I:Int);
              condTrue (!I): BlockTrue  ~> goto done(!I);
              condFalse(!I): BlockFalse ~> goto done(!I); ~>
              #popLoopLabel ~>
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>

    rule <pp> if (Cond) { BlockTrue } else { BlockFalse }
           => goto condTrue(!I:Int), condFalse(!I:Int);
              condTrue (!I): assume .AttributeList   Cond; BlockTrue  ~> goto done(!I);
              condFalse(!I): assume .AttributeList ! Cond; BlockFalse ~> goto done(!I); ~>
              #popLoopLabel ~>
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>
```

Similarly, `while` loops desugar to a more complex set of `goto` statements.
At the same time, we store the loop identifier in a stack so that break and
continue statements are aware of which loop to break out of.

```k
    syntax Label ::= loopHead(Int) | loopBody(Int) | guardedDone(Int)
    rule <pp> while (*) Invariants { Body }
           => goto loopHead(!I:Int);
              loopHead(!I): ~>
                LoopInvariantListToStmtList(Invariants) ~>
                goto loopBody(!I), done(!I); ~>
              loopBody(!I): ~>
                Body ~> goto loopHead(!I);
              done(!I) :
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>
    rule <pp> while (Cond) Invariants { Body }
           => goto loopHead(!I:Int);
              loopHead(!I): ~>
                LoopInvariantListToStmtList(Invariants) ~>
                goto loopBody(!I), guardedDone(!I); ~>
              loopBody(!I): ~>
                assume .AttributeList Cond ; ~>
                Body ~> goto loopHead(!I);
              guardedDone(!I):
                assume .AttributeList ! Cond ; goto done(!I); ~>
              #popLoopLabel ~>
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>
```

```k
    syntax StmtList ::= LoopInvariantListToStmtList(LoopInvariantList) [function]
    rule LoopInvariantListToStmtList(.LoopInvariantList) => .StmtList
    rule LoopInvariantListToStmtList(#location(     invariant _  Expr;,  File,  Line,  Col, _, _) Rest)
      => #assert {File, Line, Col} Expr ; LoopInvariantListToStmtList(Rest)
    rule LoopInvariantListToStmtList(#location(free invariant _ _Expr;, _File, _Line, _Col, _, _) Rest)
      => LoopInvariantListToStmtList(Rest)
```

We may then use that stack when desugaring break statements.

```k
    rule <pp> break ; => goto done(I); ... </pp>
         <loopStack> I, _Stack </loopStack>
```

Finally, when the done statement for the while loop is reached, we pop it
from the stack.

```k
    syntax KItem ::= "#popLoopLabel"
    rule <pp> #popLoopLabel => .K ... </pp>
         <loopStack> _I, Stack => Stack </loopStack>
```

When we encounter a new label or reach the end of the body, we must finalize the previous block.

```k
    syntax KItem ::= "#finalizeBlock"
    rule <pp> (.K => #location(return;, "boogie.md", 0, 0, 0, 0) ~> #finalizeBlock) ~>  _Label : ... </pp>
         <currLabel> _:Label </currLabel>
    rule <pp> (.K => #location(return;, "boogie.md", 0, 0, 0, 0) ~> #finalizeBlock) </pp>
         <currLabel> _:Label </currLabel>
    rule <pp> #finalizeBlock => .K ... </pp>
         <currLabel> CurrLabel => .Nothing </currLabel>
         <currBlock> CurrBlock </currBlock>
         <ppCurrImpl> ImplId </ppCurrImpl>
         <implId> ImplId </implId>
         <labels> (.Map => CurrLabel |-> CurrBlock)
                  _Labels
         </labels>
```

```k
    rule <pp> Label : => .K ... </pp>
         <currLabel> .Nothing => Label </currLabel>
         <currBlock> _ => .StmtList </currBlock>
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
        <locals> (.Map => X:Id |-> value(#undefined, T, Where)) Rho </locals>
     requires notBool( X in_keys(Rho) )

   rule <k> var .AttributeList X:Id, Xs : T where Where; Vs:LocalVarDeclList
         => var .AttributeList       Xs : T where Where; Vs
            ...
        </k>
        <locals> X |-> (_ => value(#undefined, T, Where)) ... </locals>

   rule <k> var .AttributeList .IdList : _T where _Where; Vs:LocalVarDeclList
         => Vs
            ...
        </k>
```

9.2 Assertions and assumptions
------------------------------

```k
    syntax Stmt ::= "#assert" Location Expr ";"
                  | "#assert" message: String Expr ";"
```

```k
    syntax String ::= #makeAssertionMessage(Location, errorCode: String, errorMessage: String) [function, total]
    rule #makeAssertionMessage({File, Line, Column}, Code, Message)
      => File +String "(" +String Int2String(Line) +String "," +String Int2String(Column) +String "): "
         +String "Error " +String Code +String ": " +String Message
```

```k
    rule <k> #assert Location Expr; =>
             #assert #makeAssertionMessage(Location, "BP5001", "This assertion might not hold.") Expr;
             ...
         </k>

    syntax KItem ::= "#failure" "(" String ")" [klabel(#failure), symbol]
    context  #assert _:String HOLE ;
    rule <k> #assert _:String true ; => .K ... </k>
    rule <k> #assert Message false ; => #failure(Message) ... </k>
```

```k
    context assume _ HOLE ;
    rule <k> assume _ true ; => .K      ... </k>
//    rule <k> assume _ false; => #Bottom ... </k>
    rule <k> assume _ false; ~> _:K => .K </k>
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
         <currImpl> CurrentImpl </currImpl>
         <implId> CurrentImpl </implId>
         <modifies> Modifies </modifies>
      requires notBool X in_keys(Env)
       andBool         X in Modifies

    rule <k> X, .LhsList := V:ValueExpr, .ExprList ; => .K ... </k>
         <locals> Env </locals>
         <globals> X |-> value(... value: _ => V) ... </globals>
      requires notBool X in_keys(Env)
```

9.5 Label Statements and jumps
------------------------------

Non-deterministically transition to all labels

```k
    rule <k> (goto L, _Ls ; ~> _) => (Stmts) </k>
         <labels> L |-> Stmts ... </labels>
         <currImpl> Impl </currImpl>
         <implId>      Impl </implId>
    rule <k> goto _L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .LabelList
```

9.6 Return statements
---------------------

When returning, we first `assert` that the post condition holds, and then pop the stack.

```k
    syntax Stmt ::= "#return" Location ";"
    rule <k> (#return Location ; ~> _:K)
          => #assert #makeAssertionMessage(Location, "BP5003", "A postcondition might not hold on this return path.")
                     (lambda IdsTypeWhereListToIdsTypeList(PArgs) ++IdsTypeList IdsTypeWhereListToIdsTypeList(PRets)
                          :: Ensures
                     ) [ IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets) ] ;
          ~> IdsTypeWhereListToExprList(IRets)
         </k>
         <currImpl> CurrentImpl </currImpl>
         <iargs> IArgs </iargs>
         <ireturns> IRets </ireturns>
         <implId> CurrentImpl </implId>
         <ensures> Ensures </ensures>
         <args> PArgs </args>
         <returns> PRets </returns>
```

```k
    rule <k> Ret:ExprList
          => Ret ~> Continuation
         </k>
         <stack> <stackFrame>
                   <continuation> Continuation </continuation>
                   ...
                 </stackFrame> => .Bag
                ...
         </stack>
      requires isKResult(Ret)
```

9.9 Call statements
-------------------

```k
    syntax AssignRhs ::= "#call" Location OptionalFree Id "(" ExprList ")"
```

```k
    context #call _Loc _OptFree _ProcedureName:Id(HOLE)
    rule <k> ( #call Location _OptFree ProcedureName:Id(ArgVals) ~> Continuation)
          => makeDecls(IArgs)
          ~> makeAssignments(IdsTypeWhereListToIdList(IArgs), ArgVals) // Declare input arguments
          ~> makeDecls(IRets)                                    // Declare output arguments
          ~> VarDeclList                                         // Declare locals

          // Requires clause are defined in terms of procedure args, and not the names used in the implementation body.
          // We use a lambda to do the renaming.
          ~> #assert #makeAssertionMessage(Location, "BP5002", "A precondition for this call might not hold.")
                     (lambda IdsTypeWhereListToIdsTypeList(PArgs) :: Requires && FreeRequires)[IdsTypeWhereListToExprList(IArgs)];
          ~> goto $start;
         </k>
         <stack> .Bag => <stackFrame>
                           <currImpl> N </currImpl>
                           <olds> Globals </olds>
                           <locals> .Map </locals>
                           <continuation> Continuation </continuation>
                         </stackFrame>
                ...
         </stack>
         <globals> Globals </globals>
         <proc>
           <procName> ProcedureName </procName>
           <args> PArgs </args>
           <requires> Requires </requires>
           <freeRequires> FreeRequires </freeRequires>
           <impl>
              <implId> N </implId>
              <iargs> IArgs </iargs>
              <ireturns> IRets </ireturns>
              <vars> VarDeclList </vars>
              ...
           </impl>
           ...
         </proc>
      requires isKResult(ArgVals)
```

At program start, we simply call main.

```k
    syntax KItem ::= "#start"
    syntax Id ::= "main" [token]
    rule <k> #start
          => #call {"boogie.md",0,0} .Nothing main(.ExprList)
             ...
         </k>
```

```k
endmodule
```
