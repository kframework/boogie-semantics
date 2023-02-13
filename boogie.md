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
                    <preprocess multiplicity="?">
                        <pp> .K </pp>
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
                      <locals> .Map </locals>
                      <globals> .Map </globals>
                      <olds> .Map </olds>
                      <cutpoints> .List </cutpoints>
                      <currImpl multiplicity="?"> -1 </currImpl>
                      <freshVars> .K </freshVars>
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
    rule <k> const _:AttributeList .Nothing X, .IdList : T ; => X := inhabitants(T), .ExprList ; ... </k>
         <globals> (.Map => X:Id |-> value("undefined", T, true)) Rho </globals>
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
    rule <k> select(S, update(Key, Val, _Map)) => Val ...            </k> requires Key  ==K S
    rule <k> select(S, update(Key, _, Map))    => select(S, Map) ... </k> requires Key =/=K S

    rule <k> select(.ExprList,     map(Id, [_ArgT]RetT)) => intToT(RetT, lookupMap0(Id))                                              ... </k>
    rule <k> select(S,             map(Id, [_ArgT]RetT)) => intToT(RetT, lookupMap1(Id, TToInt(S)))                                   ... </k>
    rule <k> select((S1,S2),       map(Id, [_ArgT]RetT)) => intToT(RetT, lookupMap2(Id, TToInt(S1),TToInt(S2)))                       ... </k>
    rule <k> select((S1,S2,S3),    map(Id, [_ArgT]RetT)) => intToT(RetT, lookupMap3(Id, TToInt(S1),TToInt(S2),TToInt(S3)))            ... </k>
    rule <k> select((S1,S2,S3,S4), map(Id, [_ArgT]RetT)) => intToT(RetT, lookupMap4(Id, TToInt(S1),TToInt(S2),TToInt(S3),TToInt(S4))) ... </k>

    // Uninterpreted function
    syntax Int ::= lookupMap0(mapId: Int)                            [function, total, smtlib(lookupMap0), no-evaluators]
    syntax Int ::= lookupMap1(mapId: Int, keys: Int)                 [function, total, smtlib(lookupMap1), no-evaluators]
    syntax Int ::= lookupMap2(mapId: Int, keys: Int, Int)            [function, total, smtlib(lookupMap2), no-evaluators]
    syntax Int ::= lookupMap3(mapId: Int, keys: Int, Int, Int)       [function, total, smtlib(lookupMap3), no-evaluators]
    syntax Int ::= lookupMap4(mapId: Int, keys: Int, Int, Int, Int)  [function, total, smtlib(lookupMap4), no-evaluators]
```

#### Update

```k
    rule <k> X:Id [ Key ], .LhsList := Value, .ExprList ; => X := X [ Key := Value ], .ExprList ; ... </k>

    context HOLE [ _ := _ ]
    context _Map:MapValue [ HOLE := _Value ]
    context _Map:MapValue [ Key := HOLE ] requires isKResult(Key)
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

  rule <k> var .AttributeList X:Id : T:Type ;:Decl
        => X := inhabitants(T), .ExprList ;
           ...
       </k>
       <globals> (.Map => X:Id |-> value("undefined", T, true)) Rho </globals>
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
          (.CurrImplCell => <currImpl> !N:Int </currImpl>)
          (.PreprocessCell => <preprocess> <pp> #addStartLabel(StmtList) </pp> ... </preprocess> )
```

Preprocessing
-------------

### Location Information

```k
    syntax Stmt ::= #location(Stmt, String, Int, Int, Int, Int) [symbol, function]
```

```k
    syntax Id ::= "inferred" [token]
    syntax Stmt ::= "#cutpoint" LocationExprList ";"
    rule #location(assert { :inferred .AttrArgList } Inferred  ;, File, Line, Col, _, _)
      => #cutpoint { File, Line, Col } Inferred ;
```

Other assertions are simply annotated with their location information:

```k
    rule #location(assert _ Expr  ;, File, Line, Col, _, _)
      => #assert {File, Line, Col} Expr ; [priority(51)]
```

Using `OptionalFree` at the begining of a production in the main syntax messes up line numbering.

```k
    rule #location(     call CallLhs ProcId(Args);, File, Line, Col, _, _) => #call {File,Line,Col} .Nothing CallLhs  ProcId(Args);
    rule #location(free call CallLhs ProcId(Args);, File, Line, Col, _, _) => #call {File,Line,Col} free     CallLhs  ProcId(Args);
    rule #location(     call         ProcId(Args);, File, Line, Col, _, _) => #call {File,Line,Col} .Nothing .Nothing ProcId(Args);
    rule #location(free call         ProcId(Args);, File, Line, Col, _, _) => #call {File,Line,Col} free     .Nothing ProcId(Args);
```

```k
    rule #location(return ;, File, Line, Col, _, _) => #return {File, Line, Col} ;
```

Other statements don't need location information:

```k
    rule #location(Stmt, _File, _StartLine, _StartCol, _EndLine, _EndCol) => Stmt [priority(52)]
```

### Converting complex control structures to `goto`s

`#preprocess` splits an implementation body into labeled blocks,
populates the `<labels>` cell with a map from labels to their bodies.
It also desugars `while` loops and `if` statements into `goto` statements
and combines invariants into a cutpoints.

```k
    syntax KItem ::= "#preprocess"
```

Ensure that the label `$start` is the initial label.

```k
    syntax Id ::= "$start" [token]
    syntax StmtList ::= #addStartLabel(StmtList) [function, total]
    rule #addStartLabel((Label : _):StmtList #as Ss) => $start: goto Label; Ss
    rule #addStartLabel((_:Stmt _):StmtList  #as Ss) => $start:             Ss
    rule #addStartLabel((.StmtList):StmtList #as Ss) => $start:             Ss
```

We preprocess each statement one at a time, and finish preprocessing once all statements have been processed.

```k
    rule <pp> Stmt Stmts:StmtList => Stmt ~> Stmts ... </pp>
    rule <pp> .StmtList => .K ... </pp>
    rule (<preprocess> <pp> .K </pp> <currLabel> .Nothing </currLabel> ... </preprocess> => .PreprocessCell)
         (<currImpl> _ </currImpl> => .CurrImplCell)
         <k> #preprocess => .K ... </k>
```

Each cutpoint statement is given an numeric identifier allowing us to distinguish them.

```k
    syntax Stmt ::= "#cutpoint" "(" Int ")" LocationExprList ";"
    rule <pp> #cutpoint Invariants ; => #cutpoint(!_:Int) Invariants ; ... </pp>
```

Assertions immediately after a cutpoint are considered part of the invariant:

```k
    rule <pp> #cutpoint (_) ( Invariants => Invariants ++LocationExprList { File, Line, Col } Expr ) ;
           ~> (#assert{File, Line, Col} Expr ; S2s => S2s)
             ...
         </pp>
```

```k
    syntax Label ::= done(Int)
    syntax Label ::= condTrue(Int) | condFalse(Int)
    rule if (_) _ (.Nothing => else { .StmtList }) [anywhere]
    rule if (_) _ else (if (_) _ _ #as Else => { Else .StmtList }) [anywhere]
    rule <pp> if (*) { BlockTrue } else { BlockFalse }
           => goto condTrue(!I:Int), condFalse(!I:Int);
              condTrue (!I): BlockTrue  ~> goto done(!I);
              condFalse(!I): BlockFalse ~> goto done(!I);
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>

    rule <pp> if (Cond) { BlockTrue } else { BlockFalse }
           => goto condTrue(!I:Int), condFalse(!I:Int);
              condTrue (!I): assume .AttributeList   Cond; BlockTrue  ~> goto done(!I);
              condFalse(!I): assume .AttributeList ! Cond; BlockFalse ~> goto done(!I);
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>
```

Loops are similarly desugared to `goto`s, with the invariants desugared to cutpoints:

```k
    syntax Label ::= loopHead(Int) | loopBody(Int) | guardedDone(Int)
    rule <pp> while (*) Invariants { Body }
           => goto loopHead(!I:Int);
              loopHead(!I): ~>
                #cutpoint(!I) LoopInvariantListToCutpointExprs(Invariants) ; ~>
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
                #cutpoint(!I) LoopInvariantListToCutpointExprs(Invariants) ; ~>
                goto loopBody(!I), guardedDone(!I); ~>
              loopBody(!I): ~>
                assume .AttributeList Cond ; ~>
                Body ~> goto loopHead(!I);
              guardedDone(!I):
                assume .AttributeList ! Cond ; goto done(!I); ~>
              done(!I) :
              .StmtList
             ...
         </pp>
         <loopStack> Stack => !I, Stack </loopStack>
```

```k
    syntax LoopInvariant ::= #loopLocation(LoopInvariant, String, Int, Int, Int, Int) [klabel(#loopLocation), symbol]
    syntax LocationExprList ::= LoopInvariantListToCutpointExprs(LoopInvariantList) [function]
    rule LoopInvariantListToCutpointExprs(.LoopInvariantList) => .LocationExprList
    rule LoopInvariantListToCutpointExprs(#loopLocation(invariant _ Expr;, File, Line, Col, _, _) Rest)
      => {File, Line, Col} Expr, LoopInvariantListToCutpointExprs(Rest)
    rule LoopInvariantListToCutpointExprs(free invariant _ _; Rest) => LoopInvariantListToCutpointExprs(Rest)

    syntax StmtList ::= LoopInvariantListToFreeAssumes(LoopInvariantList) [function]
    rule LoopInvariantListToFreeAssumes(#loopLocation(invariant _ _;, _, _, _, _, _) Rest)
      => LoopInvariantListToFreeAssumes(Rest)
    rule LoopInvariantListToFreeAssumes(free invariant _ Expr; Rest)
      => assume .AttributeList Expr; LoopInvariantListToFreeAssumes(Rest)

```


```k
    rule <pp> break ; => goto done(I); ... </pp>
         <loopStack> I, _Stack </loopStack>
    rule <pp> done(I) : ... </pp>
         <loopStack> I, Stack => Stack </loopStack>
```

If no further preprocessing is needed, we accumulate the statements in `<currBlock>`:

```k
    rule <pp> S:Stmt => .K ... </pp>
         <currBlock> Ss => Ss ++StmtList S </currBlock> [owise]
```

```k
    rule <pp> Label : => .K ... </pp>
         <currLabel> .Nothing => Label </currLabel>
         <currBlock> _ => .StmtList </currBlock>

    syntax KItem ::= "#finalizeBlock"
    rule <pp> (.K => #finalizeBlock) ~>  _Label : ... </pp> <currLabel> _:Label </currLabel>
    rule <pp> (.K => #finalizeBlock)             </pp> <currLabel> _:Label </currLabel>
    rule <pp> #finalizeBlock => .K ... </pp>
         <currLabel> CurrLabel => .Nothing </currLabel>
         <currBlock> CurrBlock </currBlock>
         <currImpl> ImplId </currImpl>
         <implId> ImplId </implId>
         <labels> (.Map => CurrLabel |-> CurrBlock ++StmtList #location( return;, "boogie.md", 0, 0, 0, 0))
                  _Labels
         </labels>
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
          ~> assume .AttributeList (lambda IdsTypeWhereListToIdsTypeList(PArgs) :: Requires && FreeRequires)[IdsTypeWhereListToExprList(IArgs)] ;
          ~> goto $start;
         </k>
         (.CurrImplCell => <currImpl> N </currImpl>)
         <globals> Globals </globals>
         <olds> .Map => Globals </olds>
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
    rule <k> (goto L, _Ls ; ~> _) => (Stmts) </k>
         <labels> L |-> Stmts ... </labels>
         <currImpl> Impl </currImpl>
         <implId>      Impl </implId>
    rule <k> goto _L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .LabelList
```

Invariants
----------

A cutpoint's invariants must evaluate to true before it is reached.
We may also assume they hold after.

```verification
    rule <k> #cutpoint(I) Location Inv, LocExprs ;:KItem
          => #assert #if I in Cutpoints
                     #then #makeAssertionMessage(Location, "BP5005", "This loop invariant might not be maintained by the loop.")
                     #else #makeAssertionMessage(Location, "BP5004", "This loop invariant might not hold on entry.")
                     #fi
                     Inv ;
             #cutpoint(I) LocExprs ;
             assume .AttributeList Inv ;
             ...
         </k>
         <cutpoints> Cutpoints </cutpoints>
```

When we reach a particular cutpoint the first time, we treat it as an abstraction point
and replace modifiable variables with fresh symbolic values.

```k
    rule <k> #cutpoint(I) .LocationExprList ; => #generalize(envToIds(Rho) ++IdList Modifiable) ... </k>
         <locals> Rho </locals>
         <modifies> Modifiable </modifies>
         <cutpoints> (.List => ListItem(I)) Cutpoints </cutpoints>
      requires notBool I in Cutpoints
```

When we reach it a second time we can prune this execution branch, because the
assert/assume structure ensures that our current program state is a subset of
the states when we first encountered the cutpoint (modulo `free invariant`s and
`where` clauses.)

```verification
    rule <k> #cutpoint(I) .LocationExprList ; => assume .AttributeList (false); ... </k>
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
    rule envToIds(X:Id |-> _ Rho) => (X, envToIds(Rho))
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
    syntax Stmt ::= "#return" Location ";"
    rule <k> #return Location ;:KItem
          => #assert #makeAssertionMessage(Location, "BP5003", "A postcondition might not hold on this return path.")
                     (lambda IdsTypeWhereListToIdsTypeList(PArgs) ++IdsTypeList IdsTypeWhereListToIdsTypeList(PRets)
                          :: Ensures
                     ) [ IdsTypeWhereListToExprList(IArgs) ++ExprList IdsTypeWhereListToExprList(IRets) ] ;
             ...
         </k>
         <currImpl> CurrentImpl </currImpl>
         <iargs> IArgs </iargs>
         <ireturns> IRets </ireturns>
         <implId> CurrentImpl </implId>
         <ensures> Ensures </ensures>
         <args> PArgs </args>
         <returns> PRets </returns>
```

9.9 Call statements
-------------------

```k
    syntax Stmt ::= "#call" Location OptionalFree OptionalCallLhs Id "(" ExprList ")" ";"
    rule <k> #call _:Location _:OptionalFree (.Nothing => .IdList :=) _:Id(_:ExprList) ; ... </k>
```

```verification
    context #call _Loc _OptFree _:IdList := _ProcedureName:Id(HOLE) ;
    rule <k> #call Location OptFree X:IdList := ProcedureName:Id(ArgVals);:KItem
          => #if OptFree ==K .Nothing
             #then #assert #makeAssertionMessage(Location, "BP5002", "A precondition for this call might not hold.")
                           (lambda IdsTypeWhereListToIdsTypeList(Args) :: Requires)[ArgVals];
             #else .K
             #fi
          ~> freshen(X ++IdList Mods)
          ~> assume .AttributeList ( lambda IdsTypeWhereListToIdsTypeList(Args) ++IdsTypeList IdsTypeWhereListToIdsTypeList(Rets)
                                         :: Ensures && FreeEnsures )
                                   [ ArgVals ++ExprList IdListToExprList(X) ] ;
             ...
         </k>
         <procName> ProcedureName </procName>
         <args> Args </args>
         <returns> Rets </returns>
         <requires> Requires </requires>
         <ensures> Ensures </ensures>
         <freeEnsures> FreeEnsures </freeEnsures>
         <modifies> Mods </modifies>
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
//    rule <k> inhabitants(T)  => intToT(T, ?V:Int) ... </k>
//         <freshVars> K:K => (K ~> ?V) </freshVars>

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

    syntax Bool ::= intToBool(Int)               [function, total, smtlib(intToBool), no-evaluators]
```

```k
endmodule
```
