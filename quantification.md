We'd like a semantics for `forall` that works as follows:

1.  `(forall-true)`: If the expression reduces to $\true$ on *all* paths, the `forall` reduces to $\true$:

    in K:

    ```
    rule (forall X : T :: E) => true requires "E reaches true on all paths for all evaluations of `X` in `inhabitants(T)`"
    ```

2.  `(forall-false)`: If the expression reduces to $\false$ on *any* path, the `forall` reduces to $\false$: 

    in K:

    ```
    rule (forall X : T :: E) => false requires "E reaches false on any path for any one evaluation of `X` in `inhabitants(T)`"
    ```

Note that `(forall-true)` and `(forall-false)` are not mutually exclusive.
Since Reachability Logic claims hold vacuously on infinite traces, they may both hold. 

## Implementation

Our implementation takes advantage of the following properties of Boogie:

1. There are no transitions from $\C[\k(\inhabitants{\Bool})]$. i.e. $\C[\k(\inhabitants{\Bool})] = \X \C[\k(\inhabitants{\Bool})]$
2. Expressions do not have side-effects.
3. Execution traces for all expressions converges. (This makes axioms `5.` and `6.` mutually exclusive)

TODO: Prove that with these assumptions, the semantics above matches the semantics below.

Since K does not support this kind of reasoning within a semantics, we approximate it for Boogie using a meta definition.
In this file, we interleave two K definitions:

the other at the object level (code-blocks tagged with `object`):

```objectk
module BOOGIE-QUANTIFIERS
    imports BOOGIE
```

one, a meta-definition (code-blocks tagged with `metak`),

```metak
module BOOGIE-QUANTIFIERS-META
    imports DRIVER-HELPERS
    imports K-FRONTEND
```

When Boogie's forall is encountered, we convert it to a binder. We use `lambda` because the haskell backend does not support substitution.

```objectk
    syntax Expr ::= "(" "forallbinder" ValueExpr "::" Expr ")"  [klabel(forallbinder)      , symbol]
    rule <k> (#forall X : T :: Expr) => (forallbinder ?I:Int :: (lambda X : T :: Expr)[intToT(T, ?I:Int)]) ... </k>
```

We then use a meta rule to heat the binder.
Note that this *cannot* be implemented as a object-level rule because we need to ensure that different `forall` binders are not confused.
i.e. a `forall` encountered along one program path must be evaulated separately from a `forall` encountered alond a different path.

```objectk
    syntax Expr ::= "(" "forallbinderheated" ValueExpr "::" Expr ")"  [klabel(forallbinderheated), symbol, strict(2)]
```

```metak
    rule <k> triage(kseq { .Sorts } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinder  { .Sorts } ( V, E )), Rest) , Pgm)
          => koreExec(setKCell(Pgm, kseq { .Sorts } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinderheated  { .Sorts } ( V, E )), dotk { .Sorts }(.Patterns))))
          ~> forallFreezer(Rest, Pgm)
             ...
         </k>
         <freshVars> .K => getFreshVars(Pgm) ... </freshVars>
```

The evaluation of the quantified expression results in a disjunction of configurations, constrained by their path conditions.

```metak
    syntax KItem ::= forallResult(Pattern, Pattern)
    rule <k> triage(kseq { .Sorts }(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated { .Sorts }(inj { QSort, SortValueExpr{} } ( V : QSort ), inj{SortBool{},SortExpr{}}(E))),dotk { .Sorts }(.Patterns)),\and{_}(C,PathConditions))
          => forallResult( V : QSort
                         , \or { SortGeneratedTopCell {}}
                               ( \not {SortGeneratedTopCell{}}( makePathConditions(PathConditions, FreshVarsOrig, getFreshVars(C)) )
                               , \equals{SortBool{}, SortGeneratedTopCell{}} (E, \dv {SortBool{}}("true"))
                               )
                         )
             ...
         </k>
         <freshVars> FreshVarsOrig ...</freshVars>
```

```metak
    syntax Pattern ::= makePathConditions(Pattern, origVars: Patterns, newVars: Patterns) [function] 
    rule makePathConditions(PC, dotk {.Sorts}(.Patterns), _) => PC
    rule makePathConditions( PC
                           , kseq {.Sorts}(inj{Sort, _}(V1), P1s)
                           , kseq {.Sorts}(inj{Sort, _}(V2), P2s)
                           )
      => makePathConditions(\and{SortGeneratedTopCell{}}(\equals { Sort, SortGeneratedTopCell{} } (V1, V2), PC), P1s, P2s)
      requires V1 =/=K V2
    rule makePathConditions( PC
                           , kseq {.Sorts}(inj{Sort, _}(V), P1s)
                           , kseq {.Sorts}(inj{Sort, _}(V), P2s)
                           )
      => makePathConditions(PC, P1s, P2s)
```

The results and path-conditions from these branches are combined into an object-level boolean function using object-level logical connectives.

```metak
    rule <k> forallResult(V : QSort, E1) ~> forallResult(V : QSort, E2)
          => forallResult(V : QSort, \and {SortGeneratedTopCell{}} (E1, E2))
             ...
         </k>
```

We may sometimes need to alpha-rename the bound variable to enable this.

```metak
    rule <k> (forallResult(V1 : QSort, E1) => forallResult(V1 : QSort, E1)[freshVariable(!I)/V1:KVar])
          ~> (forallResult(V2 : QSort, E2) => forallResult(V2 : QSort, E2)[freshVariable(!I)/V2:KVar])
             ...
         </k>
      requires V1 =/=K V2
```

We bring each branch to the front to allow them to be triaged.

```metak
    rule <k> (forallResult(_, _) #as Curr) ~> (_:Pattern       #as Next) => (Next:KItem ~> Curr:KItem) ... </k>
    rule <k> (forallResult(_, _) #as Curr) ~> (koreExec(_, _)  #as Next) => (Next:KItem ~> Curr:KItem) ... </k>
```

Finally, when all branch branches are fully reduced, we cool the result back into the original context,
replacing the `forallbinderheated` with `forallbindercooled` to indicate to the object-definition that the `forall` has been fully evaluated.

```objectk
    syntax Expr ::= "(" "forallbindercooled" ValueExpr "::" Expr ")"  [klabel(forallbindercooled), symbol, strict(2)]
```

```metak
    syntax KItem ::= forallFreezer(kcellRest: Pattern, config: Pattern)
    rule <k> forallResult(V : QSort, E)
          ~> forallFreezer(Rest, Pgm)
          => koreExec( WorkingDir +String "/" +String Int2String(!I) +String "-true.kore"
                     , \and { SortGeneratedTopCell{} }( setKCell(Pgm, kseq { .Sorts }( inj{SortBool{},SortKItem{}}(\dv {SortBool{}} ("true")), Rest))
                                                      , \not{SortGeneratedTopCell{}}(\exists{SortGeneratedTopCell{}}(V : QSort,\not{SortGeneratedTopCell{}}(E)))
                     )                                )
          ~> koreExec( WorkingDir +String "/" +String Int2String(!J) +String "-false.kore"
                     , \and { SortGeneratedTopCell{} }( setKCell(Pgm, kseq { .Sorts }( inj{SortBool{},SortKItem{}}(\dv {SortBool{}} ("false")), Rest))
                                                      , \exists{SortGeneratedTopCell{}}(V : QSort,\not{SortGeneratedTopCell{}}(E))
                     )                                )
             ...
         </k>
         <freshVars> _:Patterns => .K ... </freshVars>
         <workingDir> WorkingDir </workingDir>
```

```objectk
endmodule
```

```metak
endmodule
```
