<!-- Generic ML -->
\newcommand{\extension}      {\mathrm{extension}}
\newcommand{\inhabitants}[1] {\llbracket #1 \rrbracket}
\newcommand{\limplies}  {\longrightarrow}
\newcommand{\satisfies}  {\models}

<!-- ML CTL* -->
\newcommand{\rewrites}[1]  {\in \E\X}
\newcommand{\A}            {\mathtt{A}}
\newcommand{\F}            {\mathtt{F}}
\newcommand{\E}            {\mathtt{E}}
\newcommand{\X}            {\mathtt{X}}

<!-- Boogie -->
\newcommand{\true}           {\mathrm{true }}
\newcommand{\false}          {\mathrm{false }}
\newcommand{T}               {\mathrm{Int}}
\newcommand{\Expr}           {\mathrm{Expr}}
\newcommand{\Bool}           {\mathrm{Bool}}
\newcommand{\bforall}[2]     {\mathtt{forall } #1 \mathtt{ : int . } #2}

<!-- Context -->
\renewcommand{\C}  {\mathrm{C}}
\newcommand{\K}    {\mathrm{K}}
\renewcommand{\k}  {\mathrm{k}}

<!-- Boogie related ML -->
\newcommand{\rforall}                  {\mathrm{\#forall }}
\newcommand{\PredicatePatternToBool}   {\mathrm{PredicatePatternToBool}}

Notations:

*   $\PredicatePatternToBool(\phi) \equiv (\phi \land \true) \lor (\lnot(\phi) \land \false)$
*   Binding: $\bforall{x}{e} \equiv \rforall [ x : T ] e$

---

*   $\C$ denotes a configuration context
*   $\K$ denotes a context who's top symbol is $\k$

Symbols:

1.  $\Expr$ a sort constant
2.  $\Bool$ a sort constant
3.  $\true$, $\false$ inhabitants of the Bool sort

1.  $\bforall \_ \_$ Boogie's forall expression
2.  $\rforall$ the retraction symbol

1.  $\k$ is the `<k>` cell.

Axioms:

1.  $\inhabitants{Int} \subset \inhabitants{\Expr}$
2.  $\inhabitants{Bool} \subset \inhabitants{\Expr}$
3.  $\inhabitants{Bool} = \true \lor \false$

5.  `(forall-true)`: If the expression reduces to $\true$ on *all* paths, the `forall` reduces to $\true$:

    | $\C[\K[\bforall{x}{e}]] \reachesE \C[\K[\true]]$
    |   if $\forall x : T . \C[\k(e)] \reachesA \C[\k(\true)]$

6.  `(forall-false)`: If the expression reduces to $\false$ on *any* path, the `forall` reduces to $\false$: 

    | $\C[\K[\bforall{x}{e}]] \reachesE \C[\K[\false]]$
    |   if  $\exists x : T . \C[\k(e)] \reachesE \C[\k(\false)]]$

Note that `(forall-true)` and `(forall-false)` are not mutually exclusive.
Since Reachability Logic claims hold vacuously on infinite traces, they may both hold. 

## Implementation

Our implementation takes advantage of the following properties of Boogie:

1. There are no transitions from $\C[\k(\inhabitants{\Bool})]$. i.e. $\C[\k(\inhabitants{\Bool})] = \X \C[\k(\inhabitants{\Bool})]$
2. Expressions do not have side-effects.
3. Execution traces for all expressions converges. (This makes axioms `5.` and `6.` mutually exclusive)

TODO: Prove that with these assumptions, the semantics above matches the semantics below.

Since K does not support this kind of reasoning within a semantics, we approximate it for Boogie using a meta definition.
In this file, we interleave to K definitions: one, a meta-definition (code-blocks tagged with `metak`),
the other at the object level (code-blocks tagged with `object`).

```objectk
module BOOGIE-QUANTIFIERS-OBJECT
    imports BOOGIE-RUNTIME
```

```metak
module BOOGIE-QUANTIFIERS-META
    imports DRIVER-HELPERS
```

When Boogie's forall is encountered, we convert it to a binder. We use `lambda` because the haskell backend does not support substitution.

```objectk
    syntax Expr ::= "(" "forallbinder" ValueExpr "::" Expr ")"  [klabel(forallbinder)      , symbol]
    rule <k> (#forall X : T :: Expr) => (forallbinder ?I:Int :: (lambda X : T :: Expr)[?I:Int]) ... </k>
```

We then use a meta rule to heat the binder.
Note that this *cannot* be implemented as a object-level rule because we need to ensure that different `forall` binders are not confused.
i.e. a `forall` encountered along one program path must be evaulated separately from a `forall` encountered alond a different path.

```objectk
    syntax Expr ::= "(" "forallbinderheated" ValueExpr "::" Expr ")"  [klabel(forallbinderheated), symbol, strict(2)]
```

```metak
    rule <k> triage(kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinder { } ( V, E )), Rest) , Pgm) => .K
          ~> exec(setKCell(Pgm, kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinderheated { } ( V, E )), dotk{}(.Patterns))))
          ~> forallFreezer(Rest, Pgm)
             ...
         </k>
```

The evaluation of the quantified expression results in a disjunction of configurations, constrained by their path conditions.

The results and path-conditions from these branches are combined into an object-level boolean function using object-level logical connectives.

```metak
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( V : Sort ) ,inj{SortBool{},SortExpr{}}(E1))),dotk{}(.Patterns)),\and{GTC}(C,PathConditions1))
          ~> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( V : Sort ) ,inj{SortBool{},SortExpr{}}(E2))),dotk{}(.Patterns)),\and{GTC}(_,PathConditions2))
          => triage( kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( V : Sort )
                   , inj{SortBool{},SortExpr{}} ( Lbland{} (
                        Lblimplies{}(PredicateToBooleanExpression(PathConditions2), PredicateToBooleanExpression(E2))
                      , Lblimplies{}(PredicateToBooleanExpression(PathConditions1), PredicateToBooleanExpression(E1))
                     ))
                     )), dotk{}(.Patterns))
                   , \and {GTC} (C, \or {GTC} (PathConditions1, PathConditions2))
                   )
             ...
         </k>
```

We may sometimes need to alpha-rename the bound variable to enable this.

```metak
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( (V1 => freshVariable(!I)) : Sort ), inj{SortBool{},SortExpr{}}(E1 => E1[freshVariable(!I)/V1]))),dotk{}(.Patterns)),C1 => C1[freshVariable(!I)/V1:KVar])
          ~> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( (V2 => freshVariable(!I)) : Sort ), inj{SortBool{},SortExpr{}}(E2 => E2[freshVariable(!I)/V2]))),dotk{}(.Patterns)),C2 => C2[freshVariable(!I)/V2:KVar])
             ...
         </k>
      requires V1 =/=K V2
```

We bring each branch to the front to allow them to be triaged. (See [driver/driver.md] for other cases of triaging.)

```metak
    rule <k> (triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(_,inj{SortBool{},SortExpr{}}(_))), dotk{}(.Patterns)), _) #as Now)
          ~> (\and { SortGeneratedTopCell { } } ( _, _ ) #as Next)
          => (Next:KItem ~> Now:KItem)
             ...
         </k>
```

Finally, when all branch branches are fully reduced, we cool the result back into the original context,
replacing the `forallbinderheated` with `forallbindercooled` to indicate to the object-definition that the `forall` has been fully evaluated.

```objectk
    syntax Expr ::= "(" "forallbindercooled" ValueExpr "::" Expr ")"  [klabel(forallbindercooled), symbol, strict(2)]
```

```metak
    syntax KItem ::= forallFreezer(kcellRest: Pattern, config: Pattern)
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(V,inj{SortBool{},SortExpr{}}(E))), dotk{}(.Patterns)), _)
          ~> forallFreezer(Rest, Pgm)
          => exec(setKCell(Pgm, kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbindercooled{}(V,inj{SortBool{},SortExpr{}}(E))),Rest)))
             ...
         </k> 
```

Finally, we reduce the binder to the logical `forall` construct:

```objectk
    syntax Bool ::= smtforall(Int, Bool) [function, functional, no-evaluators, smt-hook((forall ((#1 Int)) #2))]
    rule <k> (forallbindercooled V :: B) => smtforall(V, B) ... </k>
```

```objectk
endmodule
```

```metak
endmodule
```
