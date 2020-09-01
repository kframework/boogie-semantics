To specify the behaviour of `forall` expressions, we use a combination evaluation contexts and binders.

### Evaluation contexts

Evaluation contexts allow us to define the small step semantics of larger expressions in terms of their subexpressions.
For example in K, we may write:

```
    syntax Expr ::= Int "+" Int
    context HOLE + _E2
    context _:Int + HOLE
    rule <k> V1 + V2 => V1 +Int V2 ... </k>
```

The two `context` statement indicate that the sub-expressions in the first and
second arguments of `+` must be evaluated first, and in order, before the entire
expression is evaluated to the integer sum.

Contexts are translated into matching logic axioms.

First, we define notation, $\gamma$ for describing contexts: $\gamma \hole . e \equiv \exists \gamma' \hole . e$

Next, we define a set of axioms over $\gamma$ 

1. Identity context: $(\gamma \hole . \hole)[T] = T$
2. Nested contexts: $(\gamma \hole_1 . \phi(\hole_1)) [(\gamma \hole_2 . \psi(\hole_2)) [T]] = \gamma \hole . \phi(\psi(\hole)) [T]$
3. For every evaluation context $C[\hole]$ we define an axiom: $\C[T] = (\gamma \hole. \C(\hole))[T]$

   For example, for addition we may define the following contexts:
   
   $$
   X + Y = (\gamma \hole . \hole + Y)[X] \\
   (X \limplies \inhabitants{\Int}) \implies X + Y = (\gamma \hole . \hole + Y)[Y]
   $$


The `rule` declaration is also translated to a matching logic axiom as follows:

$$
\C{cfg}[ \C{k}[X+Y] ] \implies \next \C{k}[ \C{k}[ X +_{Int} Y ]]
$$

TODO: Explain exactly what $\C{cfg}$ and $\C{k}$ are.

### Binders

TODO: Explain `intension` and taking the graphs.

Notations:

* Binding: $\bforall{x}{e} \equiv \rforall [ x : \Int ] e$

* Forall is a context: $(\bforall{x}{\C[E]}) = (\gamma \hole .\bforall{x}{\C[\hole]})[E]$ if $x$ is not free in $E$ 

  Note that we may not use the standard axiom for other contexts since we need the additional contraint that $x$ is not free.

* If the inner expression is fully reduced, we can replace `forall` with ML's forall:

  $\bforall{x}{\true}            \implies \next \true$
  $\bforall{x}{\true \or \false} \implies \next \false$
  $\bforall{x}{\false}           \implies \next \false$


Evaluating the expression: `forall x :: int . inc(x) = x + 1`

$$
    C[forall x :: int . f(x) = x + y]
=   C[forall x :: int .  (\gamma \hole . f(x) = x + \hole)[y]]
=>  C[(\gamma  \hole . forall x :: int . f(x) = x + \hole)[y]]
=>  C[(\gamma  \hole . forall x :: int . f(x) = x + \hole)[3]]
=   C[(                forall x :: int . f(x) = x + 3)]
=   C[forall x :: int .  (\gamma \hole . f(x) = \hole)[x + 3]]
$$


Now, we are stuck. We cannot heat out `x + 3` because `x` is bound.

----

```k
    syntax Expr ::= "(" "forallbinder"       ValueExpr "::" Expr ")"  [klabel(forallbinder)      , symbol]
                  | "(" "forallbinderheated" ValueExpr "::" Expr ")"  [klabel(forallbinderheated), symbol, strict(2)]
                  | "(" "forallbindercooled" ValueExpr "::" Expr ")"  [klabel(forallbindercooled), symbol, strict(2)]
    syntax Bool ::= smtforall(Int, Bool) [function, functional, no-evaluators, smt-hook((forall ((#1 Int)) #2))]

    rule <k> (#forall X : T :: Expr) => (forallbinder ?I:Int :: (lambda X : T :: Expr)[?I:Int]) ... </k>
// Note: There is an additional rule implemented at the meta level to for heating from forallbinder to forallbinderheated
// and for cooling from forallbinderheated to forallbindercooled. 
    rule <k> (forallbindercooled V :: B) => smtforall(V, B) ... </k>
```

```k
    syntax KVar ::= "Lblforallbinder"       [token]
                  | "Lblforallbinderheated" [token]
                  | "Lblforallbindercooled" [token]
                  | "SortExpr"              [token]
                  | "SortBool"              [token]
                  | "SortInt"               [token]
    syntax KItem ::= forallFreezer(kcellRest: Pattern, config: Pattern)
    rule <k> triage(kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinder { } ( V, E )), Rest) , Pgm) => .K
          ~> exec(setKCell(Pgm, kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinderheated { } ( V, E )), dotk{}(.Patterns))))
          ~> forallFreezer(Rest, Pgm)
             ...
         </k>
```

```k
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(V,inj{SortBool{},SortExpr{}}(E))), dotk{}(.Patterns)), _)
          ~> forallFreezer(Rest, Pgm)
          => exec(setKCell(Pgm, kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbindercooled{}(V,inj{SortBool{},SortExpr{}}(E))),Rest)))
             ...
         </k> 

    // TODO: We should also update the fresh counter here
    rule <k> (triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(_,inj{SortBool{},SortExpr{}}(_))), dotk{}(.Patterns)), _) #as Now)
          ~> (\and { SortGeneratedTopCell { } } ( _, _ ) #as Next)
          => (Next:KItem ~> Now:KItem)
             ...
         </k>
         
    syntax KVar ::= freshVariable(Int) [function]
    rule freshVariable(I) => String2KVar("VDriver" +String Int2String(I))

    syntax KVar ::= "Lblimplies" [token]
    // Be careful about chosing fresh variables from a domain that does not intersect with either K's, or kore-execs domains of choice.
    // TODO: We should also update the fresh counter here
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( (V1 => freshVariable(!I)) : Sort ), inj{SortBool{},SortExpr{}}(E1 => E1[freshVariable(!I)/V1]))),dotk{}(.Patterns)),C1 => C1[freshVariable(!I)/V1:KVar])
          ~> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(inj { Sort, SortValueExpr } ( (V2 => freshVariable(!I)) : Sort ), inj{SortBool{},SortExpr{}}(E2 => E2[freshVariable(!I)/V2]))),dotk{}(.Patterns)),C2 => C2[freshVariable(!I)/V2:KVar])
             ...
         </k>
      requires V1 =/=K V2

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
