---
geometry: margin=2cm
---


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
\newcommand{\Int}            {\mathrm{Int}}
\newcommand{\Nat}            {\mathrm{Nat}}
\newcommand{\Exp}            {\mathrm{Exp}}
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
*   Binding: $\bforall{x}{e} \equiv \rforall [ x : \Int ] e$

---

*   $\C$ denotes a configuration context
*   $\K$ denotes a context who's top symbol is $\k$

Symbols:

1.  $\Exp$ a sort constant
2.  $\Bool$ a sort constant
3.  $\Int$ a sort constant
4.  $\true$, $\false$ inhabitants of the Bool sort

1.  $\bforall \_ \_$ Boogie's forall expression
2.  $\rforall$ the retraction symbol

1.  $\k$ is the `<k>` cell.

Assumptions:

1. `(bool-value)`: There are no transitions from $\C[\k(\inhabitants{\Bool})]$. i.e. $\C[\k(\inhabitants{\Bool})] = \X \C[\k(\inhabitants{\Bool})]$
2. `(exp-no-side-effects)`: Evaluating expressions are deterministic and do not modify the outer context:

   For all applicative contexts $\C$, $\forall e' : \Exp . \exists e . \C[\k(e)] = \E\X \C[\k(e')]$

3. `(exp-bounded)`: Execution traces for all expressions converges.

Axioms:

1.  $\inhabitants{Int} \subset \inhabitants{\Exp}$
2.  $\inhabitants{Bool} \subset \inhabitants{\Exp}$
3.  $\inhabitants{Bool} = \true \lor \false$

Big step semantics of `forall` in terms of a big step semantics ($\A$, $\E$, $\F$ are from inifinite trace CTL*):

5.  `(bigstep-forall-true)`: If the expression reduces to $\true$ on *all* paths, the `forall` reduces to $\true$:

    | $\C[\K[\bforall{x}{e}]] \in \E\F \C[\K[\true]]$
    |   if $\forall x : \Int . \C[\k(e)] \in \A\F \C[\k(\true)]$

6.  `(bigstep-forall-false)`:
    If the expression reduces to $\false$ on *any* path and to a $\Bool$ on all paths, the `forall` reduces to $\true$:

    | $\C[\K[\bforall{x}{e}]] \in \E\F \C[\K[\false]]$
    |   if  $\exists x : \Int . \C[\k(e)] \in \E\F \C[\k(\false)]]$
    |   and $\forall x : \Int . \C[\k(e)] \in \A\F \C[\k(\inhabitants{\Bool})]$

A small step semantics:

5.  `(smallstep-forall-reduce)`
    If the inner expression is fully reduced, we can replace `forall` with ML's forall:

    | $(\forall x : \Int . e : \Bool) \limplies$
    |    $\C[\K[\bforall{x}{e}]] \rewrites1 \C[\K[\PredicatePatternToBool(\forall x . e = \true)]]$

6.  `(smallstep-forall-progress)`
    Otherwise, progress on the inner expression is progress on the outer expression, and convert the predicate pattern to a $\Bool$:

    | $(\exists x : \Int . \lnot(e : \Bool) \land \forall x : \Int . e : \Exp) \limplies$
    |    $\C[\K[\bforall{x}{e}]] \rewrites1 \C[\K[\bforall{x}{\exists e' : Exp . e' \land ( \C[k[e]] \rewrites1 \C[k[e']])}]]$

### Prove that the small step semantics above implies the big step semantics: 

a.  Consider a state $\C[\K[\bforall{x}{e}]]$, such that $\forall x : Int . \C[\k(e)] \in \A\F \C[\k(\true)]$.
    We know that for all $\Int$s $x$, there is a minumum $N$ such that $\C[\k(e)] \limplies (\A\X)^N \C[\k(\true)]$.
    By `(exp-bounded)`, there is a maximum such $N$, say $n$.
    By `(bool-value)` we have $\forall x. \C[\k(e)] \limplies (\A\X)^n \C[\k(\true)]$.
    Since $N$ was chosen to be the minumum such $N$, we have for all $i < n$, $\lnot \forall x : \Int . e : \Bool$.
    Apply induction on $n$.

    When $n = 0$, we have $\forall x. \C[\k(e)] \limplies \C[\k(\true)]$.
    By `(smallstep-forall-reduce)` $\C[\K[\bforall{x}{e}]] \in \E\X \C[\K[true]]$, since $\PredicatePatternToBool(\forall x . \true = \true) = \true$.
    
    When $n > 0$, we have $\exists x. \Int . \lnot e : Bool$ and `(smallstep-forall-progress)` holds.
    $\C[\K[\bforall{x}{e}]] \limplies \E\X \C[\K[\bforall{x}{\exists e' : Exp . e' \land ( \C[k[e]] \rewrites1 \C[k[e']])}]]$
    But, $e'$ is an expression, so we can apply the inductive hypothesis.

b.  Consider a state $\C[\K[\bforall{x}{e}]]$, such that $\forall x : Int . \C[\k(e)] \in \A\F \C[\k(\inhabitants{\Bool})]$.
    We know that for all $\Int$s $x$, there is a minumum $N$ such that $\C[\k(e)] \limplies (\E\X)^N \C[\k(\inhabitants{\Bool})]$.
    By `(exp-bounded)`, there is a maximum such $N$, say $n$.
    By `(bool-value)` and assumption, we have $\exists x. \C[\k(e)] \limplies (\E\X)^n \C[\k(\false)]$.
    and $\forall x. \C[\k(e)] \limplies (\E\X)^n \C[\k(\false)]$.
    Since $N$ was chosen to be the minumum such $N$, we have for all $i < n$, $\lnot \forall x : \Int . e : \Bool$.
    Apply induction on $n$.

    When $n = 0$, we have $\forall x. \C[\k(e)] \limplies \C[\k(\false)]$.
    By `(smallstep-forall-reduce)` $\C[\K[\bforall{x}{e}]] \in \E\X \C[\K[\false]]$, since $\PredicatePatternToBool(\forall x . e = \true) = \true$ when some $e$ is $\false$.

    Inductive case is identical.
