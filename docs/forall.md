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

<!-- *   One step rewrite: $x \rewrites{1} y \equiv x \in \E\X y$ -->
*   $\PredicatePatternToBool(\phi) \equiv (\phi \land \true) \lor (\lnot(\phi) \land \false)$
*   Binding: $\bforall{x}{e} \equiv \rforall [ x : \Int ] e$

Symbols:

1.  $\Exp$ a sort constant
2.  $\Bool$ a sort constant
3.  $\Int$ a sort constant
4.  $\true$, $\false$ inhabitants of the Bool sort

1.  $\bforall \_ \_$ Boogie's forall expression
2.  $\rforall$ the retraction symbol

Assumptions:

1. There are no transitions from $\C[\k[\inhabitants{\Bool}]]$. i.e. $\C[\k[\inhabitants{\Bool}]] = \X \C[\k[\inhabitants{\Bool}]]$
2. Evaluating expressions are deterministic and do not modify the outer context:

   For all applicative contexts $\C$, $\forall e' : \Exp . \exists e . \C[\k[e]] = \X \C[\k[e']]$

Axioms:

1.  $\inhabitants{Int} \subset \inhabitants{\Exp}$
2.  $\inhabitants{Bool} \subset \inhabitants{\Exp}$
3.  $\inhabitants{Bool} = \true \lor \false$

Small big semantics of `forall` in terms of a big step semantics ($\A$, $\E$, $\F$ are from inifinite trace CTL*):

5.  If the expression reduces to $\true$ on *all* paths, the `forall` reduces to $\true$:

    $\C[\K[\bforall{x}{e}]] \in \E\F \C[\K[\true]]$  if $\forall x : \Int . \C[\k[e]] \in \A\F \C[\k[\true]]$
6.  If the expression reduces to $\false$ on *any* path and to a $\Bool$ on all paths, the `forall` reduces to $\true$:

    $\C[\K[\bforall{x}{e}]] \in \E\F \C[\K[\false]]$ if $\exists x : \Int . \C[\k[e]] \in \E\F \C[\k[\false]]]$ and $\C[\k[e]] \in \A\F \C[\k[\inhabitants{\Bool}]]$

A small step semantics:

5.  If the inner expression is fully reduced, we can replace `forall` with matching logic's forall:

    | $(\forall x : \Int . e : \Bool) \limplies$
    |    $\C[\K[\bforall{x}{e}]] \rewrites1 \C[\K[\PredicatePatternToBool(\forall x . e = \true)]]$

6.  Otherwise, progress on the inner expression is progress on the outer expression:

    | $(\forall x : \Int . \lnot(e : \Bool) \land e : \Exp) \limplies$
    |    $\C[\K[\bforall{x}{e}]] \rewrites1 \C[\K[\bforall{x}{\exists e' : Exp . e' \land ( \C[k[e]] \rewrites1 \C[k[e']])}]]$ 


### Prove that the small step semantics above implies the big step semantics: 

Consider a state $\C[\K[\bforall{x}{e}]]$, such that $\forall x : Int . \C[\k[e]] \in \A\F \C[\k[\inhabitants{\Bool}]]$.
Along each path $\pi$, there exists a minimum $N$ such that $\pi_N \satisfies \C[\k[\inhabitants{\Bool}]]$.
Take the maximum, $n$, for each of these $N$s.

By assumption `1.`, $\forall x : Int . \C[\k[e]] \in X^n \C[\k[\inhabitants{\Bool}]]$ holds.

Induct on $n$:

When $n = 0$, by `(smallstep 5)` and the definition of $\PredicatePatternToBool$, we get the big step semantics.

When $n > 0$, This lets us apply `(smallstep 6)`.

The precondition holds since
along at least one path, the expression is not fully evaluated.

Further, for any $i \lt n$, $\forall x : Int . \C[\k[e]] \in AX^n \C[\k[\inhabitants{\Bool}]]$
does not hold (since on atleast one path the expression is not fully evaluated).


we have, $\C[\k[\inhabitants{\Bool}]]$, and two cases:

1. $\C[\k[\inhabitants{true}]]$
.

After a bounded number of steps, $n$ along every path, the state eventually reaches $\C[\k[\Bool]]$.

There are two possibilities

When n = 0:

    1. it reaches 

By Assumption 1, we have for some finite $n$, $\C[\k[e]] \in (\E\X)^n \C[\k[\true]]$.



$\C[\bforall{x}{e}] \in\E\X \C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}]$

$\C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}] \in\E\X  \C[\bforall{x}{\exists e'' : Exp . e'' \land ( \C[{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}] \in\E\X \C[e''])}]$

$\C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}] \in\E\X  \C[\bforall{x}{\exists e', e'' : Exp . e'' \land ( \C[{ e' }] \in\E\X \C[e''])\land ( \C[e] \in\E\X \C[e'])}]$

By monotonicity of symbol application:

$\C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}] \in\E\X  \C[\bforall{x}{\exists e', e'' : Exp . e'' \land ( \C[e] \in\E\X\E\X \C[e''])}]$

Removing redundant quantifier: 

$\C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \in\E\X \C[e'])}] \in\E\X  \C[\bforall{x}{\exists e'' : Exp . e'' \land ( \C[e] \in\E\X\E\X \C[e''])}]$

$\C[\bforall{x}{e}] \in \E\X\E\X  \C[\bforall{x}{\exists e'' : Exp . e'' \land ( \C[e] \in\E\X\E\X \C[e''])}]$

By induction:

$\C[\bforall{x}{e}] \in (\E\X)^n  \C[\bforall{x}{\exists e'' : Exp . e'' \land ( \C[e] \in(\E\X)^n \C[e''])}]$
$\C[\bforall{x}{e}] \in (\E\F)^n  \C[\bforall{x}{\exists e'' : Exp . e'' \land ( \C[e] \in(\E\X)^n \C[e''])}]$

