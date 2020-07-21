---
geometry: margin=2cm
---


<!-- Generic ML -->
\newcommand{\extension}      {\mathrm{extension}}
\newcommand{\inhabitants}[1] {\llbracket #1 \rrbracket}
\newcommand{\limplies}  {\longrightarrow}
\renewcommand{\C}  {\mathrm{C}} <!-- Context -->

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

Axioms:

1.  $\inhabitants{Int} \subset \inhabitants{\Exp}$
2.  $\inhabitants{Bool} \subset \inhabitants{\Exp}$
3.  $\inhabitants{Bool} = \true \lor \false$

Small step semantics of `forall` in terms of a big step semantics ($\A$, $\E$, $\F$ are from inifinite trace CTL*):

5.  |     $\C[\bforall{x}{e}] \in \E\F \C[\true]$  if $\forall x : \Int . \C[e] \in \A\F \C[\true]$
6.  | $\C[e] \in \A\F \C[\true\lor\false] \limplies$
    |     $\C[\bforall{x}{e}] \in \E\F \C[\false]$ if $\exists x : \Int . \C[e] \in \E\F \C[\false]$

Or, in terms of a small step semantics:

5.  If the inner expression is fully reduced, we can replace `forall` with matching logic's forall:

    | $(\forall x : \Int . e : \Bool) \limplies$
    |    $\C[\bforall{x}{e}] \rewrites1 \C[ \PredicatePatternToBool(\forall x . e = \true) ]$

6.  Otherwise, progress on the inner expression is progress on the outer expression:

    | $(\forall x : \Int . \lnot(e : \Bool) \land e : \Exp) \limplies$
    |    $\C[\bforall{x}{e}] \rewrites1 \C[\bforall{x}{\exists e' : Exp . e' \land ( \C[e] \rewrites1 \C[e'])))}]$ 

<!--
    
5.  The graph of the constant $\true$ function evaluates to $\true$:

    $\C[\bforall{x}{\true}] \rewrites1 \C[true]$

6.  If the graph contains any non-$\true$ Bool elements, then the expression evaluates to $\false$:

    | $\C[\bforall{x}{e}] \rewrites1 \C[\false]$
    |     if   $\extension [ x : \Int ] e \subseteq \exists x : \Int . \langle x, \true \lor \false \rangle$
    |     and  $[ x : \Int ] e \neq [ x : \Int ] \true$

- Prove that this is functional

  i.e. prove that
 
- Soundness?

-->
