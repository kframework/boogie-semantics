---
geometry: margin=2cm
---

\newcommand{\inhabitants}[1] {\llbracket #1 \rrbracket}

\newcommand{\extension}        {\mathrm{extension}}
\newcommand{\bforall}[2]        {\mathtt{forall } #1 \mathtt{ : int . } #2}
\newcommand{\rforall}        {\mathrm{\#forall }}
\newcommand{\true}           {\mathrm{true }}
\newcommand{\false}          {\mathrm{false }}
\newcommand{\next}           {\bullet}

\newcommand{\Int}          {\mathrm{Int}}
\newcommand{\Exp}          {\mathrm{Exp}}
\newcommand{\Bool}          {\mathrm{Bool}}

\newcommand{\PredicatePatternToBool}          {\mathrm{PredicatePatternToBool}}

\newcommand{\limplies}  {\longrightarrow}
\newcommand{\rewrites}[1]  {\Longrightarrow^{#1}}

Notations:

*   One step rewrite: $x \rewrites{1} y \equiv x \in \next y$
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

Small step semantics of `forall` in terms of a big step semantics:

5.  $C[\bforall{x}{e}] \rewrites{1} C[\true]$ if
    $\forall x : \Int . C[e] \rewrites{*}_{\forall} C[\true]$
6.  $C[\bforall{x}{e}] \rewrites{1} C[\false]$ if
    $\exists x : \Int . C[e] \rewrites{*}_{\exists} C[\false]$

Or, in terms of a small step semantics:

5.  If the inner expression is fully reduced, we can replace `forall` with matching logic's forall:

    | $(\forall x : \Int . e : \Bool) \limplies$
    |    $C[\bforall{x}{e}] \rewrites1 C[ \PredicatePatternToBool(\forall x . e = \true) ]$

6.  Otherwise, progress on the inner expression is progress on the outer expression:

    | $(\forall x : \Int . \lnot(e : \Bool) \land e : \Exp) \limplies$
    |    $C[\bforall{x}{e}] \rewrites1 C[\bforall{x}{\exists e' : Exp . e' \land ( C[e] \rewrites1 C[e'])))}]$ 

<!--
    
5.  The graph of the constant $\true$ function evaluates to $\true$:

    $C[\bforall{x}{\true}] \rewrites1 C[true]$

6.  If the graph contains any non-$\true$ Bool elements, then the expression evaluates to $\false$:

    | $C[\bforall{x}{e}] \rewrites1 C[\false]$
    |     if   $\extension [ x : \Int ] e \subseteq \exists x : \Int . \langle x, \true \lor \false \rangle$
    |     and  $[ x : \Int ] e \neq [ x : \Int ] \true$

- Prove that this is functional

  i.e. prove that
 
- Soundness?

-->
