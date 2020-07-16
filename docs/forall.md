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
\newcommand{\rewrites}     {\Longrightarrow_1}

Symbols:

* $\Exp$               a sort constant
* $\Bool$              a sort constant
* $\Int$               a sort constant
* $\true$, $\false$    inhabitants of the Bool sort

* $\bforall \_ \mathtt{: int .} \_$    Boogie's forall expression
* $\rforall$    the retraction symbol

Axioms:

* $\inhabitants{Int} \subset \inhabitants{\Exp}$
* $\inhabitants{Bool} \subset \inhabitants{\Exp}$
* $\inhabitants{Bool} = \true \lor \false$

* Binding: $\bforall{x}{e} \equiv \rforall [ x : \Int ] e$

*  The graph of the constant $\true$ function evaluates to $\true$:

   $C[\bforall{x}{\true}] \rewrites C[true]$

* If the graph contains any non-$\true$ Bool elements, then the expression evaluates to $\false$:

  | $C[\bforall{x}{e}) \rewrites C[\false]$
  |     if   $\extension [ x : \Int ] e \subseteq \exists x : \Int . \langle x, \true \lor \false \rangle$
  |     and  $[ x : \Int ] e \neq [ x : \Int ] \true$

*  a graph who's inner expression can be further reducted can be reduced to the intension of the set of all the states $e$ can evaluate to:

   $C[\bforall{x}{e}] \rewrites C[\bforall{x}{\exists e' : Exp . e' \land ( C[e] \rewrites C[e'])))}]$ 

where $x \rewrites y \equiv x \in \next y$


- Use booigie forall everywhere
- 
- Prove that this is functional
- Soundness
