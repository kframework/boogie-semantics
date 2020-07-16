\newcommand{\inhabitants}[1] {\llbrackets #1 \rrbrackets}
\newcommand{\bforall}        {\mathtt{forall}}
\newcommand{\rforall}        {\mathrm{forall}}
\newcommand{\true}           {\mathrm{true}}
\newcommand{\false}          {\mathrm{false}}
\newcommand{\next}           {\circle}

Symbols:

* Var               a sort constant
* Exp               a sort constant
* Bool              a sort constant
* $\true$, $\false$ inhabitants of the Bool sort

* $\bforall$    Boogie's forall expression
* $\rforall$    the retraction symbol

Axioms:

* $\inhabitants{Var}  \subset \inhabitants{Exp}$
* $\inhabitants{Bool} \subset \inhabitants{Exp}$
* $\inhabitants{Bool} = \true \lor \false$


* Binding: $\bforall x . e \equiv \rforall [ x : Var ] e$

* $\rforall [ x : Var ] true  \in \next(true)$

* If the graph contains any non-$\true$ Bool elements, then the expression evaluates to false.

  $\rforall [ x : Var ] e) \in \next(false)$
  if   $extension [ x : Var ] e \subset \exists x : Var \langle x, \true \or \false \rangle$
  and  $[ x : Var ] e \not\eq [ x : Var ] \true$

* Any steps taken on the inner expression can by taken by the 
  $\next(\rforall([ x : Var ] e)) \implies \rforall([ x : Var ] \next(e))$
