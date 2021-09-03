---
title: Boogie Semantics in K
header-includes: |
  <style>
    body { width: 5em !important; }
    div.slide {
        width: 40em !important;
        margin-left: auto !important;
        margin-right: auto  !important;
    }

    h1 { margin-right: 0em !important; text-align: center}
  </style>
---

# What is Boogie?

- Intermediate Verification language

    ![](../../docs/boogie-architecture.svg)

- Imperative programming language with additional features needed for verification
    - pre- and post-conditions
    - invariants
    - quantification

----

# Motivation

- Translations exist for Dafny, C, Java.
- Entering the Blockchain space: Facebook's Move language has a prover that relies Boogie.

![.](../../docs/boogie-languages.png){ width=20em }

# Motivation: Advantages of Boogie over K

- Allows specifing invariants and claims in source language
    - In K, the user must be aware of details of configuration
      and have working knowledge of K
- Fast! Z3 is called only for each assertion?
    - K calls Z3 multiple times before taking each step
      whereas Boogie appears to only call into the solver

# Motivation: Advantages of K over Boogie

- Semantics-first approach removes redundancy 
  E.g.
  * Compiler: Dafny to C#      is  6577 LoC
  * Verifier: Dafny to Boogie  is 18852 LoC

- Better confidence re consistency between interpreter and prover

- (In theory,) can generate proof objects

# Motivation

:::bigger
Can K do everything that Boogie can?
:::

# Motivation

-  Claims, invariants, pre- and post-conditions
   may all be written in the source language with small extensions.

-  No knowledge of internals of K would be needed.

-  Lowers the barriers to entry for using K

- Some blockchains are using Boogie to verify contracts.  
  E.g. Facebook/Diem's Move language:

  ```
  fun simple1(x: u64, y: u64) {
      if (!(x > y)) abort 1;
      spec {
          assert x > y;
      }
  }
  ```

# The Boogie Language {.title} 

# Boogie: State, Procedures and Implementations

```boogie
const e : int;
const f : [int] int;

// Find a 'k' such that 'f[k] == e'
procedure Find(a: int, b: int)
    returns (k: int) ;
  requires a <= b;
  ensures f[k] == e || k == -1 ;

implementation Find(a: int, b: int) returns (k: int)
{
    if (f[a] == e) { k := a;    return; }
    if (a == b)    { k := -1;   return; }
    call k := Find(a + 1, b);
    return ;
}

implementation Find(a: int, b: int) returns (k: int)
{
    assume f[k] == e;
    return;
}
```

----

This is equivalent to the following K specification:

```
configuration <k> .K </k>
              <E> ?_:Int </E>
              <f> ?_:Map{Int, Int} </f>

rule ...
rule ...
rule ...
rule ...

claim <k> Find(A, B) => K ... </k>
      <E> E </E>
      <f> F </f>
  requires A <=Int B
  ensures  F[K] ==Int E orBool K ==Int -1
```

# Boogie: When does a program succeed?

A Boogie program is sucessful when every trace
is proved to never reach a failing assertion

- `assert` statement
- `ensures` clause
- `invariant` clause



# Boogie: `assert` statements

* `assert <Expression>`
* `assert(x != 0);`
* Similar to assertions in other imperative languages.
* Terminates a program (unsuccessfully) if `<Expression>` evaluates to `false`.

# Boogie: `assume` statements

* `assume <Expression>` or `axiom <Expression>` in global scope.
* Ignores a trace if `<Expression>` evaluates to `false`.
* ```
  implementation Find(a: int, b: int) returns (k: int)
  {
      assume f[k] == e;
      return;
  }
  ```


# Boogie: `call` statements

* Doesn't need an implementation

* ```
  procedure Split(totsec: int) returns (hours, minutes, seconds: int);
    requires totsec >= 0;
    ensures hours * 3600 + minutes * 60 + seconds == totsec;
    ensures 0 <= seconds && seconds < 60;
    ensures 0 <= minutes && minutes < 60;
  
  // Example calls to Split
  procedure main() returns (hours1, minutes1, seconds1,
                            hours2, minutes2, seconds2,
                            hours3, minutes3, seconds3: int)
  {
    call hours1, minutes1, seconds1 := Split(0);
    call hours2, minutes2, seconds2 := Split(11720);     // 3 h 15 min 20 sec
    call hours3, minutes3, seconds3 := Split(31536000);  // a year
  }
  ```
 
# Boogie: `goto` statements

Non-deterministic control flow.

```
implementation LESS(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume x >= y;
  z := false;
  return;
}
```

# Boogie: `goto` statements

Non-deterministic control flow.

```
implementation LESS(x: int, y: int) returns (z: bool)
{
start:
  goto yes, no;
yes:
  assume x < y;
  z := true;
  return;
no:
  assume x >= y;
  z := false;
  return;
}
```

# Boogie: `while` statements and invariants

```
procedure sum(n : int) returns (sum : int)
    requires n >= 0 ;
    ensures  sum == n * (n - 1) div 2 ;
{
    var rem : int;
    sum := 0 ; rem := n ;
    while (rem > 0)
        invariant sum + (rem * (rem-1)) div 2 == (n * (n-1)) div 2 ;
        invariant rem >= 0;
    {
        rem := rem - 1;
        sum := sum + rem;
    }
}
```

# Boogie: Quantification

* In  K, we may define lemmas about functions.
* Boogie, instead, lets us use quantification:

  ```
  const lessThan[int,int]bool;
  axiom (forall x:int :: ! lessThan[x, x] );
  ```

* Arbitary quantifier alternation allowed.

# KBoogie

# KBoogie: Difficulties

1. `kprove` does not support adding claims on the dynamically
2. Quantifiers in Boogie bind language expressions (rather than functional patterns)

# Assert & Assume

```
rule <k> assert true ; => .K       ... </k>
rule <k> assert false; => #failure ... </k>
```

```
rule <k> assume true ; => .K      ... </k>
rule <k> assume false; => #Bottom ... </k>
```

Another possible implementation:

```
rule <k> assert B:Bool ; => .K ... </k> requires B
rule <k> assume B:Bool ; => .K ... </k> ensures  B
```

# Labels & `goto` statements

First, build a table of labels and the corresponding code:

```
label_1:                            <k> goto label_1 </k>
    Body_1                          <labels>
label_2:                                label_1 |-> Body_1
    Body_2                   ==>        label_2 |-> Body_2
  ...                                   ...
label_n:                                label_N |-> Body_N
    Body_N                          <labels> 
```

Then, non-deterministically jump to the correct code:

```
    rule <k> (goto L, Ls ; ~> _) => (Stmts) </k>
         <labels> L |-> Stmts ... </labels>
    rule <k> goto L, Ls ; => goto Ls ; ... </k>
      requires Ls =/=K .IdList
```

# Loops and invariants

```
while (rem > 0)
    invariant sum + (rem * (rem-1)) div 2 == (n * (n-1)) div 2 ;
    invariant rem >= 0;
{
    rem := rem - 1;
    sum := sum + rem;
}
```

is transformed to:

```
  sum := 0;
  rem := n;
  goto LoopHead;

LoopHead:  // cut point
  assert 0 <= rem && 0 <= sum;                      // }
  assert 2 * sum + rem * (rem - 1) == n * (n - 1);  // } Invariant
  assert rem >= 0;                                  // }
  goto LoopDone, LoopBody;

LoopBody:
  assume rem > 0;
  rem := rem - 1;
  sum := sum + rem;
  goto LoopHead;

LoopDone:
  assume 0 >= rem;
  return;
```

Ordinarily, we would prove this by adding a circularity:

```
claim <k> goto LoopHead => return; </k>
      <labels> ... </labels>
      <locals> Old => New </locals>
  requires Invariant(Old)
```

# KBoogie: Cutpoints

```
  sum := 0;
  rem := n;
  goto LoopHead;

LoopHead:
  cutpoint(!Id, Invariant) ;
  goto LoopDone, LoopBody;

LoopBody:
  assume rem > 0;
  rem := rem - 1;
  sum := sum + rem;
  goto LoopHead;

LoopDone:
  assume 0 >= rem;
  return;
```

# KBoogie: Cutpoints

Emulating `claims`/circularities using `krun`.

First time round:

```verification
    rule <k> cutpoint(Id, Invariant) ;
          => assert(Invariant); // Subsumption/requires clause check
          ~> #generalize(Rho)   // Replace variables with fresh values
          ~> assume(Invariant); // Assume that the invariant holds
             ...
         </k>
         <locals> Rho </locals>
         <cutpoints> (.List => ListItem(I)) Cutpoints </cutpoints>
      requires notBool I in Cutpoints
```

Second time we reach a cutpoint:

```verification
    rule <k> cutpoint(I) ; => assume .AttributeList (false); ... </k>
         <cutpoints> Cutpoints </cutpoints>
      requires I in Cutpoints
```

# KBoogie: Cutpoints: Ideal situation

Dynamically create new circularities:

```
  claim <k> cutpoint(Id, Invariant) => return; </k>
        <locals> Old => ?New </locals>
    requires [[ <k> Invariant =>* true </k> ]]
    [claim_id(Id)]
```


# KBoogie: Quantifiers

* K gives us access to matching logic's `\forall` using the syntax `#Forall`
* These requires the bound expression to be functional patterns!

# KBoogie: Quantifiers

Want to transform configuration:

```
<k> (forall x :: f(x, y) > 3) ~>  Rest </k>
<locals> y |-> 27 </locals>
```

into:

```
    <k> Rest </k>
    <locals> y |-> 27 </locals>
#And
    #Forall X . lookup(f, X, 27) >Int 3
```

# KBoogie: Quantifiers: Ideal situation

```
rule <k> (forall x :: Exp) => true ... </k>
     <locals> Locals </locals>
  requires <k> Exp =>* true ... </k>
           <locals> Locals[x <- ?X] </locals>

rule <k> (forall x :: Exp) => false ... </k>
     <locals> Locals </locals>
  [owise]
```

* This is OK, because expressions have a deterministic, finite evaluation.
* This is not the same as if corresponding reachability claim succeeds.

# KBoogie: Quantifiers: Implementation

We use a "custom frontend" to implement this.

:::columns
::::column
1. Run program until it gets stuck at a quantifier.
2. Evaluate the expression until to a Boolean value
3. Combine the path conditions with the value into a closed form expression
4. Replace this into the original context
::::
::::column
![](../../docs/forall-example.svg)
::::
:::

# KBoogie: Quantifiers: Implementation

![](../../docs/forall-implementation.svg)

# Next steps

* Annotations and specifications (with quantifiers etc) for other languages
* Could we build the tools for implementing quantifiers into K?
