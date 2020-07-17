// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  Naive computation of Fibonacci numbers using a recursive procedure.
  An assertion defines the semantics using a recursive function.
  The postcondition of ComputeFib is missing, so Boogie cannot prove the assertion.

  The {:inline N} attribute instructs Boogie to inliine a procedure N times;
  inlining allows Boogie to prove the assertion,
  but scales poorly and starting from N == 8 causes a stack overflow.

  Error:
    - Wrong value for x == 0
*/

// n-th Fibonacci number
function fib(x: int): int;
axiom fib(0) == 0;
axiom fib(1) == 1;
axiom (forall x: int :: x > 1 ==> fib(x) == fib(x - 2) + fib(x - 1));

// Compute n-th Fibonacci number
procedure {:inline 8} ComputeFib(x: int) returns (res: int)
  requires x >= 0;
{
  var f1, f2: int;
  if (x > 1) {
    call f1 := ComputeFib(x - 1);
    call f2 := ComputeFib(x - 2);
    res := f1 + f2;
  } else {
    res := 1;
  }
}

// One way to call ComputeFib
procedure main(x: int) returns (fib: int)
  requires x >= 8;
{
  call fib := ComputeFib(x);
  assert fib == fib(x);
}

