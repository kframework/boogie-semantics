// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  Naive computation of Fibonacci numbers using a recursive procedure.
  An assertion defines the semantics using a recursive function.
  The postcondition of ComputeFib is missing, so Boogie cannot prove the assertion.

  The {:inline N} attribute instructs Boogie to inliine a procedure N times;
  inlining allows Boogie to prove the assertion,
  but scales poorly and starting from N == 8 causes a stack overflow.
*/


// n-th Fibonacci number
function fib(n: int): int;
axiom fib(0) == 0;
axiom fib(1) == 1;
axiom (forall n: int :: n > 1 ==> fib(n) == fib(n - 2) + fib(n - 1));


// Compute n-th Fibonacci number
procedure {:inline 8} ComputeFib(n: int) returns (res: int)
  requires n >= 0;
{
  var f1, f2: int;
  if (n > 1) {
    call f1 := ComputeFib(n - 1);
    call f2 := ComputeFib(n - 2);
    res := f1 + f2;
  } else {
    res := n;
  }
}

// One way to call ComputeFib
procedure main(n: int) returns (fib: int)
  requires n >= 8;
{
  call fib := ComputeFib(n);
  assert fib == fib(n);
}

