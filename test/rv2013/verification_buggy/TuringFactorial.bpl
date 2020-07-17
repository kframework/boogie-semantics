/*
  Turing factorial with recursive specificaiton and unstructured control flow.
  Original example from the Boogie repository.
  
  Error:
  - Typo in the update of u.
*/

// Compute factorial using only additions
procedure ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == factorial(n);
{
  var r, v, s: int;
  r, u := 1, 1;
TOP:  // B
  v := u;
  if (n <= r) { return; }
  s := 1;
INNER:  // E
  u := u + u; // Error here: should be u + v; this works for n == 1 and n == 2, but fails after that.
  s := s + 1;
  if (s <= r) { goto INNER; }
  r := r + 1;
  goto TOP;
}

function factorial(int): int;
axiom factorial(0) == 1;
axiom (forall n: int :: 1 <= n ==> factorial(n) == n * factorial(n-1));
