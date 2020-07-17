/*
  Turing factorial with recursive specificaiton and unstructured control flow.
  Original example from the Boogie repository.
*/

// Compute factorial using only additions
procedure ComputeFactorial(n: int) returns (u: int)
  requires 1 <= n;
  ensures u == factorial(n);
{
  var r, v, s: int;
  r, u := 1, 1;
TOP:  // B
  assert r <= n;
  assert u == factorial(r);
  v := u;
  if (n <= r) { return; }
  s := 1;
INNER:  // E
  assert s <= r;
  assert v == factorial(r) && u == s * factorial(r);
  u := u + v;
  s := s + 1;
  assert s - 1 <= r;
  if (s <= r) { goto INNER; }
  r := r + 1;
  goto TOP;
}

function factorial(int): int;
axiom factorial(0) == 1;
axiom (forall n: int :: 1 <= n ==> factorial(n) == n * factorial(n-1));

procedure main () returns (result: int)
{
  call result := ComputeFactorial(30);
}