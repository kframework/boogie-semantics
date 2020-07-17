/*
  Bubble Sort, where the specification says the output is a permutation of the input.
  Permutation-related loop invariants are missing.
  Original example from the Boogie repository.
  
  Errors:
  - Incorrect swapping
*/

// Array length
const N: int;

// Array elements
var a: [int] int;

// Is the array a[0..N) sorted?
function isSorted(a: [int] int, N: int): bool
{ (forall i, j: int :: 0 <= i && i <= j && j < N ==> a[i] <= a[j]) }

// Bubble sort
procedure BubbleSort() returns (perm: [int]int)
  modifies a;
  // array size is non-negative
  requires 0 <= N;
  // array is sorted
  ensures isSorted(a, N); // (forall i, j: int :: 0 <= i && i <= j && j < N ==> a[i] <= a[j]);
  // perm is a permutation
  ensures (forall i: int :: 0 <= i && i < N ==> 0 <= perm[i] && perm[i] < N);
  ensures (forall i, j: int :: 0 <= i && i < j && j < N ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: 0 <= i && i < N ==> a[i] == old(a)[perm[i]]);
{
  var n, p, tmp: int;  
  
  n := 0;
  while (n < N)
    invariant 0 <= n && n <= N;
  {
    perm[n] := n;
    n := n + 1;
  }
  
  while (true)
    invariant 0 <= n && n <= N;
    // array is sorted from n onwards
    invariant (forall i, k: int :: n <= i && i < N && 0 <= k && k < i ==> a[k] <= a[i]);
  {
    n := n - 1;
    if (n < 0) {
      break;
    }

    p := 0;
    while (p < n)
      invariant p <= n;
      // array is sorted from n+1 onwards
      invariant (forall i, k: int :: n+1 <= i && i < N && 0 <= k && k < i ==> a[k] <= a[i]);
      invariant (forall k: int :: 0 <= k && k < p ==> a[k] <= a[p]);
    {
      if (a[p+1] < a[p]) {
        a[p] := a[p + 1]; a[p + 1] := a[p]; // error here
        perm[p] := perm[p+1];  perm[p+1] := perm[p]; // error here
      }

      p := p + 1;
    }
  }
}