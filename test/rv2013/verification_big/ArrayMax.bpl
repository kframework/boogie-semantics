// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  Maximum in an array.
  Loop invariant is omitted, which prevents Boogie from verifying the example.
*/

// Iteratively compute the maximum element of the array a[0..N)
procedure Max(a:[int] int, N: int) returns (max: int)
  requires N > 0;
  ensures (forall j: int :: 0 <= j && j < N ==> a[j] <= max);
  ensures (exists j: int :: 0 <= j && j < N && a[j] == max);
{
  var i: int;
  i := 0;
  max := a[0];
  while (i < N)
  {
    if (a[i] > max) {
      max := a[i];
    }
    i := i + 1;
  }
}

// Inputs to Max
const N: int;
const a: [int] int;

// One way to call Max
procedure main() returns (max: int)
{
  assume N >= 30;
  call max := Max(a, N);
}
