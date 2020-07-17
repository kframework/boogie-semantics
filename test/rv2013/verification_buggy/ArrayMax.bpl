/*
  Maximum in an array.
  
  Errors:
  - Precondition N > 0 is missing.
  - Initializing max with 0 is wrong when all elements of a are negative.
*/

// Iteratively compute the maximum element of the array a[0..N)
procedure Max(a:[int] int, N: int) returns (max: int)
  ensures (forall j: int :: 0 <= j && j < N ==> a[j] <= max);
  ensures (exists j: int :: 0 <= j && j < N && a[j] == max);
{
  var i: int;
  i := 0;
  max := 0;
  while (i < N) 
  {
    if (a[i] > max) {
      max := a[i];
    }
    i := i + 1;
  }
}