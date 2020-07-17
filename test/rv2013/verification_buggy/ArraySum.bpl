/*
  Sum of array elements, with the semantics of sum defined recursively.
  
  Errors:
  - The implementation assumes 1-based arrays, while the specification assumes 0-based arrays.
*/

// Sum of N elements of array a
function recSum(a: [int] int, N: int) returns (int)
{ if N == 0 then 0 else recSum(a, N - 1) + a[N - 1] }

// Iteratively compute the sum of array elements.
procedure Sum(a: [int] int, N: int) returns (sum: int)
  requires 1 <= N;
  ensures recSum(a, N) == sum;
{
  var i: int;
  i, sum := 1, 0;
  while (i < N)
  {
    sum := sum + a[i];
    i := i + 1;
  }
}
