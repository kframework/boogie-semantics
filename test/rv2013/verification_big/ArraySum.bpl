/*
  Sum of array elements, with the semantics of sum defined recursively.
*/

// Sum of N elements of array a
function recSum(a: [int] int, N: int) returns (int)
{ if N == 0 then 0 else recSum(a, N - 1) + a[N - 1] }

// Iteratively compute the sum of array elements
procedure Sum(a: [int] int, N: int) returns (sum: int)
	requires 0 <= N;
  ensures recSum(a, N) == sum;
{
	var i: int;
	i, sum := 0, 0;
	while (i < N)
		invariant i <= N;
    invariant recSum(a, i) == sum;
	{
		sum := sum + a[i];
		i := i + 1;
	}
}

// Inputs to Sum
const N: int;
const a: [int] int;

// One way to call Sum
procedure main() returns (sum: int)
{
  assume N >= 30;
  call sum := Sum(a, N);
}