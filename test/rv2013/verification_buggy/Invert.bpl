/*
  Invert a permutation
  Example inspired by: 1st Verified Software Competition (https://sites.google.com/a/vscomp.org), problem II.
  
  Errors: 
  - Missing a precondition that all indexes be non-negative.
*/

procedure Invert (a: [int] int, N: int) returns (b: [int] int)
	requires 0 < N;
	requires (forall i: int :: 0 <= i && i < N ==> a[i] < N);
	requires (forall i, j: int :: 0 <= i && i < j && j < N ==> a[i] != a[j]);
	
	ensures (forall i: int :: 0 <= i && i < N ==> b[a[i]] == i);
	ensures (forall i, j: int :: 0 <= i && i < j && j < N ==> b[i] != b[j]);
{
	var k: int;
	k := 0;
	while (k < N)
		invariant (forall i: int :: 0 <= i && i < k ==> b[a[i]] == i);
	{
		b[a[k]] := k;
		k := k + 1;
	}	
}