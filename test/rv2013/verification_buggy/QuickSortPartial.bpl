/*
  Quick Sort with partial implementation:
  implementation of Partition is missing; in return its specification is complete.
  
  Errors:
  - Postcondition too weak in Partition: it does not guarantee that the pivot found its final position 
*/

// Array length
const N: int;

// Array elements
var a: [int] int;

// Is the array a[lower..upper) sorted?
function isSorted(a: [int] int, lower, upper: int): bool
{ (forall i, j: int :: lower <= i && i <= j && j < upper ==> a[i] <= a[j]) }

// a[lower..upper) <= pivot
function leqPivot(pivot: int, a: [int] int, lower, upper: int): bool
{ (forall k: int :: lower <= k && k < upper ==> a[k] <= pivot) }

// a[lower..upper) >= pivot
function geqPivot(pivot: int, a: [int] int, lower, upper: int): bool
{ (forall k: int :: lower <= k && k < upper ==> pivot <= a[k]) }

// Partition the array a[lower, upper) such that all elements of a[lower, index) are <= pivot
// and all elements of a[index, upper) are >= pivot
procedure Partition(lower, upper, pivot: int) returns (index: int, perm: [int] int);
  modifies a;
  requires lower < upper;
	ensures lower <= index && index <= upper;
	ensures leqPivot (pivot, a, lower, index);
	ensures geqPivot (pivot, a, index, upper);
  // perm is a permutation
  ensures (forall i: int :: lower <= i && i < upper ==> lower <= perm[i] && perm[i] < upper);
  ensures (forall i, j: int :: lower <= i && i < j && j < upper ==> perm[i] != perm[j]);
  // the final array is that permutation of the input array
  ensures (forall i: int :: lower <= i && i < upper ==> a[i] == old(a)[perm[i]]);
  // outside of [lower, upper) a is unchanged
  ensures (forall i: int :: 0 <= i && i < lower ==> a[i] == old(a[i]));
  ensures (forall i: int :: upper <= i && i < N ==> a[i] == old(a[i]));
  

// Sort the array a[lower, upper)
procedure QuickSort(lower, upper: int)
  requires 0 <= lower && lower <= upper && upper <= N; 
  modifies a;
  ensures isSorted(a, lower, upper);
{
  var pivotIndex: int;
  var _: [int] int;
  
  if (lower < upper - 1) {
    pivotIndex := (lower + upper) div 2;
    call pivotIndex, _ := Partition(lower, upper, a[pivotIndex]);
    call QuickSort(lower, pivotIndex);
    call QuickSort(pivotIndex + 1, upper);
  }
}