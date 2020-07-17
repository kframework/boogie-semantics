/*
  Quick Sort with partial specification (does not say the output is a permutation of the input, loop invariants are missing).
  
  Errors:
  - Wrong implementation and postcondition of Partition: it does not guarantee that the pivot found its final position 
  and does not do any progress on two unsorted elements 
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
					
// Swap a[i] and a[j]          
procedure Swap(i: int, j: int) returns ()
  modifies a;
	// elements in positions i,j are swapped
	ensures a[i] == old(a[j])  &&  a[j] == old(a[i]);
	// all other elements are unchanged
	ensures (forall k: int :: k != i && k != j ==> a[k] == old(a[k]));
{
	var tmp: int;
	
	tmp := a[i];
	a[i] := a[j];
	a[j] := tmp;
}

// Partition the array a[lower, upper) such that all elements of a[lower, index) are <= pivot
// and all elements of a[index, upper) are >= pivot
procedure Partition(lower, upper, pivotIndex: int) returns (index: int)
  modifies a;
  requires lower < upper - 1;
	ensures lower <= index && index < upper;
	ensures leqPivot (old(a[pivotIndex]), a, lower, index);
	ensures geqPivot (old(a[pivotIndex]), a, index, upper);
{
  var left, right, pivot: int;
  left, right, pivot := lower, upper - 1, a[pivotIndex];
	while (left != right) {
		while (left != right && a[left] <= pivot) {
			left := left + 1;
		}
		while (left != right && pivot <= a[right]) {
			right := right - 1;
		}		
		call Swap(left, right);
	}
	
	if (pivot <= a[left]) {
    index := left;
	} else {
    index := left + 1;
  }  
}

// Sort the array a[lower, upper)
procedure QuickSort(lower, upper: int)
  requires lower <= upper;
  modifies a;
  ensures isSorted(a, lower, upper);
{
  var pivotIndex: int;
  if (lower < upper - 1) {
    pivotIndex := (lower + upper) div 2;
    
    call pivotIndex := Partition(lower, upper, pivotIndex);
    call QuickSort(lower, pivotIndex);
    call QuickSort(pivotIndex + 1, upper);
  }
}