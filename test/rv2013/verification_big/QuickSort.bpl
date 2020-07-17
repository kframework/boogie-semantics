/*
  Quick Sort with partial specification (does not say the output is a permutation of the input, loop invariants are missing).
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
  ensures old(a[pivotIndex]) == a[index];
	ensures leqPivot (a[index], a, lower, index);
	ensures geqPivot (a[index], a, index, upper);
{
  var i, pivot: int;
  index, i, pivot := lower, lower, a[pivotIndex];
  call Swap(pivotIndex, upper - 1); // Move pivot to the end

  while (i < upper - 1) {
    if (a[i] < pivot) {
      call Swap(i, index);
      index := index + 1;
    }
    i := i + 1;
  }
  call Swap(index, upper - 1);
}

// Sort the array a[lower, upper)
procedure QuickSort(lower, upper: int)
  requires 0 <= lower && lower <= upper && upper <= N;
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

// One way to call QuickSort
procedure main() returns ()
  modifies a;
{
  assume N == 7;
  assume !isSorted(a, 0, N);
  call QuickSort(0, N);
}
