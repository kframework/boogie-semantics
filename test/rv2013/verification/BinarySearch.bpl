/*
  Binary Search.
  Original example from the Boogie repository.
*/

// Is array a of length N sorted?
function sorted(a: [int] int, N: int): bool
{ (forall j, k: int :: 0 <= j && j < k && k < N ==> a[j] <= a[k]) }

// Efficiently search for value in a sorted array a of length N.
procedure BinarySearch(a: [int] int, N: int, value: int) returns (index: int)
  requires N >= 0;
  requires sorted(a, N);
  ensures 0 <= index && index <= N;
  ensures index < N ==> a[index] == value;                                      // If index is within bounds, value was found
  ensures index == N ==> (forall j: int :: 0 <= j && j < N ==> a[j] != value);  // If index is out of bounds, value does not occur
{
  var low, high, mid: int;
  low, high := 0, N;
  while (low < high)
    invariant 0 <= low && low <= high && high <= N;
    invariant (forall i: int :: 0 <= i && i < N && !(low <= i && i < high) ==> a[i] != value);
  {
    mid := (low + high) div 2;
    if (a[mid] < value) {
      low := mid + 1;
    } else if (value < a[mid]) {
      high := mid;
    } else {
      index := mid;
      return;
    }
  }
  index := N;
}

// Inputs to BinarySearch
const N: int;
const array: [int] int;
const value: int;

// One way to call BinarySearch
procedure main() returns (index: int)
{
  // Constrain the inputs to get an interesting test case.
  assume N == 10;
  assume (forall i, j: int :: 0 <= i && i < j && j < N ==> array[i] < array[j]); // Let all the values be distinct
  call index := BinarySearch(array, N, value);
}
