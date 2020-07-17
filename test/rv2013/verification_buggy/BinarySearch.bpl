/*
  Binary Search.
  Original example from the Boogie repository.
  
  Errors:
  - Out of bounds when N == 0.
  - Gives a wrong answer (not found) whenever in the last iteration a[index] == value but index == high.
  Error ideas borrowed from "Richard E Pattis: Textbook errors in binary searching (1988)
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
  var low, high: int;
  low, high := 0, N - 1;
  while (true)    
  {
    index := (low + high) div 2;
    assert 0 <= index && index < N; // Language-enforced
    if (value < a[index]) {
      high := index - 1;      
    } else {
      low := index + 1;
    }
    if (low > high || value == a[index]) {
      break;
    }
  }
  if (low > high) {
    index := N; // not found
  }
}