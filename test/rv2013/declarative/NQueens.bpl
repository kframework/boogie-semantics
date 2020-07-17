// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  The N-Queens puzzle.
*/

// Size of the board
const N: int;
axiom N == 8;

// Is i a valid row or column index?
function validPos(i: int): bool
{ 0 <= i && i < N }

// Are positions (i1, j2) and (i2, j2) on the same diagonal?
function sameDiagonal(i1, j1, i2, j2: int): bool
{ i2 - i1 == j2 - j1 || i2 - i1 == j1 - j2 }

// Dummy procedure that forces initialization of a[0..N)
procedure Touch(a: [int] int, n: int) returns ()
{
  var i, dummy: int;
  i := 0;
  while (i < N) {
    dummy := a[i];
    i := i + 1;
  }
}

// Generate a solution to the puzzle
// For each row i, queens[i] stores a queens column
procedure main() returns (queens: [int] int)
{
  var res: int;
  assume (forall i: int :: validPos(i) ==> validPos(queens[i])); // all columns within the board
  assume (forall i, j: int :: validPos(i) && validPos(j) && i != j ==> queens[i] != queens[j]); // none of the queens share a column
  assume (forall i, j: int :: validPos(i) && validPos(j) && i != j ==> !sameDiagonal(i, queens[i], j, queens[j])); // none of the queens share a diagonal
  call Touch(queens, N);
}
