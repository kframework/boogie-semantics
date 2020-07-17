/*
  Generating primes defined with recursive constraints.
  Original example from "Koksal, Kuncak, Suter: Constraints as Control (POPL'12)"
*/

// Does none of [from, j) divide j?
function noneDivides(from, j: int): bool
{ if from == j then true else j mod from != 0 && noneDivides(from + 1, j) }

// Is i prime?
function isPrime(i: int): bool
{ i >= 2 && noneDivides(2, i) }


procedure PrimeGreater(i: int) returns (x: int);
  ensures isPrime(x);
  ensures x > i;

procedure main() returns (a: [int] int)
{
  var last, i: int;
  last := 0;
  i := 0;

  while (i < 8)
  {
    call last := PrimeGreater(last);
    a[i] := last;
    i := i + 1;
  }
}
