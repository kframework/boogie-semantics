/*
  Verbal arithmetic puzzle: find digits that correspond to letters so that the following equalition holds
      S E N D
    + M O R E
  -----------
  = M O N E Y
  Original example from "Koksal, Kuncak, Suter: Constraints as Control (POPL'12)"
*/

const unique s, e, n, d, m, o, r, y: int;
const N, fstLine, sndLine, total: int;
const letters: [int] int;

// Is n a base-10 digit?
function isDigit(n: int): bool
{ 0 <= n && n <= 9 }

// Solve the puzzle
procedure main() returns ()
{
  assume N == 8;
  assume letters[0] == s;
  assume letters[1] == e;
  assume letters[2] == n;
  assume letters[3] == d;
  assume letters[4] == m;
  assume letters[5] == o;
  assume letters[6] == r;
  assume letters[7] == y;

  assume (forall i: int :: 0 <= i && i < N ==> isDigit(letters[i]));
  assume s > 0 && m > 0;
  assume fstLine == s*1000 + e*100 + n*10 + d;
  assume sndLine == m*1000 + o*100 + r*10 + e;
  assume total == m*10000 + o*1000 + n*100 + e*10 + y;
  assume fstLine + sndLine == total;
}