/*
  Dutch flag problem.
  Original example by Carlo A. Furia from the loop invariant study.
  
  One of the postconditions of Swap is omitted.
  
  Error:
  - Off-by-one error in the initialization of r.
    
*/  

type array t = [int] t;

type COLOR;
const unique Blue, White, Red: COLOR;

function is_flag_color ( col: COLOR ) returns (bool)
{ col == Blue  ||  col == White  ||  col == Red }

type ARRAY_COLOR = array COLOR;

function is_flag_color_array ( A: ARRAY_COLOR, low: int, high: int) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  is_flag_color(A[i]) ) }

function monochrome ( A: ARRAY_COLOR, low: int, high: int, col: COLOR) returns (bool)
{ ( forall i: int :: low <= i && i <= high  ==>  A[i] == col ) }


procedure Swap <tt> (A: array tt, i : int, j: int) returns(B: array tt)
        // elements in positions i,j are swapped
        ensures (B[i] == A[j]  &&  B[j] == A[i]);
        // all other elements are unchanged
        // ensures (forall k: int :: k != i && k != j  ==>  B[k] == A[k]);
{
  var tmp: tt;

  B := A;
  tmp := B[i];
  B[i] := B[j];
  B[j] := tmp;
}


procedure MakeFlag (A: ARRAY_COLOR, n: int)
  returns (B: ARRAY_COLOR, b: int, r: int)
  requires n >= 1;
  requires is_flag_color_array(A, 1, n);
  ensures 1 <= b;
  ensures b <= r;
  ensures r <= n+1;
  ensures monochrome(B, 1, b-1, Blue);
  ensures monochrome(B, b, r-1, White);  
  ensures monochrome(B, r, n, Red);
{
  var i: int;

  B := A;
  b, i, r := 1, 1, n; // Error here: the value at r should refer to the first red value, initially this is not necessarily true, so it should be n + 1
  
  while ( i < r )
  {
    if (B[i] == Blue)
    {
      call B := Swap(B, b, i);
      i := i + 1;
      b := b + 1;
    }
    else
    {
      if (B[i] == White)
      {
        i := i + 1;
      }
      else
      {
        r := r - 1;
        call B := Swap(B, r, i);
      }
    }
  }
}

