procedure main ()
          returns ()
{
  var inc : int ;
  inc := 100;
  while (*) invariant inc > 99; {
      inc:= inc + 5;
  }
  assert inc > 99;
}
