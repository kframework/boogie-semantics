// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure main ()
          returns ()
{
  var inc : int ;
  inc := 100;
  while (*) invariant inc < 200; // fail
  {
      inc:= inc + 5;
  }
  assert inc > 100; // fail
}
