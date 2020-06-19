// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

procedure P0()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  assert 0 <= x;
  assert x <= y;
  assert y < 5;  // error
}

procedure P1()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  havoc y;
  assert 5 <= y;

  havoc x;
  assert 0 <= x;
  assert x <= y;  // error
}

procedure P2()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  havoc y;  // y first
  havoc x;
  assert x <= y;  // error
}

procedure P3()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  havoc x;  // this time, x first
  havoc y;
  assert x <= y;  // yeah!
  assert 5 <= y;  // error
}

