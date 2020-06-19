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

procedure P4()
{
  var x: int where 0 <= x;
  var y: int where x <= y;

  havoc x, y;  // both at the same time
  assert 0 <= x && x <= y;
  havoc y, x;  // or in the other order
  assert 0 <= x && x <= y;

  assert x == 7;  // error
}

procedure R2()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  x := 5;
  y := 10;
  while (*) {
    w := w + 1;
    assert w == 6;
    y := y + 2;
    assert 7 <= y;
  }
  assert x == 5 && 0 <= y - w;
  assert y == 10;  // error
}

procedure R3()
{
  var w: int where w == x;
  var x: int where 0 <= x;
  var y: int where x <= y;

  // change w and x
  y := 10;
  while (*) {
    w := w;  x := x;
  }
  assert w == x;
  assert 0 <= x;
  assert y == 10;
  assert w <= 10;  // error
}
