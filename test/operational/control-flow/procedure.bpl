// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure p0(x: int, y: int) returns (z: int) requires true ; ensures z == 5;
{
    z := 5;
    return;
}

procedure main() returns () {
    var w: int;
    call w := p0(27, 3);

    assert  w == 5;

}

var x : int;
procedure P() returns() modifies x; {
    x := 5;
    call P();
    assert(x == 5);
}

// From test2/Call: Parameters for the procedures have been renamed
// since the haskell backed doesn't support substitution

procedure Bar() returns (barresult: ref);

procedure Foo();

implementation Foo()
{
  var x: ref;

  entry:
    call x := Bar();
    assume x == null;
    call x := Bar();
    assert x == null; // error
    return;

}

procedure DifferentFormalNames(x: int, y: int) returns (z: int);
  requires x < y;
  ensures z == x;

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    assert x < y;
    z := x;
    return;
}

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    goto A, B;
  A:
    assert x < y;
    assume false;
    return;
  B:
    z := x;
    return;
}

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    assert y < x;  // error
    z := x;
    return;
}

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    z := y;
    return;  // error: postcondition violation
}

implementation DifferentFormalNames(x: int, y: int) returns (z: int)
{
  start:
    z := y;
    return;  // error: postcondition violation

}

type ref;
const null : ref;
