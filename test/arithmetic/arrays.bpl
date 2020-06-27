// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure P0()
{
    var x : [int] int;
    var y : [int] int;

    x := y;
    assume(x[0] == 3);
    assert(y[0] == 3);  // Succeeds
}

procedure P1()
{
    var x : [int] int;
    var y : [int] int;

    x := y;
    x[0] := 3;
    assert(y[0] == 3);  // Fails
}
