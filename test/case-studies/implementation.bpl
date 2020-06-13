// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure p0(x: int, y: int) returns (z: int); requires true ; ensures z >= 5;

implementation p0(x: int, y: int) returns (z: int)
{
    z := 5;
    return;
}

implementation p0(x: int, y: int) returns (z: int)
{
    z := 6;
    return;
}

implementation p0(x: int, y: int) returns (z: int)
{
    z := 0;
    return; // ensures fails
}

implementation p0(x: int, y: int) returns (z: int)
{
    return; // ensures fails
}

procedure main() returns ()
    requires true;
    ensures true;
{
    var z: int;
    call z := p0(27, 3);
    assert  z >= 5;
    assert  z <= 7; // fail
}
