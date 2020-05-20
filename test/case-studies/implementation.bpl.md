Multiple Procedure Implementations
----------------------------------

This program demonstrations Boogie's feature of defining multiple
implementations of the same procedure, and being able to verify that
each of the implementations satisfies the required specification.

```boogie
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
    assert { :code "BP5001" } { :source __LINE__ }  z >= 5;
    assert { :code "BP5001" } { :source __LINE__ }  z <= 7; // fail
}
```
