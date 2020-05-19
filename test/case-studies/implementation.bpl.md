Multiple Procedure Implementations
----------------------------------

This program demonstrations Boogie's feature of defining multiple
implementations of the same procedure, and being able to verify that
each of the implementations satisfies the required specification.

```boogie
procedure p0(x: int, y: int) returns (z: int); ensures z >= 5;

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


procedure main() returns () {
    var z: int;
    call z := p0(27, 3);

    assert { :source __FILE__ , __LINE__ } z >= 5;

}
```
