// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"


procedure p0(x: int, y: int) returns (z: int) requires true ; ensures z == 5;
{
    z := 5;
    return;
}


procedure main() returns () {
    var z: int;
    call z := p0(27, 3);

    assert  z == 5;

}

