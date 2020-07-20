// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure square(w: int) returns (z: int) requires true ; ensures z == w * w;
{
    z := w * w;
    return;
}

procedure main() returns () {
    var w: int;
    w := 5;
    call w := square(w);
    assert  w == 25;

}
