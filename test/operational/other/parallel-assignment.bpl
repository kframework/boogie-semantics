// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure main() returns () {

    var w: int;
    var x: int;

    w, x := 2, 4;

    assert w == 2;
    assert x == 4;
}

