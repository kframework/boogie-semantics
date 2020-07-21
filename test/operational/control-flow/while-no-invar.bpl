// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
procedure main() returns () {
    var it: int;
    var inc: int;
    var n : int;
    it:=0;
    inc:=0;
    n:=10;

    while (it != n)
    {
        inc := inc + 5;
        it := it + 1;
    }

    assert inc == 50;
}

