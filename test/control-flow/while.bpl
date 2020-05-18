procedure main() returns () {
    var it: int;
    var inc: int; 
    var n : int;
    it:=0;
    inc:=0;
    n:=10;

    while (it != n)
        invariant inc + 5*(n - it) == 5 * n;
    {
        inc := inc + 5;
        it := it + 1;
    }

    assert inc == 50;
}

