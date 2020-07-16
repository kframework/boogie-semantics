// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"


procedure main() returns () {

    var w: int;
    w:= 0;
    goto B;
    A: 
        w:= 1;
    B: 
        w:= 2;
    C: 
        w:= 3;
    END:

    assert  w == 3;

}

