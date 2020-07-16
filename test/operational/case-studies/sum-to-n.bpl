// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure main() returns () {
    var sumTo: int;
    var sum: int;
    var iter: int;
    sumTo:=20;
    sum:=0;
    iter:=0;

    while (iter != sumTo) invariant sum * 2 == iter * (iter + 1); {
        iter := iter + 1;
        sum := sum + iter;
    }

    assert  sum == 210;
}
