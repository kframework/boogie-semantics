
procedure main() returns () {
    var sumTo: int;
    var sum: int; 
    var iter: int;
    sumTo:=101;
    sum:=0;
    iter:=1;

    while (iter != sumTo) invariant sum * 2 == (iter * (iter - 1)); {
        sum := sum + iter; 
        iter := iter + 1;
    }

    assert sum == 5050;
}

