

procedure main() returns () {
    var it: int;
    var inc: int; 
    it:=0;
    inc:=0;

    while (it < 1000) {
        inc:= inc + 5;
    }

    assert inc == 5000;
}

