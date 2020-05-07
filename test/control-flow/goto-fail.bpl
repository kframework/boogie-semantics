

procedure main() returns () {

    var w: int;
    w:= 0;
    goto B;
    A: 
        w:= 1;
        goto END;
    B: 
        w:= 2;
        goto END;
    C: 
        w:= 3;
    END:

    assert { :source __FILE__ , __LINE__ } w == 3;

}

