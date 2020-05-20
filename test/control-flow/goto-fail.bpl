

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

    assert { :code "BP5001" } { :source __LINE__ }  w == 3;

}

