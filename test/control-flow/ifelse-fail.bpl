
procedure main() returns () {

    var a: int;
    var y: int;
    y:= 100;
    a:= 0;

    if (*) {
        a:= 300;
    }
    assert { :code "BP5001" } { :source __LINE__ }  a == 300; // Fail

    if (y > 150) {
        a:= 1;
    } else if (y > 50) {
        a:= 2;
    }
    assert { :code "BP5001" } { :source __LINE__ }  a >= 1; 

    if (y > 150) {
        a:= 1;
    } else if (y > 125) {
        a:= 2;
    } else {
        a:= 3;
    }
    assert { :code "BP5001" } { :source __LINE__ }  a == 2; // Fail

}

