
procedure main() returns () {
    var in1: int;
    var in2: int;
    var max: int;

    havoc in1;
    havoc in2;

    if (in1 > in2) {
        max := in1;
    } else {
        max := in2;
    }

    assert { :code "BP5001" } { :source __LINE__ }  max >= in1;
    assert { :code "BP5001" } { :source __LINE__ }  max >= in2;
}
