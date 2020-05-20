
procedure main() returns () {
    var a: int;
    var b: int; 

    a:= 5;
    b:= 6; 
    assert { :code "BP5001" } { :source __LINE__ }  a + b == 11;
}
