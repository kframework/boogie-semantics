
procedure main() returns () {
    var a: int;
    var b: int; 
    var c: int;
    var d: int; 

    a:= 5;
    b:= 7; 
    c:= 13;
    d:= 20;

    assert { :code "BP5001" } { :source __LINE__ }  a + b == 12;
    assert { :code "BP5001" } { :source __LINE__ }  d - c == b;
    assert { :code "BP5001" } { :source __LINE__ }  (a * b) + (a * d) - c == 122;  

}

