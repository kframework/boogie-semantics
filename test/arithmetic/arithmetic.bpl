
procedure main() returns () {
    var a: int;
    var b: int; 
    var c: int;
    var d: int; 

    a:= 5;
    b:= 7; 
    c:= 13;
    d:= 20;

    assert { :source __FILE__ , __LINE__ } a + b == 12;
    assert { :source __FILE__ , __LINE__ } d - c == b;
    assert { :source __FILE__ , __LINE__ } (a * b) + (a * d) - c == 122;  

}

