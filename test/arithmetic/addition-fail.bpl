
procedure main() returns () {
    var a: int;
    var b: int; 

    a:= 5;
    b:= 6; 
    assert { :source __FILE__ , __LINE__ } a + b == 200;
}