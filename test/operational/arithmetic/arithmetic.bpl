// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure main() returns () {
    var a: int;
    var b: int; 
    var c: int;
    var d: int; 

    a:= 5;
    b:= 7; 
    c:= 13;
    d:= 20;

    assert  a + b == 12;
    assert  d - c == b;
    assert  (a * b) + (a * d) - c == 122;  

}

