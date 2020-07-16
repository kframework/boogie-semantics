// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

procedure main() returns () {
    var input: int; // where input > 0;
    var squared: int;

    havoc input;
    assume input != 0;
    assert  input != 0; 
    squared := input * input;

    assert  squared >= input;
    assert  squared >= 0;
}
