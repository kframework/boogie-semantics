
procedure main() returns () {
    var input: int;
    var squared: int;

    havoc input; 
    squared := input * input;

    assert squared >= input;
    assert squared >= 0;
}
