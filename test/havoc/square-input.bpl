
procedure main() returns () {
    var input: int;
    var squared: int;

    havoc input; 
    squared := input * input;

    assert { :source __FILE__ , __LINE__ } squared >= input;
    assert { :source __FILE__ , __LINE__ } squared >= 0;
}
