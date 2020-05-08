
procedure main() returns () {
    var input: int; // where input > 0;
    var squared: int;

    havoc input;
    assume input != 0;
    assert { :source __FILE__ , __LINE__ } input != 0; 
    squared := input * input;

    assert { :source __FILE__ , __LINE__ } squared >= input;
    assert { :source __FILE__ , __LINE__ } squared >= 0;
}
