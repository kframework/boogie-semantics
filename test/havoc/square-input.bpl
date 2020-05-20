
procedure main() returns () {
    var input: int; // where input > 0;
    var squared: int;

    havoc input;
    assume input != 0;
    assert { :code "BP5001" } { :source __LINE__ }  input != 0; 
    squared := input * input;

    assert { :code "BP5001" } { :source __LINE__ }  squared >= input;
    assert { :code "BP5001" } { :source __LINE__ }  squared >= 0;
}
