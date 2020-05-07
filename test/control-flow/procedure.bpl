

procedure p0(x: int, y: int) returns (z: int)// ensures z == 5;
{
    z := 5;
    return;
}



procedure main() returns () {
    var z: int;
    call z := p0(27, 3);

    //// this assert { :source __FILE__ , __LINE__ }ion will fail unless we have 
    //// "ensures z == 5" on the procedure above
    // assert { :source __FILE__ , __LINE__ } z == 5;
}

