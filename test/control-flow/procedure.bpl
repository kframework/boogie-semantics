

procedure p0(x: int, y: int) returns (z: int) requires true ; ensures z == 5;
{
    z := 5;
    return;
}


procedure main() returns () {
    var z: int;
    call z := p0(27, 3);

    assert { :code "BP5001" } { :source __LINE__ }  z == 5;

}

