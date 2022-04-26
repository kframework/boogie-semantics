procedure jumpIntoLoop() 
{
    while (false) {
        foo:
            assert false; // Error
    }
    goto foo;
}

procedure breakDoesNotMaintainInvariant() {
    while (true)
        invariant false; // Error
    {
        break;
    }
}

procedure breakDoesAssumeNotCond()
{
    var x : int;
    x := 0 ;
    while (x < 5)
        invariant x <= 5 ;
    { break ; }
    assert x >= 5; // Error
}
