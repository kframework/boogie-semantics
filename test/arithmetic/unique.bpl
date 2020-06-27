// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"

type foo ;
const x : foo ;
const y : foo ;

const unique a : foo ;
const unique b : foo ;

procedure P0 ()
{
    assert x == y ; // Fails
    assert x != y ; // Fails
}

procedure P1 ()
{
    assert x == a ; // Fails
    assert x != a ; // Fails
}

procedure P2 ()
{
    assert a != b ;
    assert a == b ; // Fails
}
