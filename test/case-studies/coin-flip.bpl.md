## Coin flip

This program demonstrates traditional `while` loops, non-deterministic choice
and `invariant` specifications.

```boogie
procedure main() returns () {
    var numFlips: int;
    var iter: int;
    var heads: int; 
    var tails: int;
    numFlips:=4;
    iter:=0;
    heads:=0;
    tails:=0;

    while (iter != numFlips)
      invariant heads + tails == iter;
    {
        iter := iter + 1;
        if (*) {
            heads := heads + 1;
        } else {
            tails := tails + 1;
        }
    }

    assert { :code "BP5001" } { :source __LINE__ }  heads + tails == numFlips;
}
```
