Since K's haskell backend does not support fresh constants in functions,
we implement a system of our own based on a strings of integers.

For each occurance of a recursive function that needs fresh values in a rule,
we pass in `next(FreshGenerator, N)` where `N` is an integer constant that only occurs
once in that rule.

```k
module FRESH-GENERATOR
    imports INT
    imports ID
    imports STRING

    syntax FreshGenerator ::= List{Int, ","} [klabel(FreshGenerator)]
    syntax FreshGenerator ::= next(FreshGenerator, Int) [function]
    rule next(FG, I) => I,FG

    syntax Id ::= id(String, FreshGenerator) [function]
    rule id(Prefix, .FreshGenerator) => String2Id(Prefix)
    rule id(Prefix, F, Fs) => id(Prefix +String "_" +String Int2String(F), Fs)
endmodule
```
