```k
module QUANTIFIABLE-BUILTINS
    imports INT
    imports ID

    syntax QInt ::= bound(Id) [smt-hook(#1)]
                  | Int
    syntax QBool ::= Bool

    syntax QInt  ::= QInt "+QInt" QInt [smt-hook(+)]
    syntax QBool ::= QInt ">QInt" QInt [smt-hook(>)]
endmodule
```
