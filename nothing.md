Quite a few Boogie contructs have, often multiple, "optional" parts. The
`Nothing` modules below make using the empty token in these productions easier,
with a different syntax for parsing programs and for parsing rules.

```k
module NOTHING-COMMON-SYNTAX
    syntax Nothing
endmodule

module NOTHING-PROGRAM-SYNTAX
    imports NOTHING-COMMON-SYNTAX
    syntax Nothing ::= "" [klabel(Nothing), symbol]
endmodule

module NOTHING-RULE-SYNTAX
    imports NOTHING-COMMON-SYNTAX
    syntax Nothing ::= ".Nothing" [klabel(Nothing), symbol]
endmodule
```
