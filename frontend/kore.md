KORE
====

This module defines the syntax of kore, a language representing matching logic
patterns, used by the various K utilities.

```k
module KORE
    imports STRING-SYNTAX
    imports KVAR-SYNTAX
    imports BUILTIN-ID-TOKENS

    syntax Sort ::= KVar "{" "}"
    syntax Symbol ::= KVar "{" Sorts "}"
    syntax Pattern ::= "\\dv" "{" Sort "}" "(" String ")"                           [klabel(\dv)]
                     | KVar ":" Sort                                                [klabel(variable)]
                     | Symbol "(" Patterns ")"                                      [klabel(application)]
                     | "\\not" "{" Sort "}" "(" Pattern ")"                         [klabel(\not)]
                     | "inj" "{" Sort "," Sort "}" "(" Pattern ")"                  [klabel(inj)]
                     | "\\ceil" "{" Sort "," Sort "}" "(" Pattern  ")"              [klabel(\ceil)]
                     | "\\equals" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")" [klabel(\equals)]
                     | "\\and" "{" Sort "}" "(" Pattern "," Pattern ")"             [klabel(\and)]
                     | "\\or" "{" Sort "}" "(" Pattern "," Pattern ")"              [klabel(\or)]
                     | "\\implies" "{" Sort "}" "(" Pattern "," Pattern ")"         [klabel(\implies)]
                     | "\\top" "{" Sort "}" "(" ")"                                 [klabel(\top)]
                     | "\\bottom" "{" Sort "}" "(" ")"                              [klabel(\bottom)]
                     | "\\forall" "{" Sort "}" "(" Pattern "," Pattern ")"          [klabel(\forall)]
                     | "\\exists" "{" Sort "}" "(" Pattern "," Pattern ")"          [klabel(\exists)]

    syntax Patterns ::= List{Pattern, ","} [klabel(Patterns)]
    syntax Sorts ::= List{Sort, ","}       [klabel(Sorts)]
endmodule

module KORE-SYNTAX
    imports KORE
    syntax KVar ::= r"[A-Za-z'-][A-Za-z'0-9-]*" [prec(2), token]
                  | #UpperId [token]
                  | #LowerId [token]
endmodule
```

`KORE-UNPARSE`
==============

```k
module KORE-UNPARSE
    imports KORE
    imports STRING
    imports BOOL
    imports K-EQUAL

    syntax String ::= unparsePattern(Pattern) [function, functional]
    rule unparsePattern(\equals { S1 , S2 } (P1, P2)) => "\\equals{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"
    rule unparsePattern(Var : Sort)                   => KVarToString(Var) +String ":" +String unparseSort(Sort)
    rule unparsePattern(\dv { S } (Value))            => "\\dv{" +String unparseSort(S)  +String "} (\"" +String Value +String "\")"
    rule unparsePattern(\top { S } ())                => "\\top{" +String unparseSort(S)  +String "} ()"
    rule unparsePattern(\bottom { S } ())             => "\\bottom{" +String unparseSort(S)  +String "} ()"
    rule unparsePattern(inj { S1 , S2 } (P1))         => "inj{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(\ceil { S1 , S2 } (P1))       => "\\ceil{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(\not { S1 } (P1))             => "\\not{" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(S(Args:Patterns))             => unparseSymbol(S) +String "(" +String unparsePatterns(Args) +String ")"
    rule unparsePattern(\and { S1 } (P1, P2))
      => "\\and{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\or { S1 } (P1, P2))
      => "\\or{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\implies { S1 } (P1, P2))
      => "\\implies{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\forall  { S1 } (P1, P2)) => "\\forall {" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"
    rule unparsePattern(\exists  { S1 } (P1, P2)) => "\\exists {" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"

    syntax String ::= KVarToString(KVar)         [function, functional, hook(STRING.token2string)]

    syntax String ::= unparseSort(Sort) [function, functional]
    rule unparseSort(KVar {}) => KVarToString(KVar) +String "{}"

    syntax String ::= unparseSymbol(Symbol) [function, functional]
    rule unparseSymbol(KVar {Sorts}) => KVarToString(KVar) +String "{" +String unparseSorts(Sorts) +String "}"

    syntax String ::= unparsePatterns(Patterns) [function, functional]
    rule unparsePatterns(P, Ps) => unparsePattern(P) +String "," +String unparsePatterns(Ps) requires notBool Ps ==K .Patterns
    rule unparsePatterns(P, .Patterns) => unparsePattern(P)
    rule unparsePatterns(.Patterns) => ""

    syntax String ::= unparseSorts(Sorts) [function, functional]
    rule unparseSorts(S, Ss) => unparseSort(S) +String "," +String unparseSorts(Ss) requires notBool Ss ==K .Sorts
    rule unparseSorts(S, .Sorts) => unparseSort(S)
    rule unparseSorts(.Sorts) => ""
endmodule
```

`KORE-PARSE`
============

```k
module KORE-PARSE
    imports IO-NONFUNCTIONAL
    imports KORE
    imports K-REFLECTION

    syntax PrePattern ::= Pattern
    syntax PrePattern ::= parse(input: PreString, parser: String)
                        | parseFile(filename: PreString, parser: String) [seqstrict(1), result(String)]
    rule parse(Program, Parser) => parseFile(writeTempFile(Program), Parser)
    rule parseFile(File, Parser) => parseKore(system(Parser +String " " +String File))

    syntax PrePattern ::= parseKore(PreString) [seqstrict(1), result(String)]
    rule parseKore(String) => #parseKORE(String):Pattern

endmodule
```

`KORE-HELPERS`
==============

Various generic library functions over kore.

```k
module KORE-UTILITIES
    imports KORE
    imports K-EQUAL
    imports KVAR
    imports STRING

    syntax KVar ::= freshVariable(Int) [function]
    rule freshVariable(I) => String2KVar("VDriver" +String Int2String(I))

    syntax Patterns ::= Patterns "+Patterns" Patterns [function, functional, left]
    rule (P1, P1s) +Patterns P2s => P1, (P1s +Patterns P2s)
    rule .Patterns +Patterns P2s =>                    P2s

    syntax Pattern ::= negatePredicate(Pattern) [function]
    rule negatePredicate(\top{S} ())          => \bottom{S}()
    rule negatePredicate(\bottom{S} ())       => \top{S}()
```

The Haskell backend has difficulty dealing with `\not(\equals)` in some cases, so lets avoid them

```k
    syntax KVar ::= "SortBool" [token]
    rule negatePredicate(\equals{S2, S}(P1, \dv{SortBool{}}("true"))) =>  \equals{S2, S}(P1, \dv{SortBool{}}("false"))
    rule negatePredicate(\equals{S2, S}(P1, \dv{SortBool{}}("false"))) => \equals{S2, S}(P1, \dv{SortBool{}}("true"))
    rule negatePredicate(\equals{S2, S}(P1, P2)) => \not{S}(\equals{S2, S}(P1, P2)) [owise]

    rule negatePredicate(\ceil{S2, S}  (P)) => \not{S}(\ceil{S2, S}(P))
    rule negatePredicate(\and{S} (P1, P2)) => \or{S}(negatePredicate(P1), negatePredicate(P2))
    rule negatePredicate(\or {S} (P1, P2)) => \and{S}(negatePredicate(P1), negatePredicate(P2))
    rule negatePredicate(\forall{S} (X, P)) => \exists{S} (X, negatePredicate(P))
    rule negatePredicate(\exists{S} (X, P)) => \forall{S} (X, negatePredicate(P))
    rule negatePredicate(\implies {S} (P1, P2)) => \and{S}(P1, negatePredicate(P2))
    rule negatePredicate(\not{_} (P)) => negatePredicate(P)

    syntax Pattern ::= changePredicateSort(Sort, Pattern) [function]
    rule changePredicateSort(Sort, \forall{_} (X, P) ) => \forall{Sort} (X, changePredicateSort(Sort, P))
    rule changePredicateSort(Sort, \exists{_} (X, P) ) => \exists{Sort} (X, changePredicateSort(Sort, P))
    rule changePredicateSort(Sort, \top{_} ())          => \top{Sort}()
    rule changePredicateSort(Sort, \equals{S2, _}(P1,P2)) => \equals{S2, Sort}(P1, P2)
    rule changePredicateSort(Sort, \ceil{S2, _}  (P)) => \ceil  {S2, Sort}(P)
    rule changePredicateSort(Sort, \and{_} (P1, P2) ) => \and{Sort}(changePredicateSort(Sort, P1), changePredicateSort(Sort, P2))
    rule changePredicateSort(Sort, \or {_} (P1, P2) ) => \or {Sort}(changePredicateSort(Sort, P1), changePredicateSort(Sort, P2))
    rule changePredicateSort(Sort, \implies {_} (P1, P2) ) => \implies {Sort}(changePredicateSort(Sort, P1), changePredicateSort(Sort, P2))
    rule changePredicateSort(Sort, \not{_} (P) ) => \not{Sort}(changePredicateSort(Sort, P))

    // Get predicate
    syntax Patterns ::= findSubTermsByConstructor(KVar, Pattern) [function]

    // Looks for a subterm within the term part constrained term
    syntax Patterns ::= findSubTermsByConstructor(KVar, Pattern) [function]
    rule findSubTermsByConstructor(Ctor, Ctor { .Sorts } ( Arg, .Patterns ) ) => Arg, .Patterns
    rule findSubTermsByConstructor(Ctor, S { _ } ( Args ) ) => findSubTermsByConstructorPs(Ctor, Args) requires S =/=K Ctor
    rule findSubTermsByConstructor(Ctor, inj{ _, _ } (P) ) => findSubTermsByConstructor(Ctor, P)
    rule findSubTermsByConstructor(Ctor, \and{ _ } (P1, P2) ) => findSubTermsByConstructorPs(Ctor, (P1, P2))

    rule findSubTermsByConstructor(  _ , \dv{ _ } (_) ) => .Patterns
    rule findSubTermsByConstructor(  _ , _ : _) => .Patterns

    // These should only occur in the constraint and not the main term
    rule findSubTermsByConstructor(  _ , \forall{ _ } (_, _) ) => .Patterns
    rule findSubTermsByConstructor(  _ , \exists{ _ } (_, _) ) => .Patterns
    rule findSubTermsByConstructor(  _ , \top{ _ } () ) => .Patterns
    rule findSubTermsByConstructor(  _ , \bottom{ _ } () ) => .Patterns
    rule findSubTermsByConstructor(  _ , \equals{ _, _ } (_ , _ ) ) => .Patterns
    rule findSubTermsByConstructor(  _ , \not{ _ } (_) ) => .Patterns
    rule findSubTermsByConstructor(  _ , \ceil{_, _}  (_)) => .Patterns

    syntax Patterns ::= findSubTermsByConstructorPs(KVar, Patterns) [function, functional]
    rule findSubTermsByConstructorPs(Ctor, P, Ps) => findSubTermsByConstructor(Ctor, P) +Patterns findSubTermsByConstructorPs(Ctor, Ps)
    rule findSubTermsByConstructorPs(   _, .Patterns) => .Patterns
endmodule
```

Tools for developing a frontend
===============================

```k
module K-FRONTEND
    imports KORE-PARSE
    imports KORE-UNPARSE
    imports KORE-UTILITIES
    imports LIST
```

`parse`
-------

```k
    syntax PrePattern ::= parse(input: PreString)
    rule parse(Input) =>  parse(Input, ".build/defn/frontend/frontend-kompiled/parser_Pattern_KORE-SYNTAX")
```

`kore-exec`
-----------

```k
    syntax PrePattern ::= koreExec(config: PrePattern)  [seqstrict(1), result(Pattern)]
                        | koreExec(filename: String, config: PrePattern) [seqstrict(2), result(Pattern)] /* Write PrePattern to filename */
                        | koreExecFile(file: PreString) [seqstrict(1), result(String)]
    rule koreExec(Configuration) => koreExecFile(writeTempFile(unparsePattern(Configuration)))
    rule koreExec(File, Configuration) => write(open(File, "w"), unparsePattern(Configuration)) ~> koreExecFile(File)
    rule koreExecFile(File)
      => parse( system("kore-exec .build/defn/verification/boogie-kompiled/definition.kore" +String
                           " --module BOOGIE-QUANTIFIERS" +String
                           " --pattern " +String File
                      )
              )
```

Pretty print
------------

```k
    syntax KItem ::= prettyPrint(config: PrePattern) [seqstrict(1), result(Pattern)]
                   | prettyPrint(file:   PreString)  [seqstrict(1), result(String)]
    rule prettyPrint(Configuration)
      => prettyPrint(writeTempFile(unparsePattern(Configuration)))
    rule prettyPrint(File)
      => print(system("kprint .build/defn/verification/boogie-kompiled/" +String
                    " " +String File +String
                    " false true"
               ))
```

```k
    syntax KItem ::= print(PreString) [seqstrict(1), result(String)]
    rule print(Str:String) => #write(#stdout, Str)
```

```k
endmodule
```

