```k
module KORE
    imports STRING-SYNTAX

    syntax Name ::= r"[A-Za-z'-][A-Za-z'0-9-]*" [token]
    syntax Sort ::= Name "{" "}"
    syntax Symbol ::= Name "{" "}"
    syntax Pattern ::= "\\dv" "{" Sort "}" "(" String ")"                           [klabel(\dv)]
                     | Name ":" Sort                                                [klabel(variable)]
                     | Symbol "(" Patterns ")"                                      [klabel(application)]
                     | "\\not" "{" Sort "}" "(" Pattern ")"                          [klabel(\not)]
                     | "inj" "{" Sort "," Sort "}" "(" Pattern ")"                  [klabel(inj)]
                     | "\\equals" "{" Sort "," Sort "}" "(" Pattern "," Pattern ")" [klabel(\equals)]
                     | "\\and" "{" Sort "}" "(" Pattern "," Pattern ")"             [klabel(\and)]
                     | "\\or" "{" Sort "}" "(" Pattern "," Pattern ")"              [klabel(\or)]
                     | "\\top" "{" Sort "}" "(" ")"                                 [klabel(\top)]

    syntax Patterns ::= List{Pattern, ","} [klabel(Patterns)]
endmodule
```

```k
module KORE-UNPARSE
    imports KORE
    imports STRING

    syntax String ::= unparsePattern(Pattern) [function, functional]
    rule unparsePattern(\equals { S1 , S2 } (P1, P2)) => "\\equals{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String " , " +String unparsePattern(P2) +String ")"
    rule unparsePattern(Name : Sort)                  => NameToString(Name) +String ":" +String unparseSort(Sort)
    rule unparsePattern(\dv { S } (Value))            => "\\dv{" +String unparseSort(S)  +String "} (\"" +String Value +String "\")"
    rule unparsePattern(\top { S } ())                => "\\top{" +String unparseSort(S)  +String "} ()"
    rule unparsePattern(inj { S1 , S2 } (P1))         => "inj{" +String unparseSort(S1) +String "," +String unparseSort(S2)  +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(\not { S1 } (P1))         => "\\not{" +String unparseSort(S1) +String "} (" +String unparsePattern(P1) +String ")"
    rule unparsePattern(S(Args:Patterns))             => unparseSymbol(S) +String "(" +String unparsePatterns(Args) +String ")"

    rule unparsePattern(\and { S1 } (P1, P2))
      => "\\and{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"
    rule unparsePattern(\or { S1 } (P1, P2))
      => "\\or{" +String unparseSort(S1) +String "} (" +String unparsePatterns(P1) +String "," +String unparsePatterns(P2) +String  ")"

    syntax String ::= NameToString(Name) [function, functional, hook(STRING.token2string)]

    syntax String ::= unparseSort(Sort) [function, functional]
    rule unparseSort(Name {}) => NameToString(Name) +String "{}"

    syntax String ::= unparseSymbol(Symbol) [function, functional]
    rule unparseSymbol(Name {}) => NameToString(Name) +String "{}"

    syntax String ::= unparsePatterns(Patterns) [function, functional]
    rule unparsePatterns(P, Ps) => unparsePattern(P) +String "," +String unparsePatterns(Ps) requires notBool Ps ==K .Patterns
    rule unparsePatterns(P, .Patterns) => unparsePattern(P)
    rule unparsePatterns(.Patterns) => ""
endmodule
```

```k
module DRIVER
    imports KORE
    imports KORE-UNPARSE
    imports K-IO
    imports K-REFLECTION
    imports LIST
```

```k
    configuration <k> $PGM:Pattern ~> init </k>
                  <out stream="stdout"> .List </out>
                  <definition> $Definition:String </definition>
                  <workingDir> $WorkingDir:String </workingDir>
                  <exitcode exit="0"> 1 </exitcode>
    rule  <k> .K </k>
          <exitcode> 1 => 0 </exitcode>
```

Normalization
=============

Normalize constrained configurations, so that the configuration is at the front of the term:

```k
    rule \and { S }(P, \and { S } (Lbl'-LT-'generatedTop'-GT-' { } (_) #as Config, Ps)) => \and { S }(Config, \and { S } (P, Ps)) [anywhere]
    rule \and { S }(P, (Lbl'-LT-'generatedTop'-GT-' { } (_) #as Config)) => \and { S }(Config, P)                                 [anywhere]
```

The result of `kore-exec --search` and `krun` are of the form:

```
    {       sideconditions
    #And    Result == Configuration
    }
```

We convert this to a constrained confiuration:

```
    {       sideconditions
    #And    Configuration
    }
```

```k
    syntax Name ::= "SortK" [token]
                  | "SortKItem" [token]
                  | "VarResult" [token]
                  | "kseq" [token]
                  | "dotk" [token]
                  | "SortGeneratedTopCell" [token]

    rule \equals { SortK { } , SortKItem { } } ( VarResult : SortK { }
                                               , kseq { } ( inj { SortGeneratedTopCell { } , SortKItem { } }(Result) , dotk { } ( .Patterns ) ) )
      => Result
    rule \equals { _ , _ } ( VarResult : SortGeneratedTopCell { } , Result ) => Result [anywhere]
    rule (P, (Lbl'-LT-'generatedTop'-GT-' { } ( _ ) #as Config), Ps)
      => Config, P, Ps [anywhere]

    rule <k> Lbl'-LT-'generatedTop'-GT-' { } ( _ ) #as Pgm
          => \and { SortGeneratedTopCell { } } (Pgm, \top {SortGeneratedTopCell { }}())
             ...
         </k>
```

Search
======

We perform a depth first search over branches:

```k
    rule <k> \or { SortGeneratedTopCell { } }(P1, P2) => P1 ~> P2 ... </k>
```

For each constrained configuration, we triage according to the content of the `<k>` cell:

```k
    syntax Name ::= "Lbl'-LT-'generatedTop'-GT-'" [token]
    rule <k> \and { SortGeneratedTopCell { } }(Lbl'-LT-'generatedTop'-GT-' { } (_) #as Config, _Constraints) #as ConstrainedConfiguration
          => triage(getKCell(Config), ConstrainedConfiguration)
             ...
         </k>
```

```k
    syntax KItem ::= triage(kcell: Patterns, config: Pattern)
```

```k
    syntax KItem ::= "init"
    rule <k> triage(_, Pgm) ~> init => exec(Pgm) ... </k>
```

```k
    syntax Name ::= "SortString" [token]
                  | "Lbl'Hash'failure" [token]
    rule <k> triage(kseq{ } ( Lbl'Hash'failure { } ( \dv { SortString { } } ( Message ) ), _) , Pgm) => .K ... </k>
         <out> ... .List
            => ListItem("==== failure\n")
               ListItem(Message)             ListItem("\n")
               ListItem(unparsePattern(Pgm)) ListItem("\n")
               ListItem("\n")
         </out>
```

Succeeded:

```k
    rule <k> triage(dotk{}(.Patterns), Pgm) => .K ... </k>
         <out> ... .List
            => ListItem("==== success\n")
               ListItem(unparsePattern(Pgm))
               ListItem("\n")
         </out>
```

Forall:

```k
    syntax Name ::= "Lblforallbinder"       [token]
                  | "Lblforallbinderheated" [token]
                  | "Lblforallbindercooled" [token]
                  | "SortExpr"        [token]
    syntax KItem ::= forallFreezer(kcellRest: Pattern, config: Pattern)
    rule <k> triage(kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinder { } ( V, E )), Rest) , Pgm) => .K
          ~> exec(setKCell(Pgm, kseq{ } ( inj { SortExpr { }, SortKItem { } } ( Lblforallbinderheated { } ( V, E )), dotk{}(.Patterns))))
          ~> forallFreezer(Rest, Pgm)
             ...
         </k>
```

```k
    rule <k> triage(kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbinderheated{}(V,inj{SortBool{},SortExpr{}}(E))), dotk{}(.Patterns)), _)
          ~> forallFreezer(Rest, Pgm)
          => exec(setKCell(Pgm, kseq{}(inj{SortExpr{},SortKItem{}}(Lblforallbindercooled{}(V,inj{SortBool{},SortExpr{}}(E))),Rest)))
             ...
         </k> 
```

```k
    syntax Patterns ::= getKCell(Pattern) [function]
    rule getKCell(Lbl'-LT-'k'-GT-' { } ( Arg, .Patterns ) ) => Arg, .Patterns
    rule getKCell(S { } ( Args ) ) => getKCellPs(Args) requires S =/=K Lbl'-LT-'k'-GT-'
    rule getKCell(inj{ _, _ } (P) ) => getKCell(P)
    rule getKCell(\not{ _ } (P) ) => getKCell(P)
    rule getKCell(\dv{ _ } (_) ) => .Patterns
    rule getKCell(_ : _) => .Patterns

    syntax Patterns ::= getKCellPs(Patterns) [function, functional]
    rule getKCellPs(P, Ps) => getKCell(P) +Patterns getKCellPs(Ps)
    rule getKCellPs(.Patterns) => .Patterns
```

```k
    syntax Pattern ::= setKCell(config: Pattern, kcell: Pattern) [function]
    rule setKCell(Lbl'-LT-'k'-GT-' { } ( _, .Patterns ), KCell ) => Lbl'-LT-'k'-GT-' { } ( KCell, .Patterns ) 
    rule setKCell(S { } ( Args )                       , KCell ) => S { } ( setKCellPs(Args, KCell) ) requires S =/=K Lbl'-LT-'k'-GT-'
    rule setKCell(\and { S } ( P1, P2 )                , KCell ) => \and { S } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(\equals { S1, S2 } ( P1, P2 )        , KCell ) => \equals { S1, S2 } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(inj{ S1, S2 } (P)                    , KCell ) => inj { S1, S2 } ( setKCell(P, KCell) )
    rule setKCell(\not{ S1 } (P)                       , KCell ) => \not{ S1 } ( setKCell(P, KCell) )
    rule setKCell(\top{ S1 } ()                        ,_KCell ) => \top{ S1 } ( )
    rule setKCell(\dv{ S } (P)                         ,_KCell ) => \dv{ S } (P)
    rule setKCell(S : Sort                             ,_KCell ) => S : Sort

    syntax Patterns ::= setKCellPs(config: Patterns, kcell: Pattern) [function]
    rule setKCellPs((P, Ps), KCell) => setKCell(P, KCell), setKCellPs(Ps, KCell)
    rule setKCellPs(.Patterns, _) => .Patterns
    
    syntax Name ::= "Lbl'-LT-'k'-GT-'" [token]
```

```k
    syntax Patterns ::= Patterns "+Patterns" Patterns [function, functional, left]
    rule (P1, P1s) +Patterns P2s => P1, (P1s +Patterns P2s) 
    rule .Patterns +Patterns P2s =>                    P2s 
```

Execution Plumbing
==================

To execute a configuration, we:

1. unparse it to a string,
2. write that it to a temporary file,
3. execute it using the `kore-exec-helper` script,
4. and unparse the kore output into a K term.

```k
    syntax KItem ::= exec(Pattern)
    rule <k> exec(Config)
          => write-to-file(unparsePattern(Config), #open(WD +String "/" +String Int2String(!I) +String ".input", "w"))
          ~> kore-exec(path:                             WD +String "/" +String Int2String(!I)                       )
          ~> parseKORE
             ...
         </k>
         <workingDir> WD </workingDir>

    syntax KItem ::= "write-to-file" "(" contents: String "," fd: IOInt ")"
    rule <k> write-to-file(Str, Fd) => #write(Fd, Str) ~> close(Fd) ... </k>

    syntax KItem ::= "kore-exec" "(" "path:" String ")" [seqstrict, result(String)]
    rule <k> kore-exec(path: Path)
          => #system("./driver/kore-exec-helper " +String Definition +String " " +String Path)
             ...
         </k>
         <definition> Definition </definition>
    rule <k> #systemResult(0, StdOut, _) => StdOut ... </k>

    syntax KItem ::= "parseKORE"
    rule <k> S:String ~> parseKORE
          => #parseKORE(S):Pattern
             ...
         </k>

    syntax KItem ::= close(Int)
    rule <k> close(Fd) => #close(Fd) ... </k>
```

```k
endmodule
```