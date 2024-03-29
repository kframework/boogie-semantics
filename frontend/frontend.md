```metak
requires "k-io.md"
requires "kore.md"
requires "../quantification.md"
requires "substitution.md"
```

Plumbing
========

```metak
module BOOGIE-FRONTEND-HELPERS
    imports KORE
    imports KORE-UNPARSE
    imports KORE-UTILITIES

    imports INT
    imports BOOL
    imports LIST
    imports SUBSTITUTION
```

We use these tokens in the definition.

```metak
    syntax KVar ::= "Lbl'-LT-'freshVars'-GT-'"    [token]
                  | "Lbl'-LT-'generatedTop'-GT-'" [token]
                  | "Lbl'-LT-'k'-GT-'"            [token]
                  | "Lbl'Hash'failure"            [token]
                  | "Lblforallbinder"             [token]
                  | "Lblforallbindercooled"       [token]
                  | "Lblforallbinderheated"       [token]
                  | "SortBool"                    [token]
                  | "SortExpr"                    [token]
                  | "SortGeneratedTopCell"        [token]
                  | "SortInt"                     [token]
                  | "SortK"                       [token]
                  | "SortKItem"                   [token]
                  | "SortString"                  [token]
                  | "SortValueExpr"               [token]
                  | "dotk"                        [token]
                  | "kseq"                        [token]
```

```metak
    configuration <k> $PGM:Pattern </k>
                  <freshVars> .K </freshVars>
                  <workingDir> $WorkingDir:String </workingDir>
                  <exitcode exit="0"> 1 </exitcode>
    rule  <k> .K </k>
          <exitcode> 1 => 0 </exitcode>
```

```metak
    syntax KItem ::= triage(kcell: Patterns, config: Pattern)
```

```metak
    syntax Patterns ::= getKCell(Pattern) [function]
    rule getKCell(Term) => findSubTermsByConstructor(Lbl'-LT-'k'-GT-', Term)

    syntax Patterns ::= getFreshVars(Pattern) [function]
    rule getFreshVars(Term) => findSubTermsByConstructor(Lbl'-LT-'freshVars'-GT-', Term)
```

```metak
    syntax Pattern ::= setKCell(config: Pattern, kcell: Pattern) [function]
    rule setKCell(Lbl'-LT-'k'-GT-' { .Sorts }(_), KCell ) => Lbl'-LT-'k'-GT-' { .Sorts } ( KCell, .Patterns )
    rule setKCell(S { Sorts } ( Args )          , KCell ) => S { Sorts } ( setKCellPs(Args, KCell) ) requires S =/=K Lbl'-LT-'k'-GT-'
    rule setKCell(\and { S } ( P1, P2 )         , KCell ) => \and { S } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(\or  { S } ( P1, P2 )         , KCell ) => \or  { S } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(inj{ S1, S2 } (P)             , KCell ) => inj { S1, S2 } ( setKCell(P, KCell) )

    // We do not recurse into predicates
    rule setKCell(\equals{S1, S2} (P1, P2)      ,_KCell) => \equals{S1, S2} (P1, P2)
    rule setKCell(\forall{S1} (P1, P2)          ,_KCell) => \forall{S1} (P1, P2)
    rule setKCell(\exists{S1} (P1, P2)          ,_KCell) => \exists{S1} (P1, P2)
    rule setKCell(\not{S1} (P)                  ,_KCell) => \not{S1} (P)
    rule setKCell(\top{S1} ()                   ,_KCell) => \top{S1} ()
    rule setKCell(\ceil{S1, S2} (P)             ,_KCell) => \ceil{S1, S2} (P)
    rule setKCell(\dv{S}   (P)                  ,_KCell) => \dv{S} (P)
    rule setKCell(S : Sort                      ,_KCell) => S : Sort

    syntax Patterns ::= setKCellPs(config: Patterns, kcell: Pattern) [function]
    rule setKCellPs((P, Ps), KCell) => setKCell(P, KCell), setKCellPs(Ps, KCell)
    rule setKCellPs(.Patterns, _) => .Patterns
```

```metak
endmodule
```

```metak
module BOOGIE-FRONTEND
    imports BOOGIE-FRONTEND-HELPERS
    imports BOOGIE-QUANTIFIERS-META
    imports K-FRONTEND
```

Search
======

We perform a depth first search over branches:

```metak
    rule <k> \or { SortGeneratedTopCell { } }(P1, P2) => P1 ~> P2 ... </k>
```

## Triaging

For each constrained configuration, we triage according to the content of the `<k>` cell:

```metak
    rule <k> (\and { SortGeneratedTopCell { } }(_, _) #Or Lbl'-LT-'generatedTop'-GT-' { .Sorts } ( _ )) #as ConstrainedConfiguration
          => triage(getKCell(ConstrainedConfiguration), ConstrainedConfiguration)
             ...
         </k>
```

### Failure

```metak
    rule <k> triage(kseq{ .Sorts } ( Lbl'Hash'failure { .Sorts } ( \dv { SortString { } } ( Message ) ), _) , Pgm)
          => print("==== failure: ") ~> print(Message) ~> print("\n") ~> prettyPrint(Pgm) ~> print("\n")
             ...
         </k>
```

### Succeeded:

```metak
    rule <k> triage(dotk {.Sorts} (.Patterns), Pgm)
          => print("==== success\n") ~> prettyPrint(Pgm) ~> print("\n")
             ...
         </k>
```

#### Stuck?

```metak
    syntax KItem ::= "#Stuck"
    rule <k> ( .K
            => print("==== stuck\n")
            ~> prettyPrint(Pgm)
            ~> #Stuck
             )
          ~> triage(_ , Pgm)
             ...
         </k>
         [owise]
```

## `forall`

See [../quantification.md]

```metak
endmodule
```
