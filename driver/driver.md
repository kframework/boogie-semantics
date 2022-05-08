```metak
requires "k-io.md"
requires "../quantification.md"
requires "substitution.md"
```

Plumbing
========

```metak
module DRIVER-HELPERS
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
    rule getFreshVars(Lbl'-LT-'freshVars'-GT-' { .Sorts } ( Arg, .Patterns ) ) => Arg, .Patterns
    rule getFreshVars(S { _ } ( Args ) ) => getFreshVarsPs(Args) requires S =/=K Lbl'-LT-'freshVars'-GT-'
    rule getFreshVars(inj{ _, _ } (P) ) => getFreshVars(P)
    rule getFreshVars(\not{ _ } (P) ) => getFreshVars(P)
    rule getFreshVars(\and{ _ } (P1, P2) ) => getFreshVars(P1) +Patterns getFreshVars(P2)
    rule getFreshVars(\equals{ _ , _} (_, _) ) => .Patterns
    rule getFreshVars(\forall{ _ } (_, _) ) => .Patterns
    rule getFreshVars(\exists{ _ } (_, _) ) => .Patterns
    rule getFreshVars(\dv{ _ } (_) ) => .Patterns
    rule getFreshVars(\top{ _ } () ) => .Patterns
    rule getFreshVars(_ : _) => .Patterns

    syntax Patterns ::= getFreshVarsPs(Patterns) [function, functional]
    rule getFreshVarsPs(P, Ps) => getFreshVars(P) +Patterns getFreshVarsPs(Ps)
    rule getFreshVarsPs(.Patterns) => .Patterns
```

```metak
    syntax Pattern ::= setKCell(config: Pattern, kcell: Pattern) [function]
    rule setKCell(Lbl'-LT-'k'-GT-' { .Sorts } ( _, .Patterns ), KCell ) => Lbl'-LT-'k'-GT-' { .Sorts } ( KCell, .Patterns )
    rule setKCell(S { Sorts } ( Args )                 , KCell ) => S { Sorts } ( setKCellPs(Args, KCell) ) requires S =/=K Lbl'-LT-'k'-GT-'
    rule setKCell(\and { S } ( P1, P2 )                , KCell ) => \and { S } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(\equals { S1, S2 } ( P1, P2 )        , KCell ) => \equals { S1, S2 } ( setKCell(P1, KCell), setKCell(P2, KCell))
    rule setKCell(\forall { S1 } ( P1, P2     )        , KCell ) => \forall { S1 } ( P1, setKCell(P2, KCell))
    rule setKCell(\exists { S1 } ( P1, P2     )        , KCell ) => \exists { S1 } ( P1, setKCell(P2, KCell))
    rule setKCell(inj{ S1, S2 } (P)                    , KCell ) => inj { S1, S2 } ( setKCell(P, KCell) )
    rule setKCell(\not{ S1 } (P)                       , KCell ) => \not{ S1 } ( setKCell(P, KCell) )
    rule setKCell(\top{ S1 } ()                        ,_KCell ) => \top{ S1 } ( )
    rule setKCell(\dv{ S } (P)                         ,_KCell ) => \dv{ S } (P)
    rule setKCell(S : Sort                             ,_KCell ) => S : Sort

    syntax Patterns ::= setKCellPs(config: Patterns, kcell: Pattern) [function]
    rule setKCellPs((P, Ps), KCell) => setKCell(P, KCell), setKCellPs(Ps, KCell)
    rule setKCellPs(.Patterns, _) => .Patterns
```

```metak
endmodule
```

```metak
module DRIVER
    imports DRIVER-HELPERS
    imports BOOGIE-QUANTIFIERS-META
    imports K-FRONTEND
```

Normalization
=============

First, we bring the configuration to the front of the conjunction:

```metak
    rule <k> Lbl'-LT-'generatedTop'-GT-' { .Sorts } ( _ ) #as Pgm => \and { SortGeneratedTopCell { } } (Pgm, \top {SortGeneratedTopCell { }}()) ... </k>
    rule <k> T:KItem
          ~> Lbl'-LT-'generatedTop'-GT-' { .Sorts } ( _ ) #as Pgm
          => ( T
            ~> \and { SortGeneratedTopCell { } } (Pgm, \top {SortGeneratedTopCell { }}())
             )
            ...
         </k>
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
    rule <k> \and { SortGeneratedTopCell { } }(_, _) #as ConstrainedConfiguration
          => triage(getKCell(ConstrainedConfiguration), ConstrainedConfiguration)
             ...
         </k>
    rule <k> \bottom{_}() => .K ... </k> // TODO: This is broken when the only result from a forall is `\bottom`
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
