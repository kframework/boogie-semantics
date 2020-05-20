Boogie Syntax
================

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

```k
module BOOGIE-COMMON-SYNTAX
    imports BOOL-SYNTAX
    imports ID-SYNTAX
    imports INT-SYNTAX
    imports STRING-SYNTAX
    imports NOTHING-COMMON-SYNTAX
```

1 Overview
----------

```k
    syntax Program ::= DeclList
    syntax DeclList   ::= List{Decl, ""} [klabel(DeclList)]
    syntax Decl    ::= VarDecl
                     | ProcedureDecl
                     | ImplementationDecl

    syntax IdList ::= List{Id, ","} [klabel(IdList)]
```

2 Types
-------

2.1 Built-in types
------------------

```k
    syntax Type ::= TypeAtom
    syntax TypeAtom ::= "bool" | "int"
    syntax TypeArgs ::= "<" IdList ">"
```

4 Expressions
-------------

```k
    syntax Expr ::= Bool | Int | Id
                  | "(" Expr ")" [bracket]
                  > UnOp Expr
                  > Expr MulOp Expr [left]
                  > Expr AddOp Expr [left]
                  > Expr RelOp Expr [left]
                  > Expr "||"  Expr [left]
                  | Expr "&&"  Expr [left]
    syntax RelOp ::= "==" | "!="
                   | "<" | ">" | "<=" | ">="
    syntax AddOp ::= "+" | "-"
    syntax MulOp ::= "*" | "/" | "%"
    syntax UnOp  ::= "!"
                   | "-"
    syntax ExprList ::= List{Expr, ","} [klabel(ExprList), symbol]
```

7 Mutable Variables, states, and execution traces
-------------------------------------------------

```k
    syntax VarDecl ::= "var" AttributeList IdsTypeWhereList
    syntax IdsTypeWhere ::= IdsType // OptionalWhereClause
    syntax IdsTypeWhereList ::= List{IdsTypeWhere, ","} [klabel(IdsTypeWhereList)]
```

3 Constants and functions
-------------------------

```k
    syntax IdsType ::= IdList ":" Type [avoid]
    syntax IdsTypeList ::= List{IdsType, ","} [klabel(IdsTypeList)]
```

8 Procedures and implementations
--------------------------------

```k
    syntax ProcedureDecl ::= "procedure" AttributeList Id PSig ";" SpecList
                           | "procedure" AttributeList Id PSig SpecList Body
    syntax PSig          ::= OptionalTypeArgs "(" IdsTypeWhereList ")" OptionalOutParameters
    syntax OptionalTypeArgs      ::= Nothing | TypeArgs
    syntax OptionalOutParameters ::= Nothing | OutParameters
    syntax OutParameters ::= "returns" "(" IdsTypeWhereList ")"
```

```k
    syntax Spec ::= OptionalFree "requires" Expr ";"
                  | OptionalFree "modifies" IdList ";"
                  | OptionalFree "ensures" Expr ";"
    syntax OptionalFree ::= Nothing | "free"
    syntax SpecList ::= List{Spec, ""} [klabel(SpecList)]
```

```k
    // TODO: where clauses should not be in the Args or the Returns, we need to remove them when
    // desugaring from procedure declaration to implementation declaration
    syntax ImplementationDecl ::= "implementation" AttributeList Id ISig Body
    syntax ISig               ::= OptionalTypeArgs "(" IdsTypeWhereList ")" OptionalImpOutParameters
    syntax OptionalImpOutParameters ::= Nothing | ImpOutParameters
    syntax ImpOutParameters   ::= "returns" "(" IdsTypeWhereList ")"
```

9 Statements
------------

```k
    syntax Body ::= "{" LocalVarDeclList StmtList "}"
    syntax LocalVarDecl ::= "var" AttributeList IdsTypeWhereList ";"
    syntax LocalVarDeclList ::= List{LocalVarDecl, ""} [klabel(LocalVarDeclList)]
```

`LEmptyList` and `StmtList` are defined separately for parsing and for rules.
This allows us to parse more restrictively, and still have more freedom in the semantics.

```k
    syntax StmtList
    syntax Label ::= Id ":"
    syntax LabelOrStmt ::= LStmt | LEmpty
    syntax LStmt ::= Stmt
               //  | Label LStmt        // Different productions for RULE and PROGRAM grammars
    syntax LEmpty ::= Label
                    | Label LEmpty
```

```k
    syntax SimpleStmt ::= "assert" AttributeList Expr ";"
                        | "assume" AttributeList Expr ";"
                        | "havoc" Id ";" // TODO: support IDList here
                        | Id ":=" Expr ";"
                       // Why are ValueLists as KResults work?
                       // | IdList ":=" ExprList ";"
                        | "call" OptionalCallLhs Id "(" ExprList ")" ";"
    syntax Stmt ::= SimpleStmt
                  | "goto" IdList ";"
                  | IfStmt
                  | "while" "(" WildcardExpr ")" LoopInvList BlockStmt
                  | "break" ";"
                  | "break" Id ";"
                  | "return" ";"
    syntax WildcardExpr ::= Expr | "*"
    syntax BlockStmt ::= "{" StmtList "}"
    syntax IfStmt ::= "if" "(" WildcardExpr ")" BlockStmt
                    | "if" "(" WildcardExpr ")" BlockStmt "else" Else
    syntax Else ::= BlockStmt
                  | IfStmt
    syntax LoopInv ::=        "invariant" AttributeList Expr ";"
                     | "free" "invariant" AttributeList Expr ";"
    syntax LoopInvList ::= List{LoopInv, ""} [klabel(LoopInvList)]
    syntax OptionalCallLhs ::= Nothing | CallLhs
    syntax CallLhs ::= Id ":=" // TODO: support IdList
```

11 Tool directives
------------------

```k
    syntax Attribute ::= "{" ":" Id AttrArgList  "}"
    syntax AttributeList ::= List{Attribute, ""} [klabel(AttributeList)]

    syntax AttrArgList ::= List{AttrArg, ","}
    syntax AttrArg ::= Expr | String
```

```k
endmodule
```

```k
module BOOGIE-PROGRAM-SYNTAX
    imports BOOGIE-COMMON-SYNTAX
    imports NOTHING-PROGRAM-SYNTAX
    imports ID-SYNTAX-PROGRAM-PARSING

    syntax LStmt ::= Label LStmt                [klabel(lstmt), symbol]

    syntax LEmptyList ::= ""                    [klabel(dotStmtList), symbol]
                        | LEmpty LEmptyList     [klabel(StmtListCons), symbol]
    syntax StmtList ::= LEmptyList
                      | LStmt StmtList          [klabel(StmtListConsLStmt), symbol]
endmodule
```

```k
module BOOGIE-RULE-SYNTAX
    imports BOOGIE-COMMON-SYNTAX
    imports NOTHING-RULE-SYNTAX

    syntax LStmt ::= lstmt(Label, LStmt)      [klabel(lstmt), symbol]

    syntax StmtList ::= ".StmtList"           [klabel(dotStmtList), symbol]
    syntax StmtList ::= LabelOrStmt StmtList  [klabel(StmtListCons), symbol]
                      | StmtListConsLStmt(LStmt, StmtList)
                                              [klabel(StmtListConsLStmt), symbol, avoid]

    rule StmtListConsLStmt(S, Ss) => S Ss [macro]
endmodule
```
