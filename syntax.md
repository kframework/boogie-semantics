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
==========

```k
    syntax Program ::= DeclList
    syntax DeclList   ::= List{Decl, ""} [klabel(DeclList)]
    syntax Decl    ::= VarDecl
                     | ProcedureDecl

    syntax IdList ::= List{Identifier, ","} [klabel(IdList)]
```

2 Types
=======

2.1 Built-in types
------------------

```k
    syntax Type ::= TypeAtom
    syntax TypeAtom ::= "bool" | "int"
    syntax TypeArgs ::= "<" IdList ">"
```

4 Expressions
=============

```k
    syntax Identifier ::= Id
    syntax Expr ::= Bool | Int | Identifier
                  | "(" Expr ")" [brackets]
                  > Expr RelOp Expr
                  > Expr AddOp Expr [left]
                  > Expr MulOp Expr [left]
    syntax RelOp ::= "=="
                   | "<"
    syntax AddOp ::= "+" | "-"
    syntax MulOp ::= "*" | "/" | "%"
    syntax ExprList ::= List{Expr, ","} [klabel(ExprList), symbol]
```

7 Mutable Variables, states, and execution traces
=================================================

```k
    syntax VarDecl ::= "var" AttributeList IdsTypeWhereList
    syntax IdsTypeWhere ::= IdsType // OptionalWhereClause
    syntax IdsTypeWhereList ::= List{IdsTypeWhere, ","} [klabel(IdsTypeWhereList)]
```

3 Constants and functions
=========================

```k
    syntax IdsType ::= IdList ":" Type [avoid]
```

8 Procedures and implementations
================================

8.0 Syntax
----------

```k
    syntax ProcedureDecl ::= "procedure" AttributeList Identifier PSig ";" SpecList
                           | "procedure" AttributeList Identifier PSig SpecList Body
    syntax PSig          ::= OptionalTypeArgs "(" IdsTypeWhereList ")" OptionalOutParameters
    syntax OptionalTypeArgs      ::= Nothing | TypeArgs
    syntax OptionalOutParameters ::= Nothing | OutParameters
    syntax OutParameters ::= "returns" "(" IdsTypeWhereList ")"
```

```k
    syntax Spec
    syntax SpecList ::= List{Spec, ""} [klabel(SpecList)]
```

9 Statements
============

```k
    syntax Body ::= "{" LocalVarDeclList StmtList "}"
    syntax LocalVarDecl ::= "var" AttributeList IdsTypeWhereList ";"
    syntax LocalVarDeclList ::= List{LocalVarDecl, ""} [klabel(LocalVarDeclList)]
```

TODO: this is simpler than the "This is Boogie" grammar.

```k
    syntax StmtList ::= List{LabelOrStmt, ""} [klabel(StmtList)]
    syntax LabelOrStmt  ::= Stmt
                          | Identifier ":"
```

```k
    syntax SimpleStmt ::= "assert" AttributeList Expr ";"
                        | "assume" AttributeList Expr ";"
                        | Id ":=" Expr ";"
                       // Why are ValueLists as KResults work?
                       // | IdList ":=" ExprList ";"
    syntax Stmt ::= SimpleStmt
                  | "goto" IdList ";"
                  | "while" "(" WildcardExpr ")" LoopInvList BlockStmt
                  | "break" ";"
                  | "break" Identifier ";"
                  | "return" ";"
    syntax WildcardExpr ::= Expr | "*"
    syntax BlockStmt ::= "{" StmtList "}" 
    syntax IfStmt ::= "if" "(" WildcardExpr ")" BlockStmt
                    | "if" "(" WildcardExpr ")" BlockStmt Else
    syntax Else ::= "else" BlockStmt
                  | "else" IfStmt
    syntax LoopInv ::=        "invariant" AttributeList Expr ";"
                     | "free" "invariant" AttributeList Expr ";"
    syntax LoopInvList ::= List{LoopInv, ""} [klabel(LoopInvList)]
```

11 Tool directives
==================

```k
    syntax Attribute ::= "{" ":" Identifier AttrArgList  "}"
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
endmodule
```

```k
module BOOGIE-RULE-SYNTAX
    imports BOOGIE-COMMON-SYNTAX
    imports NOTHING-RULE-SYNTAX
endmodule
```
