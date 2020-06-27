Boogie Syntax
================

```k
requires "nothing.md"

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
                     | ConstantDecl
                     | ProcedureDecl
                     | ImplementationDecl
                     | TypeDecl
```

2 Types
-------

2.0 Type constructors
---------------------

```k
    syntax TypeDecl ::= TypeConstructor
    syntax TypeConstructor ::= "type" AttributeList Id ";"
```

2.1 Built-in types
------------------

```k
    syntax Type ::= TypeAtom | MapType
    syntax TypeAtom ::= "bool" | "int"
                      | Id
    syntax MapType ::= "[" TypeList "]" Type
    syntax TypeArgs

    syntax TypeList ::= List{Type, ","} [klabel(TypeList)]
```

4 Expressions
-------------

```k
    syntax Expr ::= Bool | Int | Id
                  | "(" Expr ")" [bracket]
                  | old(Expr)
                  > Expr MapOp
                  > UnOp Expr
                  > Expr MulOp  Expr [left]
                  > Expr AddOp  Expr [left]
                  > Expr RelOp  Expr [left]
                  > Expr "||"   Expr [left]
                  | Expr "&&"   Expr [left]
                  > Expr "==>"  Expr [left]
                  > Expr "<==>" Expr [left]
    syntax MapOp ::= "[" ExprList "]"             // Lookup
                   | "[" ExprList ":=" Expr "]"   // Update

    syntax RelOp ::= "==" | "!="
                   | "<" | ">" | "<=" | ">="
    syntax AddOp ::= "+" | "-"
    syntax MulOp ::= "*" | "/"
                   | "%" [unused] // semantics defined via axioms
    syntax UnOp  ::= "!"
                   | "-"

    // TODO: We do not overload IdList and ExprList because of https://github.com/kframework/kore/issues/1817
    syntax ExprList ::= List{Expr, ","} [klabel(ExprList), symbol]
    syntax IdList   ::= List{Id, ","}   [klabel(IdList)]
```

3 Constants and functions
-------------------------

```k
    syntax ConstantDecl ::= "const" AttributeList OptionalUnique IdsType ";"
    syntax OptionalUnique ::= Nothing | "unique"


    syntax IdsType ::= IdList ":" Type [avoid]
    syntax IdsTypeList ::= List{IdsType, ","} [klabel(IdsTypeList)]
```

7 Mutable Variables, states, and execution traces
-------------------------------------------------

```k
    syntax VarDecl ::= "var" AttributeList IdsTypeWhereList ";"
    syntax WhereClause ::= "where" Expr
    syntax IdsTypeWhere ::= IdsType WhereClause
                          | IdsType
    syntax IdsTypeWhereList ::= List{IdsTypeWhere, ","} [klabel(IdsTypeWhereList)]
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
                  | OptionalFree "ensures"  Expr ";"
                  | "modifies" IdList ";"
    syntax OptionalFree ::= Nothing | "free" [unused]
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
    syntax LocalVarDecl ::= VarDecl
    syntax LocalVarDeclList ::= List{LocalVarDecl, ""} [klabel(LocalVarDeclList)]
```

`LEmptyList` and `StmtList` are defined separately for parsing and for rules.
This allows us to parse more restrictively, and still have more freedom in the semantics.

```k
    syntax StmtList ::= List{LabelOrStmt, ""} [klabel(StmtList)]
    syntax LabelOrStmt ::= Stmt | Label
    syntax Label ::= Id ":"
```

```k
    syntax Stmt ::= SimpleStmt
                  | "goto" IdList ";"
                  | "return" ";"
    syntax SimpleStmt ::= "assert" AttributeList Expr ";"
                        | "assume" AttributeList Expr ";"
                        | "havoc" IdList ";"
                        | Lhs ":=" Expr ";"
                       // Why are ValueLists as KResults work?
                       // | IdList ":=" ExprList ";"
                        | "call" OptionalCallLhs Id "(" ExprList ")" ";"

    syntax Lhs ::= Id | Lhs "[" ExprList "]"
    syntax BlockStmt ::= "{" StmtList "}"
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

Extenions
---------

We extend the Boogie syntax with a `cutpoint;` `Stmt`. Currently, these are
generated by the`boogie`program and the `/Infer` option. Eventually, we will
want to detect cutpoints ourselves.

```k
    syntax Stmt ::= "cutpoint" ";"
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
