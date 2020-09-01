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
    syntax DeclList   ::= List{Decl, ""} [klabel(DeclList), symbol]
    syntax Decl    ::= VarDecl
                     | ConstantDecl
                     | FunctionDecl
                     | AxiomDecl
                     | ProcedureDecl
                     | ImplementationDecl
                     | TypeDecl
                     | TypeSynonym
```

2 Types
-------

2.0 Type constructors
---------------------

```k
    syntax TypeDecl ::= TypeConstructor
    syntax TypeConstructor ::= "type" AttributeList Id ";"
    syntax TypeSynonym ::= "type" AttributeList Id "=" Type ";"
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

3 Constants and functions
-------------------------

```k
    syntax ConstantDecl ::= "const" AttributeList OptionalUnique IdsType ";"
    syntax OptionalUnique ::= Nothing | "unique"

    syntax IdsType ::= IdList ":" Type [avoid]
    syntax IdsTypeList ::= List{IdsType, ","} [klabel(IdsTypeList)]
```

TODO: Signature should allow unnamed arguments;
TODO: Signature should allow "returns" syntax

```k
    syntax FunctionDecl ::= "function" AttributeList Id FSig ";"
                          | "function" AttributeList Id FSig "{" Expr "}"
    syntax FSig ::= "(" IdsTypeList ")" ":" Type
```

4 Expressions
-------------

```k
    syntax Expr ::= Bool | Int
                  | Id
                  | Id "(" ExprList ")" // function application
                  | "(" Expr ")" [bracket]
                  | old(Expr)
                  | "(" "forall" IdsTypeList "::" Expr ")"
                  | "(" "#forall" Id ":" Type "::" Expr ")" [klabel(forall), symbol] // TODO: This shouldn't be public
                  | LambdaExpr
                  | "if" Expr "then" Expr "else" Expr // TODO: deal with ambiguities for nested ITEs
                  > Expr MapOp
                  > UnOp Expr | Expr ":" Type
                  > Expr MulOp   Expr [left]
                  > Expr AddOp   Expr [left]
                  > Expr RelOp   Expr [left]
                  > Expr OrOp    Expr [left]
                  | Expr AndOp   Expr [left]
                  > Expr ImplOp  Expr [left]
                  > Expr EquivOp Expr [left]
    syntax LambdaExpr ::= "(" "lambda" IdsTypeList "::" Expr ")"
    syntax MapOp ::= "[" ExprList "]"             // Lookup
                   | "[" ExprList ":=" Expr "]"   // Update

    syntax EquivOp ::= "<==>"
    syntax ImplOp ::= "==>"
    syntax AndOp ::= "&&"
    syntax OrOp ::= "||"
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

6 Axioms
--------

```k
    syntax AxiomDecl ::= "axiom" AttributeList Expr ";"
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
                        | LhsList ":=" AssignRhs ";"
                        | "call" OptionalCallLhs Id "(" ExprList ")" ";"
    syntax AssignRhs ::= ExprList
    syntax Lhs ::= Id | Lhs "[" ExprList "]"
    syntax LhsList ::= List{Lhs, ","} [klabel(LhsList)]
    syntax BlockStmt ::= "{" StmtList "}"
    syntax OptionalCallLhs ::= Nothing | CallLhs
    syntax CallLhs ::= IdList ":="
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

We treat `forall`s with multiple bindings as multiple foralls with single bindings.

```k
    rule ( forall X, Xs : T,   IdsTypeList :: Expr ) => ( #forall X : T :: ( forall Xs : T, IdsTypeList :: Expr ) ) [macro-rec]
    rule ( forall .IdList : T, IdsTypeList :: Expr ) => ( forall IdsTypeList :: Expr ) [macro-rec]
    rule ( forall             .IdsTypeList :: Expr ) => Expr [macro-rec]
```

```k
endmodule
```

```k
module BOOGIE-PROGRAM-SYNTAX
    imports BOOGIE-COMMON-SYNTAX
    imports NOTHING-PROGRAM-SYNTAX
    imports ID-SYNTAX-PROGRAM-PARSING
```

Allow `#`s in `Id`s:

```k
    syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_][A-Za-z0-9\\_#]*" [prec(1), token]
```

```k
endmodule
```

```k
module BOOGIE-RULE-SYNTAX
    imports BOOGIE-COMMON-SYNTAX
    imports NOTHING-RULE-SYNTAX
endmodule
```
