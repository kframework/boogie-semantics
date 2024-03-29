Boogie Syntax
=============

```k
module BOOGIE-COMMON-SYNTAX
    imports BOOL-SYNTAX
    imports ID-SYNTAX
    imports UNSIGNED-INT-SYNTAX
    imports STRING-SYNTAX
    imports NOTHING-COMMON-SYNTAX
```

1 Overview
----------

```k
    syntax Program ::= DeclList
    syntax DeclList ::= List{Decl, ""} [klabel(DeclList), symbol]
    syntax Decl ::= VarDecl
                  | ConstantDecl
                  | FunctionDecl
                  | AxiomDecl
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
                      | TypeSynonym
    syntax TypeConstructor ::= "type" AttributeList IdList ";"
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
    syntax FSig ::= "(" IdsTypeList ")" ":" Type [avoid]
                  | "(" TypeList ")" ":" Type
                  | "(" IdsTypeList ")" "returns" "(" Type ")" [avoid, macro]
                  | "(" TypeList ")"    "returns" "(" Type ")" [macro]
    rule ((Args:IdsTypeList) returns(Type)):FSig => (Args) : Type
    rule ((Args:TypeList)    returns(Type)):FSig => (Args) : Type
```

4 Expressions
-------------

```k
    syntax Expr ::= Bool | Int
                  | Id
                  | Id "(" ExprList ")" // function application
                  | "(" Expr ")" [bracket]
                  | old(Expr)
                  | "(" "forall" IdsTypeList "::" Expr ")" [macro-rec]
                  | "(" "exists" IdsTypeList "::" Expr ")" [macro]
                  | "(" "forall" IdsTypeList "::" TriggerList Expr ")" [avoid, macro]
                  | "(" "#forall" Id ":" Type "::" Expr ")" [klabel(forall), symbol] // TODO: This shouldn't be public
                  | LambdaExpr
                  | "if" Expr "then" Expr "else" Expr // TODO: deal with ambiguities for nested ITEs
                  > Expr MapOp
                  > UnOp Expr | Expr ":" Type
                  > Expr MulOp   Expr [left]
                  > Expr AddOp   Expr [left]
                  > Expr RelOp   Expr [left]
                  > Expr OrOp    Expr [left]
                  > Expr AndOp   Expr [left]
                  > Expr ImplOp  Expr [left]
                  > Expr EquivOp Expr [left]
    syntax LambdaExpr ::= "(" "lambda" IdsTypeList "::" Expr ")"
                        | "(" "lambda" IdsTypeList "::" AttributeList Expr ")" [macro]
    rule (lambda IdsTypeList :: _:AttributeList Expr ) => (lambda IdsTypeList :: Expr )

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

    syntax Trigger ::= "{" ExprList "}"
    syntax TriggerList ::= List{Trigger, ""} [klabel(TriggerList), symbol]
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
    // TODO: unlike in procedures, "where" clauses are not allowed in Args or Returns.
    syntax ImplementationDecl ::= "implementation" AttributeList Id PSig Body
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
    syntax LabelOrStmt ::= Stmt | Label ":"
    syntax Label ::= Id
    syntax LabelList ::= List{Label, ","} [klabel(LabelList)]
```

```k
    syntax Stmt [locations]
    syntax Stmt ::= "goto" LabelList ";"
                  | "break" Id ";"
                  | "break" ";"
                  | "return" ";"
                  | "assert" AttributeList Expr ";"
                  | "assume" AttributeList Expr ";"
                  | "havoc" IdList ";"
                  | LhsList ":=" AssignRhs ";"
                  | "free" "call" CallLhs Id "(" ExprList ")" ";"   // Note: We don't use OptionalFree here because that messes with line numbers
                  |        "call" CallLhs Id "(" ExprList ")" ";"
                  | "free" "call"         Id "(" ExprList ")" ";"
                  |        "call"         Id "(" ExprList ")" ";"
                  | IfStmt
                  | "while" "(" WildcardExpr ")" LoopInvariantList BlockStmt

    syntax WildcardExpr ::= "*" | Expr
    syntax IfStmt       ::= "if" "(" WildcardExpr ")" BlockStmt OptionalElse
    syntax OptionalElse ::= Nothing | "else" Else
    syntax Else         ::= BlockStmt | IfStmt

    syntax LoopInvariant [locations]
    syntax LoopInvariant ::= "invariant" AttributeList Expr ";"
                           | "free" "invariant" AttributeList Expr ";"
    syntax LoopInvariantList ::= List{LoopInvariant, ""} [klabel(LoopInvariantList)]

    syntax AssignRhs ::= ExprList
    syntax Lhs ::= Id | Lhs "[" ExprList "]"
    syntax LhsList ::= List{Lhs, ","} [klabel(LhsList)]
    syntax BlockStmt ::= "{" StmtList "}"
    syntax CallLhs ::= IdList ":="
    syntax OptionalCallLhs ::= Nothing | CallLhs
```

11 Tool directives
------------------

```k
    syntax Attribute ::= "{" ":" Id AttrArgList  "}"
    syntax AttributeList ::= List{Attribute, ""} [klabel(AttributeList)]

    syntax AttrArgList ::= List{AttrArg, ","}
    syntax AttrArg ::= Expr | String
```

Quantifiers
-----------

We treat `forall`s with multiple bindings as multiple foralls with single bindings, and ignore triggers for now.

```k
    rule ( forall IdsTypeList :: _:Trigger Expr ) => ( forall IdsTypeList :: Expr )

    rule ( forall X, Xs : T,   IdsTypeList :: Expr ) => ( #forall X : T :: ( forall Xs : T, IdsTypeList :: Expr ) )
    rule ( forall X, Xs : T,   IdsTypeList :: Expr ) => ( #forall X : T :: ( forall Xs : T, IdsTypeList :: Expr ) )
    rule ( forall .IdList : _, IdsTypeList :: Expr ) => ( forall IdsTypeList :: Expr )
    rule ( forall             .IdsTypeList :: Expr ) => Expr
```

Exists are desugared for forall. We cannot implement simply using K's `!` variables, because of quantifier alternation.

```k
    rule ( exists IdsTypeList :: Expr ) => ! ( forall IdsTypeList :: ! Expr )
````

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
    syntax Id ::= r"(?<![A-Za-z0-9\\_])[A-Za-z\\_]['A-Za-z0-9\\_#]*" [prec(1), token]
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
