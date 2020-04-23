While this file has been constructed by referencing https://boogie-docs.readthedocs.io/en/latest/LangRef.html#grammar

However, it appears to be inaccurate. The file, ext/boogie/Source/Core/BoogiePL.atg, should be used to confirm details.


```k
module BOOGIE-SYNTAX
    imports BOOL-SYNTAX
    imports ID
    imports INT-SYNTAX
    imports STRING-SYNTAX

    syntax BoogieProgram ::= Decls
    syntax Decls         ::= List{Decl, ""} [klabel(Decls)]
    syntax Decl          ::= AxiomDecl | ConstDecl | FuncDecl | ImplDecl | ProcDecl |  TypeDecl | VarDecl

    syntax AxiomDecl     ::= "axiom" Attrs Proposition ";"
    syntax ConstDecl     ::= "const" Attrs MaybeUnique TypedIdents MaybeOrderSpec ";"

    syntax FuncDecl      ::= "function" Attrs Ident MaybeTypeParams "(" VarOrTypes ")" FuncReturn FuncOptionalBody
    syntax FuncReturn    ::= "returns" "(" VarOrType ")"
                           | ProcReturn
    syntax ProcReturn     ::= ":" Type
    syntax FuncOptionalBody ::= "{" Exprs "}"
                              | ";"

    syntax ImplDecl      ::= "implementation" ProcSign ImplBody

    syntax ProcDecl  ::= "procedure" ProcSign ProcSpecs
    syntax ProcSpecs ::= ";" Specs
                       | Specs ImplBody

    syntax TypeDecl ::= "Type" Attrs TypeDeclParams ";"
    // TODO: These sorts need better names
    syntax TypeDeclParam ::= Ident Idents MaybeTypeAssign
    syntax TypeDeclParams ::= List{TypeDeclParam, ","} [klabel(TypeDeclParams)]
    syntax MaybeTypeAssign ::= Nothing | "=" Type

    syntax VarDecl ::= "var" Attrs TypedIdentsWheres ";"

    syntax OrderSpec         ::=  "extends" MaybeUniqueIdents MaybeComplete
    syntax MaybeUniqueIdent  ::= MaybeUnique Ident
    syntax MaybeUniqueIdents ::= List{MaybeUniqueIdent, ","} [klabel(Maybe)]

    syntax Attrs         ::= List{Attr, ""} [klabel(Attrs)]
    syntax Specs         ::= List{Spec, ""} [klabel(Specs)]

    syntax Nothing
    syntax MaybeUnique     ::= Nothing | "unique"
    syntax MaybeComplete   ::= Nothing | "complete"
    syntax MaybeOrderSpec  ::= Nothing | OrderSpec
    syntax MaybeTypeParams ::= Nothing | TypeParams
    syntax MaybeTypeArgs   ::= Nothing | TypeArgs
    syntax MaybeVarOrTypes ::= Nothing | VarOrTypes
    syntax MaybeProcReturn ::= Nothing | ProcReturn
    syntax MaybeFree       ::= Nothing | "free"

    syntax VarOrTypes        ::=  List{VarOrType, ","} [klabel(VarOr)]
    syntax VarOrType         ::= Attrs Type
                               | Ident MaybeProcReturn [avoid] // TODO: This avoid is a hack
    syntax ProcSign          ::=  Attrs Ident MaybeTypeParams "(" AttrTypedIdentsWheres ")" ProcReturn
    syntax ProcReturn        ::= Nothing
                               | "returns" "(" AttrTypedIdentsWheres ")"
    syntax ImplBody ::=  "{" LocalVarsList StmtList "}"
    syntax Stmt ::= LabelOrCmd | TransferCmd | StructuredCmd
    syntax StmtList ::=  List{Stmt, ""} [klabel(StmtL)]
    syntax LocalVarsList ::= List{LocalVars, ""} [klabel(Local)]
    syntax LocalVars ::=  "var" Attrs TypedIdentsWheres ";"
    syntax Spec  ::=  ModifiesSpec | RequiresSpec | EnsuresSpec
    syntax ModifiesSpec ::=  "modifies" Idents ";"
    syntax RequiresSpec ::=  MaybeFree "requires" Attrs Proposition ";"
    syntax EnsuresSpec ::=  MaybeFree "ensures" Attrs Proposition ";"
    syntax LabelOrCmd ::=  AssertCmd | AssignCmd | AssumeCmd | CallCmd | HavocCmd | Label | ParCallCmd | YeildCmd
    syntax TransferCmd  ::= GotoCmd | ReturnCmd
    syntax StructuredCmd ::= BreakCmd | IfCmd | WhileCmd
    syntax AssertCmd ::=  "assert" Attrs Proposition ";"
    syntax AssignCmd ::=  Ident ":=" Expr ";"                                               // ::=  Ident { "[" [ Exprs ] "]" } { "," Ident { "[" [ Exprs ] "]" } } ":=" Exprs ";"
    syntax AssumeCmd ::=  "assume" Attrs Proposition ";"
    syntax BreakCmd ::=  "break" ";"
                      |  "break" Ident ";"
    syntax CallCmd                                                                          // ::=  [ "async" ] [ "free" ] "call" Attrs CallParams ";"
    syntax GotoCmd  ::= "goto" Idents ";"
    syntax HavocCmd                                                                         // ::=  "havoc" Idents ";"
    syntax IfCmd                                                                            // ::=  "if" Guard "{" [ "else" ( IfCmd | "{" StmtList "}" ) ]
    syntax Label ::=  Ident ":"
    syntax ParCallCmd                                                                       // ::=  "par" Attrs CallParams { "|" CallParams } ";"
    syntax ReturnCmd ::=  "return" ";"

    syntax Invariant ::= MaybeFree "invariant" Attrs Expr ";"
    syntax Invariants ::= List{Invariant, ","} [klabel(Invar)]
    syntax WhileCmd ::=  "while" Guard Invariants
                         "{" StmtList "}"
    syntax YeildCmd                                                                         // ::=  "yield" ";"
    syntax CallParams                                                                       // ::=  Ident ( "(" [ Exprs ] ")" | [ "," Idents ] ":=" Ident [ Exprs ] ")" )
    syntax Guard ::= "(" "*" ")"
                   | "(" Expr ")"
    syntax Type ::=  TypeAtom | Ident MaybeTypeArgs | MapType
    syntax TypeArgs ::= TypeAtom MaybeTypeArgs
                      | Ident MaybeTypeArgs
                      | MapType
    syntax TypeAtom ::=  "int" | "real" | "bool" | "(" Type ")"
    syntax MapType                                                                          // ::=  MaybeTypeParams "[" [ Type { "," Type } ] "]" Type
    syntax Exprs ::=  List{Expr, ","} [klabel(Exprs)]
    syntax Proposition ::=  Expr
    syntax Expr ::=  ImpliesExpr
                  |  Expr EquivOp ImpliesExpr
    syntax EquivOp                                                                          // ::=  ( "<==>" | "⇔" )
    syntax ImpliesExpr ::= LogicalExpr                                                      // ::=  LogicalExpr [ ImpliesOp ImpliesExpr | ExpliesOp LogicalExpr { ExpliesOp LogicalExpr } ]
    syntax ImpliesOp                                                                        // ::=  ( "==>" | "⇒" )
    syntax ExpliesOp                                                                        // ::=  ( "<==" | "⇐" )
    syntax LogicalExpr                                                                      // ::=  RelExpr [ AndOp RelExpr { AndOp RelExpr } | OrOp RelExpr { OrOp RelExpr } ]
       ::= RelExpr
         | RelExpr AndOp RelExpr
         | RelExpr OrOp RelExpr
    syntax AndOp ::=  "&&" | "∧"
    syntax OrOp  ::=  "||" | "∨"
    syntax RelExpr ::=  BvTerm | RelExpr RepOp BvTerm
    syntax RepOp ::=  "==" | "<" | ">" | "<=" | ">=" | "!=" | "<:" | "≠" | "≤" | "≥"
    syntax BvTerm ::= Term
                    | BvTerm "++" Term
    syntax Term ::=  Factor | Term AddOp Factor
    syntax AddOp ::=  "+" | "-"
    syntax Factor ::=  Power | Factor MulOp Power
    syntax MulOp ::=  "*" | "div" | "mod" | "/"
    syntax Power ::=  UnaryExpr | Power "**" Power
    syntax UnaryExpr ::=  "-" UnaryExpr | NegOp UnaryExpr | CoercionExpr
    syntax NegOp ::= "!" | "¬"
    syntax CoercionExpr ::=  ArrayExp
// These cause ambiguities with K's syntax
//                          | CoercionExpr ":" Type
//                          | CoercionExpr ":" Nat
    syntax ArrayExp ::= AtomExpr                                                            // ::=  AtomExpr { "[" [ Exprs [ ":=" Expr ] | ":=" Expr ] "]" }
    syntax AtomExpr ::= Bool | Int | String | Ident | Ident "(" Exprs ")"  // ::=  ( Bool | Nat | Dec | Float | BvLit | Ident [ "(" ( Expr | ε ) ")" ] | OldExpr | ArithCoercionExpr | ParenExpr | ForallExpr | ExistsExpr | LambdaExpr | IfThenElseExpr | CodeExpr )
                      // TODO: ^^^ Int should be Nat
    syntax Nat                                                                              // ::=  Digits
    syntax Dec                                                                              // ::=  ( Decimal | DecFloat )
    syntax Decimal                                                                          // ::=  Digits "e" [ "-" ] Digits
    syntax DecFloat                                                                         // ::=  Digits "." Digits [ "e" [ "-" ] Digits ]
    syntax BvLit                                                                            // ::=  Digits "bv" Digits
    syntax OldExpr                                                                          // ::=  "old" "(" Expr ")"
    syntax ArithCoercionExpr                                                                // ::=  ( "int" "(" Expr ")" | "real" "(" Expr ")" )
    syntax ParenExpr                                                                        // ::=  "(" Expr ")"
    syntax ForallExpr                                                                       // ::=  "(" Forall QuandBody ")"
    syntax ExistsExpr                                                                       // ::=  "(" Exists QuandBody ")"
    syntax LambdaExpr                                                                       // ::=  "(" Lambda QuandBody ")"
    syntax Forall                                                                           // ::=  ( "forall" | "∀" )
    syntax Exists                                                                           // ::=  ( "exists" | "∃" )
    syntax Lambda                                                                           // ::=  ( "lambda" | "λ" )
    syntax QuandBody                                                                        // ::=  ( TypeParams [ BoundVars ] | BoundVars ) Qsep { AttrOrTrigger } Expr
    syntax BoundVars                                                                        // ::=  AttrTypedIdentsWheres
    syntax Qsep                                                                             // ::=  ( "::" | "•" )
    syntax IfThenElseExpr                                                                   // ::=  "if" Expr "then" Expr "else" Expr
    syntax CodeExpr                                                                         // ::=  "|{" { LocalVars } SpecBlock { speck_block  } "}|"
    syntax SpecBlock                                                                        // ::=  Ident ":" { LabelOrCmd } ( "goto" Idents | "return" Expr ) ";"
    syntax AttrTypedIdentsWheres ::=  List{AttrTypedIdentsWhere, ","} [klabel(AttrT)]
    syntax AttrTypedIdentsWhere ::=  Attrs TypedIdentsWhere
    syntax TypedIdentsWheres ::=  List{ TypedIdentsWhere, ","} [klabel(Typed)]
    syntax TypedIdentsWhere ::= TypedIdents
                              | TypedIdents "where" Expr
    syntax TypedIdents     ::=  Idents ":" Type
    syntax Idents          ::=  List{Ident, "," } [klabel(Ident)]
    syntax TypeParams                                                                       // ::=  "<" Idents ">"
    syntax Attr  ::=  AttrOrTrigger
    syntax AttrOrTrigger                                                                    // ::=  "{" ( ":" Ident [ AttrParam { "," AttrParam } ] | Exprs ) "}"
       ::= "{" ":" Ident AttrParams "}"
         | "{" Exprs "}"
    syntax AttrParams ::= List{AttrParam, ","} [klabel(AttrP)]
    syntax AttrParam ::= String | Expr
 //   syntax String                                                                         // ::=  quote { string_char | "\\\"" } quote
    syntax Ident ::=  Id                                                                    // ::= [ "\\" ] non_digit { non_digit | digit }
    syntax Digits                                                                           // ::=  digit { digit }
endmodule
```

Since the empty token and rule parsing interact badly, we define two different
syntaxes that parse to the same AST label:

```k
module BOOGIE-PROGRAM-SYNTAX
    imports BOOGIE-SYNTAX
    syntax Nothing ::= ""           [klabel(dotMaybe), symbol]
endmodule
```

```k
module BOOGIE-RULE-SYNTAX
    imports BOOGIE-SYNTAX
    syntax Nothing ::= ".Maybe"     [klabel(dotMaybe), symbol]
endmodule
```
