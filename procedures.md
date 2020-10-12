8 Procedures and implementations
--------------------------------

```k
module BOOGIE-PROCEDURES
    imports syntax DEFAULT-CONFIGURATION
    imports syntax BOOGIE-FRESH-COUNTER

    imports INT
    imports BOOGIE-RULE-SYNTAX

    configuration <procs>
                    <proc multiplicity="*" type="Map">
                      <procName> #token("ProcedureName", "Id") </procName>
                      <args> .IdsTypeWhereList </args>
                      <rets> .IdsTypeWhereList </rets>
                      <requires> true:Expr </requires>
                      <ensures> true:Expr </ensures> // ensures
                      <modifies> .IdList </modifies>   // modifies
                      <impls>
                        <impl multiplicity="*" type="Map">
                          <implId> -1 </implId>
                          <body> { .LocalVarDeclList .StmtList } </body>
                          <iargs> .IdsTypeWhereList </iargs>
                          <irets> .IdsTypeWhereList </irets>
                        </impl>
                      </impls>
                    </proc>
                  </procs>
```

Split procedures with a body into a procedure and an implementation:

```k
    rule <k> (procedure Attrs:AttributeList
                ProcedureName .Nothing ( Args ) returns ( Rets ) SpecList
                Body):Decl
          => procedure Attrs:AttributeList
               ProcedureName .Nothing ( Args ) returns ( Rets ) ; SpecList
          ~> implementation Attrs ProcedureName .Nothing ( Args ) returns ( Rets )
               Body
             ...
         </k>
```

```k
    rule <k> procedure      _:AttributeList _ProcedureName .Nothing ( _Args ) (.Nothing => returns (.IdsTypeWhereList)) ; _SpecList            ... </k>
    rule <k> implementation _:AttributeList _ProcedureName .Nothing ( _Args ) (.Nothing => returns (.IdsTypeWhereList)) { _VarList _StmtList } ... </k>
```

```k
    syntax KItem ::= "#populateProcedure"
    rule <k> (.K => #populateProcedure)
          ~> procedure _:AttributeList ProcedureName _TypeArgs ( Args ) returns ( Rets ) ; _SpecList
             ...
         </k>
         <procs> .Bag =>
           <proc>
             <procName> ProcedureName </procName>
             <args> Args </args>
             <rets> Rets </rets>
             ...
           </proc>
           ...
         </procs>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (.Nothing requires NewReq ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <requires> Reqs => Reqs && NewReq </requires>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (.Nothing ensures NewEnsures ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <ensures> Ensures => Ensures && NewEnsures </ensures>

    rule <k> #populateProcedure ~> procedure _:AttributeList ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
             ; (modifies Modifies ; SpecList => SpecList)
             ...
         </k>
         <procName> ProcedureName </procName>
         <modifies> .IdList => Modifies </modifies>

    rule <k> ( #populateProcedure ~> procedure _:AttributeList _ProcedureName _TypeArgs ( _Args ) returns ( _Rets )
               ; .SpecList
             )
          => .K
             ...
         </k>
```

```k
    rule <k> implementation Attrs:AttributeList ProcedureName .Nothing ( IArgs ) returns ( IRets ) Body
          => .K
             ...
         </k>
         <procName> ProcedureName </procName>
         <impls> .Bag
              => <impl>
                   <implId> N </implId>
                   <body> Body </body>
                   <iargs> IArgs </iargs>
                   <irets> IRets </irets>
                 </impl>
                 ...
         </impls>
         <freshCounter> N => N +Int 1 </freshCounter>
```

```k
endmodule
```
