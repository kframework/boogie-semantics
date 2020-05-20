## Nondeterministic While Loop

```k
module SPEC
    imports BOOGIE
    rule <boogie>
           <k> ( procedure .AttributeList main .Nothing (.IdsTypeWhereList)
                           returns (.IdsTypeWhereList)
                           .SpecList
                 {
                   ( var .AttributeList inc : int ;
                     .LocalVarDeclList
                   ):LocalVarDeclList

                   ( inc := 100;
                     while (*) invariant .AttributeList inc > 99; .LoopInvList {
                         inc:= inc + 5;
                         .StmtList
                     }
                     assert .AttributeList inc > 99;
                     .StmtList
                   ):StmtList
                 }
               )
            ~> #start
            => .K
           </k>
           <env> .Map => ?_  </env>
           <store> .Map  => ?_ </store>
           <labels> .Map => ?_  </labels>
           <exit-code> 1 => ?_  </exit-code>
           <freshCounter> 0 => ?_ </freshCounter>
           <procs> .Bag => ?_ </procs>
         </boogie>

    rule <boogie>
           <k>
             inc := inc + 5 ; goto Head_0_1 , .IdList ; .StmtList
          => .K
           </k>
           <env>
             inc |-> LOC:Int
           </env>
           <store>
             LOC |-> (N:Int => ?_:Int)
           </store>
           <labels>
             $return |-> assert { : code "BP5003" , .AttrArgList }  { : source 0 , .AttrArgList }  .AttributeList true ; .StmtList
             $start |-> inc := 100 ; goto Head_0_1 , .IdList ; .StmtList
             Body_0_1 |-> inc := inc + 5 ; goto Head_0_1 , .IdList ; .StmtList
             Done_0_1 |-> assert .AttributeList inc > 99 ; goto $return , .IdList ; .StmtList
             Head_0_1 |-> assert .AttributeList inc > 99 ; goto Body_0_1 , Done_0_1 , .IdList ; .StmtList
           </labels>
           <exit-code>
             1
           </exit-code>
           <freshCounter>
             FreshCounter
           </freshCounter>
           <procs> _ </procs>
         </boogie>
     requires N >=Int 99

endmodule
```
