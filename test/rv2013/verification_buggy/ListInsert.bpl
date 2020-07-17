/*
  Insert a new linked list node after a given node.
  Original example from "Le Goues, Leino, Moskal: The Boogie Verification Debugger (SEFM 2011)".
  
  Errors: 
  - If the two nodes are aliased the postcondition is violated.
*/

type ref;

var data: [ref] int;
var next: [ref] ref;

// Insert new after node
procedure InsertAfter(node, new: ref) returns ()
  modifies next;
  ensures next[new] == old(next[node]);
{
  next[new] := next[node];
  next[node] := new;
}