/*
  Insert a new linked list node after a given node.
  Original example from "Le Goues, Leino, Moskal: The Boogie Verification Debugger (SEFM 2011)".
*/

type ref;

var next: [ref] ref;
const null: ref;

function sublist(nxt: [ref] ref, node: ref, list: ref): bool
{
  if node == list || node == null
  then true
  else if list == null
    then false
    else sublist(nxt, node, nxt[list])
}

// Insert new after node
procedure InsertAfter(node, new: ref) returns ()
  requires node != new;
  modifies next;
  ensures next[new] == old(next[node]);
{
  next[new] := next[node];
  next[node] := new;
}

// Add 3 elements to a single-element list.
procedure main() returns (head: ref)
  modifies next;
{
  var node: ref;
  var i: int;
  var new_node: ref;

  assume head != null && next[head] == null;

  i := 0;

  node := head;

  while (i < 3)
  {
    havoc new_node;
    assume !sublist(next, new_node, head);
    call InsertAfter(node, new_node);
    node := new_node;
    i := i + 1;
  }
}
