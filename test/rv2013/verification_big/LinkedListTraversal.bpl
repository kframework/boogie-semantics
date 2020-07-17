// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  Calculating the length of a linked list.
*/

// Reference type
type ref;

// Null-reference
const null: ref;
// Maps a list node to the next node
const next: [ref] ref;
// Head node of the list
const head: ref;

// Indexes of node (used to express acyclicity)
function index(node: ref): int;

// All lists linked by the next field are acyclic;
axiom index(null) == 0;
axiom (forall node: ref :: node != null ==> index(next[node]) == index(node) + 1);

// How many times next should be applied to reach node' starting from node?
function distance(node, node': ref): int
{
  if node == node'
    then 0
    else distance(next[node], node') + 1
}

// Distance from node to null
function length(node: ref): int
{ distance(node, null) }

// Traverse the list starting from head and return its length
procedure main() returns (n: int)
  requires length(head) == 7;
  ensures n == length(head);
{
  var node: ref;
  node := head;
  n := 0;

  while (node != null)
    invariant n == distance(head, node);
  {
    node := next[node];
    n := n + 1;
  }
}
