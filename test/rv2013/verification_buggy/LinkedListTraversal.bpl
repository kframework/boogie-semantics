// RUN: %boogie "%s" > "%t"
// RUN: %diff "%s".expect "%t"
/*
  Calculating the length of a linked list.

  Error:
  - No acyclicity constraint; the loop invariant fails on cyclic lists.
    Note that the postcondition would not fail, because it is only reachable for finite executions, i.e. for acyclic lists.
*/

// Reference type
type ref;

// Null-reference
const null: ref;
// Maps a list node to the next node
const next: [ref] ref;
// Head node of the list
const head: ref;

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
