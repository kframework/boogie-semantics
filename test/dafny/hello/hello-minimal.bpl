
type ref;

const null: ref;

const $FunctionContextHeight: int;

type Field _;

const unique alloc: Field bool;

type Heap = <alpha>[ref,Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r, f]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

function $HeapSucc(Heap, Heap) : bool;

type TickType;

var $Tick: TickType;

procedure Impl$$_module.__default.Main() returns ($_reverifyPost: bool);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default.Main() returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

  anon0:
    // AddMethodImpl: Main, Impl$$_module.__default.Main
    $_Frame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "test/dafny/hello/hello.dfy(1,14): initial state"} true;
    $_reverifyPost := false;
    // ----- print statement ----- test/dafny/hello/hello.dfy(2,3)
    assume true;
    // ----- assert statement ----- test/dafny/hello/hello.dfy(3,3)
    assume true;
    assert 10 > 2;
    return;
}

// auto-generated lambda function
function lambda#0(l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool) : <alpha>[ref,Field alpha]bool;
