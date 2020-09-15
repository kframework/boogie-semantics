
function {:identity} LitInt(x: int) : int;

axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);

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

procedure Impl$$_module.__default._default_Main(n#0: int) returns ($_reverifyPost: bool);
  free requires 0 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.__default._default_Main(n#0: int) returns ($_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var sumTo#0: int;
  var sum#0: int;
  var iter#0: int;
  var $PreLoopHeap$loop#0: Heap;
  var $decr_init$loop#00: int;
  var $w$loop#0: bool;
  var $decr$loop#00: int;

  anon0:
    // AddMethodImpl: Main, Impl$$_module.__default._default_Main
    $_Frame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(2,0): initial state"} true;
    $_reverifyPost := false;
    havoc sumTo#0;
    havoc sum#0;
    havoc iter#0;
    // ----- assignment statement ----- test/dafny/sum/sum-to-n.dfy(6,10)
    assume true;
    assume true;
    sumTo#0 := LitInt(20);
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(6,13)"} true;
    // ----- assignment statement ----- test/dafny/sum/sum-to-n.dfy(7,8)
    assume true;
    assume true;
    sum#0 := LitInt(0);
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(7,10)"} true;
    // ----- assignment statement ----- test/dafny/sum/sum-to-n.dfy(8,9)
    assume true;
    assume true;
    iter#0 := LitInt(0);
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(8,11)"} true;
    // ----- while statement ----- test/dafny/sum/sum-to-n.dfy(10,5)
    // Assume Fuel Constant
    $PreLoopHeap$loop#0 := $Heap;
    $decr_init$loop#00 := sumTo#0 - iter#0;
    havoc $w$loop#0;
    goto anon7_LoopHead;

  anon7_LoopHead:  // cut point
    assume {:inferred} !$_reverifyPost
       && sumTo#0 == 20
       && 0 <= sum#0
       && 0 <= iter#0
       && $decr_init$loop#00 == 20;
    assume $w$loop#0 ==> true;
    assert $w$loop#0 ==> Mul(sum#0, LitInt(2)) == Mul(iter#0, iter#0 + 1);
    assume $w$loop#0 ==> true;
    assert $w$loop#0 ==> sumTo#0 - iter#0 >= LitInt(0);
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      { read($Heap, $o, $f) } 
      $o != null && read(old($Heap), $o, alloc)
         ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f));
    assume $HeapSucc($PreLoopHeap$loop#0, $Heap);
    assume (forall<alpha> $o: ref, $f: Field alpha :: 
      { read($Heap, $o, $f) } 
      $o != null && read($PreLoopHeap$loop#0, $o, alloc)
         ==> read($Heap, $o, $f) == read($PreLoopHeap$loop#0, $o, $f) || $_Frame[$o, $f]);
    assume sumTo#0 - iter#0 <= $decr_init$loop#00
       && (sumTo#0 - iter#0 == $decr_init$loop#00 ==> true);
    goto anon7_LoopDone, anon7_LoopBody;

  anon7_LoopBody:
    assume {:partition} true;
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(10,4): after some loop iterations"} true;
    goto anon8_Then, anon8_Else;

  anon8_Else:
    assume {:partition} $w$loop#0;
    assume true;
    goto anon9_Then, anon9_Else;

  anon9_Else:
    assume {:partition} iter#0 != sumTo#0;
    $decr$loop#00 := sumTo#0 - iter#0;
    // ----- assignment statement ----- test/dafny/sum/sum-to-n.dfy(15,14)
    assume true;
    assume true;
    iter#0 := iter#0 + 1;
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(15,24)"} true;
    // ----- assignment statement ----- test/dafny/sum/sum-to-n.dfy(16,13)
    assume true;
    assume true;
    sum#0 := sum#0 + iter#0;
    assume {:captureState "test/dafny/sum/sum-to-n.dfy(16,25)"} true;
    // ----- loop termination check ----- test/dafny/sum/sum-to-n.dfy(10,5)
    assert 0 <= $decr$loop#00 || sumTo#0 - iter#0 == $decr$loop#00;
    assert sumTo#0 - iter#0 < $decr$loop#00;
    assume true;
    assume true;
    goto anon7_LoopHead;

  anon9_Then:
    assume {:partition} iter#0 == sumTo#0;
    // ----- assert statement ----- test/dafny/sum/sum-to-n.dfy(19,5)
    assume true;
    assert sum#0 == LitInt(210);
    return;

  anon8_Then:
    assume {:partition} !$w$loop#0;
    assume true;
    assume Mul(sum#0, LitInt(2)) == Mul(iter#0, iter#0 + 1);
    assume true;
    assume sumTo#0 - iter#0 >= LitInt(0);
    assume true;
    assume false;
    return;

  anon7_LoopDone:
    assume {:partition} false;
    return;
}

// auto-generated lambda function
function lambda#0(l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool) : <alpha>[ref,Field alpha]bool;

// axiom (forall<alpha> $o: ref, $f: Field alpha, l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool :: 
//   { lambda#0(l#0, l#1, l#2, l#3)[$o, $f] } 
//   lambda#0(l#0, l#1, l#2, l#3)[$o, $f]
//      == ($o != l#0 && read(l#1, $o, l#2) ==> l#3));
