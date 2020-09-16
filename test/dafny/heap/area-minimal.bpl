type Ty;

const unique TInt: Ty;

type TyTag;

function Tag(Ty) : TyTag;

function {:identity} LitInt(x: int) : int;

axiom (forall x: int :: {:identity} { LitInt(x): int } LitInt(x): int == x);

type ref;

const null: ref;

type Box;

function $Box<T>(T) : Box;

function $Unbox<T>(Box) : T;

axiom (forall<T> x: T :: { $Box(x) } $Unbox($Box(x)) == x);

function $Is<T>(T, Ty) : bool;

function $IsAlloc<T>(T, Ty, Heap) : bool;

function $IsBox<T>(T, Ty) : bool;

type ClassName;

function dtype(ref) : Ty;

const $FunctionContextHeight: int;

type Field _;

function FDim<T>(Field T) : int;

type NameFamily;

function FieldOfDecl<alpha>(ClassName, NameFamily) : Field alpha;

function $IsGhostField<T>(Field T) : bool;

const unique alloc: Field bool;

type Heap = <alpha>[ref,Field alpha]alpha;

function {:inline} read<alpha>(H: Heap, r: ref, f: Field alpha) : alpha
{
  H[r, f]
}

function {:inline} update<alpha>(H: Heap, r: ref, f: Field alpha, v: alpha) : Heap
{
  H[r, f := v]
}

function $IsGoodHeap(Heap) : bool;

function $IsHeapAnchor(Heap) : bool;

var $Heap: Heap where $IsGoodHeap($Heap) && $IsHeapAnchor($Heap);

const $OneHeap: Heap;

axiom $IsGoodHeap($OneHeap);

function $HeapSucc(Heap, Heap) : bool;

axiom (forall<alpha> h: Heap, r: ref, f: Field alpha, x: alpha :: 
  { update(h, r, f, x) } 
  $IsGoodHeap(update(h, r, f, x)) ==> $HeapSucc(h, update(h, r, f, x)));

axiom (forall a: Heap, b: Heap, c: Heap :: 
  { $HeapSucc(a, b), $HeapSucc(b, c) } 
  $HeapSucc(a, b) && $HeapSucc(b, c) ==> $HeapSucc(a, c));

axiom (forall h: Heap, k: Heap :: 
  { $HeapSucc(h, k) } 
  $HeapSucc(h, k)
     ==> (forall o: ref :: { read(k, o, alloc) } read(h, o, alloc) ==> read(k, o, alloc)));

type TickType;

var $Tick: TickType;

function Mul(x: int, y: int) : int;

axiom (forall x: int, y: int :: { Mul(x, y): int } Mul(x, y): int == x * y);

const unique class._module.Rectangle?: ClassName;

function Tclass._module.Rectangle?() : Ty;

// Tclass._module.Rectangle? Tag
axiom Tag(Tclass._module.Rectangle?()) == Tagclass._module.Rectangle?;

const unique Tagclass._module.Rectangle?: TyTag;

// Box/unbox axiom for Tclass._module.Rectangle?
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Rectangle?()) } 
  $IsBox(bx, Tclass._module.Rectangle?())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Rectangle?()));

// Rectangle: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.Rectangle?()) } 
  $Is($o, Tclass._module.Rectangle?())
     <==> $o == null || dtype($o) == Tclass._module.Rectangle?());

// Rectangle: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.Rectangle?(), $h) } 
  $IsAlloc($o, Tclass._module.Rectangle?(), $h)
     <==> $o == null || read($h, $o, alloc));

axiom FDim(_module.Rectangle.x) == 0
   && FieldOfDecl(class._module.Rectangle?, field$x) == _module.Rectangle.x
   && !$IsGhostField(_module.Rectangle.x);

const _module.Rectangle.x: Field int;

// Rectangle.x: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Rectangle.x) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Rectangle?()
     ==> $Is(read($h, $o, _module.Rectangle.x), TInt));

// Rectangle.x: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Rectangle.x) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Rectangle?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Rectangle.x), TInt, $h));

axiom FDim(_module.Rectangle.y) == 0
   && FieldOfDecl(class._module.Rectangle?, field$y) == _module.Rectangle.y
   && !$IsGhostField(_module.Rectangle.y);

const _module.Rectangle.y: Field int;

// Rectangle.y: Type axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Rectangle.y) } 
  $IsGoodHeap($h) && $o != null && dtype($o) == Tclass._module.Rectangle?()
     ==> $Is(read($h, $o, _module.Rectangle.y), TInt));

// Rectangle.y: Allocation axiom
axiom (forall $h: Heap, $o: ref :: 
  { read($h, $o, _module.Rectangle.y) } 
  $IsGoodHeap($h)
       && 
      $o != null
       && dtype($o) == Tclass._module.Rectangle?()
       && read($h, $o, alloc)
     ==> $IsAlloc(read($h, $o, _module.Rectangle.y), TInt, $h));

function Tclass._module.Rectangle() : Ty;

// Tclass._module.Rectangle Tag
axiom Tag(Tclass._module.Rectangle()) == Tagclass._module.Rectangle;

const unique Tagclass._module.Rectangle: TyTag;

// Box/unbox axiom for Tclass._module.Rectangle
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.Rectangle()) } 
  $IsBox(bx, Tclass._module.Rectangle())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.Rectangle()));

procedure CheckWellformed$$_module.Rectangle.Init(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Rectangle())
         && $IsAlloc(this, Tclass._module.Rectangle(), $Heap), 
    x#0: int, 
    y#0: int);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Rectangle.Init(x#0: int, y#0: int)
   returns (this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Rectangle())
         && $IsAlloc(this, Tclass._module.Rectangle(), $Heap));
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Rectangle.x) == x#0;
  free ensures true;
  ensures read($Heap, this, _module.Rectangle.y) == y#0;
  // constructor allocates the object
  ensures !read(old($Heap), this, alloc);
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Rectangle.Init(x#0: int, y#0: int)
   returns (this: ref where this != null && $Is(this, Tclass._module.Rectangle()), 
    $_reverifyPost: bool);
  free requires 1 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures read($Heap, this, _module.Rectangle.x) == x#0;
  free ensures true;
  ensures read($Heap, this, _module.Rectangle.y) == y#0;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



implementation Impl$$_module.Rectangle.Init(x#0: int, y#0: int) returns (this: ref, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;
  var this.x: int;
  var this.y: int;

  anon0:
    // AddMethodImpl: Init, Impl$$_module.Rectangle.Init
    $_Frame := lambda#0(null, $Heap, alloc, false);
    assume {:captureState "area.dfy(9,4): initial state"} true;
    $_reverifyPost := false;
    // ----- divided block before new; ----- area.dfy(9,5)
    // ----- assignment statement ----- area.dfy(10,16)
    assume true;
    assume true;
    this.x := x#0;
    assume {:captureState "area.dfy(10,19)"} true;
    // ----- assignment statement ----- area.dfy(11,16)
    assume true;
    assume true;
    this.y := y#0;
    assume {:captureState "area.dfy(11,19)"} true;
    // ----- new; ----- area.dfy(9,5)
    assume !read($Heap, this, alloc);
    assume read($Heap, this, _module.Rectangle.x) == this.x;
    assume read($Heap, this, _module.Rectangle.y) == this.y;
    $Heap := update($Heap, this, alloc, true);
    assume $IsGoodHeap($Heap);
    assume $IsHeapAnchor($Heap);
    // ----- divided block after new; ----- area.dfy(9,5)
    return;
}



procedure CheckWellformed$$_module.Rectangle.area(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Rectangle())
         && $IsAlloc(this, Tclass._module.Rectangle(), $Heap))
   returns (a#0: int);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.Rectangle.area(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Rectangle())
         && $IsAlloc(this, Tclass._module.Rectangle(), $Heap))
   returns (a#0: int);
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures a#0
     == Mul(read($Heap, this, _module.Rectangle.x), read($Heap, this, _module.Rectangle.y));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.Rectangle.area(this: ref
       where this != null
         && 
        $Is(this, Tclass._module.Rectangle())
         && $IsAlloc(this, Tclass._module.Rectangle(), $Heap))
   returns (a#0: int, $_reverifyPost: bool);
  free requires 2 == $FunctionContextHeight;
  modifies $Heap, $Tick;
  // user-defined postconditions
  free ensures true;
  ensures a#0
     == Mul(read($Heap, this, _module.Rectangle.x), read($Heap, this, _module.Rectangle.y));
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);


implementation Impl$$_module.Rectangle.area(this: ref) returns (a#0: int, $_reverifyPost: bool)
{
  var $_Frame: <beta>[ref,Field beta]bool;

  anon0:
    // AddMethodImpl: area, Impl$$_module.Rectangle.area
    $_Frame := lambda#1(null, $Heap, alloc, false);
    assume {:captureState "area.dfy(14,64): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- area.dfy(15,11)
    assume true;
    assume true;
    a#0 := Mul(read($Heap, this, _module.Rectangle.x), read($Heap, this, _module.Rectangle.y));
    assume {:captureState "area.dfy(15,28)"} true;
    return;
}


// _module.Rectangle: subset type $Is
axiom (forall c#0: ref :: 
  { $Is(c#0, Tclass._module.Rectangle()) } 
  $Is(c#0, Tclass._module.Rectangle())
     <==> $Is(c#0, Tclass._module.Rectangle?()) && c#0 != null);

// _module.Rectangle: subset type $IsAlloc
axiom (forall c#0: ref, $h: Heap :: 
  { $IsAlloc(c#0, Tclass._module.Rectangle(), $h) } 
  $IsAlloc(c#0, Tclass._module.Rectangle(), $h)
     <==> $IsAlloc(c#0, Tclass._module.Rectangle?(), $h));

const unique class._module.__default: ClassName;

function Tclass._module.__default() : Ty;

// Tclass._module.__default Tag
axiom Tag(Tclass._module.__default()) == Tagclass._module.__default;

const unique Tagclass._module.__default: TyTag;

// Box/unbox axiom for Tclass._module.__default
axiom (forall bx: Box :: 
  { $IsBox(bx, Tclass._module.__default()) } 
  $IsBox(bx, Tclass._module.__default())
     ==> $Box($Unbox(bx): ref) == bx && $Is($Unbox(bx): ref, Tclass._module.__default()));

// _default: Class $Is
axiom (forall $o: ref :: 
  { $Is($o, Tclass._module.__default()) } 
  $Is($o, Tclass._module.__default())
     <==> $o == null || dtype($o) == Tclass._module.__default());

// _default: Class $IsAlloc
axiom (forall $o: ref, $h: Heap :: 
  { $IsAlloc($o, Tclass._module.__default(), $h) } 
  $IsAlloc($o, Tclass._module.__default(), $h)
     <==> $o == null || read($h, $o, alloc));

procedure CheckWellformed$$_module.__default.Main();
  free requires 3 == $FunctionContextHeight;
  modifies $Heap, $Tick;



procedure Call$$_module.__default.Main();
  modifies $Heap, $Tick;
  // frame condition
  free ensures (forall<alpha> $o: ref, $f: Field alpha :: 
    { read($Heap, $o, $f) } 
    $o != null && read(old($Heap), $o, alloc)
       ==> read($Heap, $o, $f) == read(old($Heap), $o, $f));
  // boilerplate
  free ensures $HeapSucc(old($Heap), $Heap);



procedure Impl$$_module.__default.Main() returns ($_reverifyPost: bool);
  free requires 3 == $FunctionContextHeight;
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
  var r#0: ref
     where $Is(r#0, Tclass._module.Rectangle())
       && $IsAlloc(r#0, Tclass._module.Rectangle(), $Heap);
  var $nw: ref;
  var x##0: int;
  var y##0: int;
  var a#0: int;
  var $rhs##0: int;

  anon0:
    // AddMethodImpl: Main, Impl$$_module.__default.Main
    $_Frame := lambda#2(null, $Heap, alloc, false);
    assume {:captureState "area.dfy(20,14): initial state"} true;
    $_reverifyPost := false;
    // ----- assignment statement ----- area.dfy(21,22)
    assume true;
    // ----- init call statement ----- area.dfy(21,39)
    // TrCallStmt: Before ProcessCallStmt
    assume true;
    // ProcessCallStmt: CheckSubrange
    x##0 := LitInt(4);
    assume true;
    // ProcessCallStmt: CheckSubrange
    y##0 := LitInt(5);
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $nw := Call$$_module.Rectangle.Init(x##0, y##0);
    // TrCallStmt: After ProcessCallStmt
    assume {:captureState "area.dfy(21,48)"} true;
    r#0 := $nw;
    assume {:captureState "area.dfy(21,48)"} true;
    // ----- call statement ----- area.dfy(22,25)
    assume true;
    // TrCallStmt: Adding lhs Microsoft.Dafny.AutoGhostIdentifierExpr with type int
    // TrCallStmt: Before ProcessCallStmt
    assert r#0 != null;
    assert (forall<alpha> $o: ref, $f: Field alpha :: false ==> $_Frame[$o, $f]);
    // ProcessCallStmt: Make the call
    call $rhs##0 := Call$$_module.Rectangle.area(r#0);
    // TrCallStmt: After ProcessCallStmt
    a#0 := $rhs##0;
    assume {:captureState "area.dfy(22,26)"} true;
    // ----- assert statement ----- area.dfy(23,5)
    assume true;
    assert a#0 == LitInt(20);
    return;
}



const unique field$x: NameFamily;

const unique field$y: NameFamily;

// auto-generated lambda function
function lambda#0(l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool) : <alpha>[ref,Field alpha]bool;

// auto-generated lambda function
function lambda#1(l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool) : <alpha>[ref,Field alpha]bool;

// auto-generated lambda function
function lambda#2(l#0: ref, l#1: Heap, l#2: Field bool, l#3: bool) : <alpha>[ref,Field alpha]bool;
