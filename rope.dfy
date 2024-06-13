function Max(a: nat, b: nat): nat {
  if a > b then a else b
}

function Fib(n: nat): nat
  decreases n
{
  if n < 2 then n else Fib(n - 2) + Fib(n - 1)
}
by method {
  var a: nat := 0;
  var b: nat := 1;
  for i := 0 to n
    invariant a == Fib(i) && b == Fib(i + 1)
  {
    a, b := b, a + b;
  }
  return a;
}

ghost function ConcatStrings(a: seq<string>): string
  decreases a
{
  if |a| == 0 then "" else a[0] + ConcatStrings(a[1..])
}

lemma ConcatStringsLemma(a: seq<string>, b: seq<string>)
  ensures ConcatStrings(a + b) == ConcatStrings(a) + ConcatStrings(b)
  decreases a
{
  if a == [] {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    ConcatStringsLemma(a[1..], b);
  }
}

ghost function Log2(n: nat): nat
  requires n > 0
  decreases n
{
  if n == 1 then 0 else 1 + Log2(n / 2)
}

lemma Log2Lemma(a: nat, b: nat)
  requires 0 < a <= b
  ensures Log2(a) <= Log2(b)
  decreases b
{
  if a < b {
    Log2Lemma(a, b - 1);
  }
}

ghost function Log2Ceil(n: nat): nat
  requires n > 0
  decreases n
{
  if n == 1 then 0 else Log2(n - 1) + 1
}

lemma Log2CeilLemma(a: nat, b: nat)
  requires 0 < a <= b
  ensures Log2Ceil(a) <= Log2Ceil(b)
  decreases b
{
  if 1 < a < b {
    Log2Lemma(a - 1, b - 1);
    Log2CeilLemma(a, b - 1);
  }
}

lemma FibLog2CeilLemma(n: nat)
  requires n > 0
  ensures Fib(Log2Ceil(n) + 2) <= n
  decreases n
{
  if n <= 2 {
    assert Fib(Log2Ceil(n) + 2) == n;
  } else {
    FibLog2CeilLemma(n - n / 2);
  }
}

datatype Stack = Nil | Cons(v: Rope, l: bool, n: Stack)

ghost function StackFootprint(stk: Stack): set<Rope>
  ensures stk.Cons? ==> StackFootprint(stk.n) <= StackFootprint(stk)
  decreases stk
{
  if stk.Cons? then StackFootprint(stk.n) + {stk.v} + stk.v.footprint else {}
}

class Rope {
  const data: string
  const left: Rope?
  const right: Rope?
  const len: nat
  const height: nat
  ghost const footprint: set<Rope>

  predicate IsLeaf()
    reads this
  {
    left == null && right == null
  }

  ghost predicate Valid()
    reads this, footprint
    decreases len, height, footprint
  {
    this in footprint &&
    (IsLeaf() ==> |data| == len && height == 0) &&
    (left != null ==>
       left in footprint &&
       left.footprint <= footprint &&
       this !in left.footprint) &&
    (right != null ==>
       right in footprint &&
       right.footprint <= footprint &&
       this !in right.footprint) &&
    (!IsLeaf() ==>
       data == "" &&
       left != null && right != null &&
       left.len > 0 && right.len > 0 &&
       len == left.len + right.len &&
       height == Max(left.height, right.height) + 1 &&
       left.Valid() && right.Valid())
  }

  function ToString(): (s: string)
    reads this, footprint
    requires Valid()
    ensures |s| == len
    ensures !IsLeaf() ==> s[0..left.len] == left.ToString()
    ensures !IsLeaf() ==> s[left.len..|s|] == right.ToString()
    decreases len, height, footprint
  {
    if IsLeaf() then data else left.ToString() + right.ToString()
  }

  function CharAt(idx: nat): (c: char)
    reads this, footprint
    requires Valid()
    requires 0 <= idx < len
    ensures c == ToString()[idx]
    decreases len, height, footprint
  {
    if IsLeaf() then data[idx]
    else if idx < left.len then left.CharAt(idx)
    else right.CharAt(idx - left.len)
  }

  function Substring(lo: nat, hi: nat): (s: string)
    reads this, footprint
    requires Valid()
    requires 0 <= lo <= hi <= len
    ensures |s| == hi - lo
    ensures s == ToString()[lo..hi]
    decreases len, height, footprint
  {
    if IsLeaf() then data[lo..hi]
    else if hi <= left.len then left.Substring(lo, hi)
    else if lo >= left.len then right.Substring(lo - left.len, hi - left.len)
    else left.Substring(lo, left.len) + right.Substring(0, hi - left.len)
  }

  constructor FromString(s: string)
    ensures Valid()
    ensures fresh(footprint)
    ensures ToString() == s
    ensures IsLeaf()
  {
    data := s;
    left := null;
    right := null;
    len := |s|;
    height := 0;
    footprint := {this};
  }

  constructor Copy(x: Rope)
    requires x.Valid()
    ensures Valid()
    ensures fresh(footprint)
    ensures ToString() == x.ToString()
    ensures height == x.height
    decreases x.len, x.height, x.footprint
  {
    data := x.data;
    len := x.len;
    height := x.height;
    if x.IsLeaf() {
      left := null;
      right := null;
      footprint := {this};
    } else {
      var l := new Rope.Copy(x.left);
      var r := new Rope.Copy(x.right);
      left := l;
      right := r;
      footprint := {this} + l.footprint + r.footprint;
    }
  }

  constructor Concat(l: Rope, r: Rope)
    requires l.Valid() && r.Valid()
    ensures Valid()
    ensures ToString() == l.ToString() + r.ToString()
    ensures height <= Max(l.height, r.height) + 1
    ensures l.len > 0 && r.len > 0 ==> height == Max(l.height, r.height) + 1
  {
    len := l.len + r.len;
    if l.len == 0 {
      data := r.data;
      left := r.left;
      right := r.right;
      height := r.height;
      footprint := r.footprint - {r} + {this};
    } else if r.len == 0 {
      data := l.data;
      left := l.left;
      right := l.right;
      height := l.height;
      footprint := l.footprint - {l} + {this};
    } else {
      data := "";
      left := l;
      right := r;
      height := Max(l.height, r.height) + 1;
      footprint := {this} + l.footprint + r.footprint;
    }
  }

  method PrependString(s: string) returns (x: Rope)
    requires Valid()
    ensures x.Valid()
    ensures x.ToString() == s + ToString()
    ensures x.height == height
    decreases len, height, footprint
  {
    if |s| == 0 {
      return this;
    }
    if IsLeaf() {
      return new Rope.FromString(s + data);
    }
    var l := left.PrependString(s);
    var r := right;
    return new Rope.Concat(l, r);
  }

  method AppendString(s: string) returns (x: Rope)
    requires Valid()
    ensures x.Valid()
    ensures x.ToString() == ToString() + s
    ensures x.height == height
    decreases len, height, footprint
  {
    if |s| == 0 {
      return this;
    }
    if IsLeaf() {
      return new Rope.FromString(data + s);
    }
    var l := left;
    var r := right.AppendString(s);
    return new Rope.Concat(l, r);
  }

  method Split(idx: nat) returns (l: Rope, r: Rope)
    requires Valid()
    requires 0 <= idx <= len
    ensures l.Valid() && r.Valid()
    ensures l.ToString() == ToString()[..idx]
    ensures r.ToString() == ToString()[idx..]
    ensures Max(l.height, r.height) <= height
    decreases len, height, footprint
  {
    if idx == 0 {
      l := new Rope.FromString("");
      r := this;
    } else if idx == len {
      l := this;
      r := new Rope.FromString("");
    } else if IsLeaf() {
      l := new Rope.FromString(data[..idx]);
      r := new Rope.FromString(data[idx..]);
    } else if idx == left.len {
      l := left;
      r := right;
    } else if idx < left.len {
      var ll, lr := left.Split(idx);
      l := ll;
      r := new Rope.Concat(lr, right);
    } else {
      var rl, rr := right.Split(idx - left.len);
      l := new Rope.Concat(left, rl);
      r := rr;
    }
  }

  static ghost function LeavesToStrings(leaves: seq<Rope>): seq<string>
    reads leaves
    requires forall x | x in leaves :: x.IsLeaf()
  {
    seq<string>(|leaves|, i requires 0 <= i < |leaves| => leaves[i].data)
  }

  method CollectLeaves() returns (leaves: seq<Rope>)
    requires Valid()
    ensures |leaves| > 0
    ensures forall x | x in leaves :: x.Valid() && x.IsLeaf()
    ensures len > 0 ==> forall x | x in leaves :: x.len > 0
    ensures ConcatStrings(LeavesToStrings(leaves)) == ToString()
    decreases len, height, footprint
  {
    if IsLeaf() {
      return [this];
    }
    var ls := left.CollectLeaves();
    var rs := right.CollectLeaves();
    leaves := ls + rs;
    ghost var lss := LeavesToStrings(ls);
    ghost var rss := LeavesToStrings(rs);
    ghost var ss := LeavesToStrings(leaves);
    assert ss == lss + rss;
    ConcatStringsLemma(lss, rss);
  }

  predicate IsBalanced()
    reads this, footprint
    requires Valid()
  {
    len >= Fib(height + 2)
  }

  static method MergeLeaves(leaves: seq<Rope>) returns (x: Rope)
    requires |leaves| > 0
    requires forall x | x in leaves :: x.Valid() && x.IsLeaf() && x.len > 0
    ensures x.Valid()
    ensures x.len >= |leaves|
    ensures x.ToString() == ConcatStrings(LeavesToStrings(leaves))
    ensures x.height == Log2Ceil(|leaves|)
    ensures x.IsBalanced()
    decreases leaves
  {
    if |leaves| == 1 {
      return leaves[0];
    }
    var mid: nat := |leaves| / 2;
    var l := MergeLeaves(leaves[..mid]);
    var r := MergeLeaves(leaves[mid..]);
    x := new Rope.Concat(l, r);
    ghost var ss := LeavesToStrings(leaves);
    ghost var lss := LeavesToStrings(leaves[..mid]);
    ghost var rss := LeavesToStrings(leaves[mid..]);
    assert lss + rss == ss;
    ConcatStringsLemma(lss, rss);
    Log2CeilLemma(|leaves[..mid]|, |leaves[mid..]|);
    FibLog2CeilLemma(|leaves|);
  }

  method Rebalance() returns (x: Rope)
    requires Valid()
    ensures x.Valid()
    ensures x.ToString() == ToString()
    ensures x.len > 0 ==> x.IsBalanced()
  {
    if (len == 0 || IsBalanced()) {
      return this;
    }
    var leaves := CollectLeaves();
    x := MergeLeaves(leaves);
  }

  ghost predicate ValidStack(stk: Stack): (valid: bool)
    reads this, footprint, StackFootprint(stk)
    requires Valid()
    ensures valid ==> stk.Cons? && stk.v.Valid()
    decreases stk
  {
    if stk.Cons? then
      if stk.n.Cons? then
        stk.v == (if stk.l then stk.n.v.left else stk.n.v.right) &&
        ValidStack(stk.n)
      else
        stk.v == this
    else
      false
  }

  ghost function LenBeforeStack(stk: Stack): (pre: nat)
    reads this, footprint, StackFootprint(stk)
    requires Valid()
    requires ValidStack(stk)
    ensures 0 <= pre <= len - stk.v.len
    ensures stk.v.ToString() == Substring(pre, pre + stk.v.len)
    decreases stk
  {
    if stk.n.Cons? then
      if stk.l then
        LenBeforeStack(stk.n)
      else
        LenBeforeStack(stk.n) + stk.n.v.left.len
    else
      0
  }
}

class RopeIter {
  const owner: Rope
  var stack: Stack
  var offset: nat
  ghost var index: nat

  ghost predicate Valid(): (valid: bool)
    reads this, owner, owner.footprint, StackFootprint(stack)
  {
    owner.Valid() &&
    owner.ValidStack(stack) &&
    stack.v.IsLeaf() &&
    0 <= offset < stack.v.len &&
    index - offset == owner.LenBeforeStack(stack)
  }

  function Current(): (c: char)
    reads this, owner, owner.footprint, StackFootprint(stack)
    requires Valid()
    ensures c == owner.CharAt(index)
  {
    stack.v.data[offset]
  }

  constructor(x: Rope, idx: nat)
    requires x.Valid()
    requires 0 <= idx < x.len
    ensures Valid()
    ensures index == idx
  {
    var stk: Stack := Cons(x, true, Nil);
    var off: nat := idx;
    while !stk.v.IsLeaf()
      invariant x.ValidStack(stk)
      invariant 0 <= off < stk.v.len
      invariant idx - off == x.LenBeforeStack(stk)
      decreases stk.v.len, stk.v.height, stk.v.footprint
    {
      if off < stk.v.left.len {
        stk := Cons(stk.v.left, true, stk);
      } else {
        off := off - stk.v.left.len;
        stk := Cons(stk.v.right, false, stk);
      }
    }
    owner := x;
    stack := stk;
    offset := off;
    index := idx;
  }

  constructor Copy(it: RopeIter)
    requires it.Valid()
    ensures Valid()
    ensures owner == it.owner
    ensures stack == it.stack
    ensures offset == it.offset
    ensures index == it.index
  {
    owner := it.owner;
    stack := it.stack;
    offset := it.offset;
    index := it.index;
  }

  method Move(cnt: int) returns (success: bool)
    requires Valid()
    modifies this
    ensures Valid()
    ensures 0 <= old(index) + cnt < owner.len ==> success
    ensures success ==> index == old(index) + cnt
    ensures !success ==> index == old(index)
  {
    var stk: Stack := stack;
    var off: nat := offset;
    var idx: nat := index;
    while stk.n.Cons? && !(0 <= off + cnt < stk.v.len)
      invariant owner.ValidStack(stk)
      invariant idx - off == owner.LenBeforeStack(stk)
      decreases stk
    {
      off := off + if stk.l then 0 else stk.n.v.left.len;
      stk := stk.n;
    }
    if !(0 <= off + cnt < stk.v.len) {
      return false;
    }
    off := off + cnt;
    idx := idx + cnt;
    while !stk.v.IsLeaf()
      invariant owner.ValidStack(stk)
      invariant 0 <= off < stk.v.len
      invariant idx - off == owner.LenBeforeStack(stk)
      decreases stk.v.len, stk.v.height, stk.v.footprint
    {
      if off < stk.v.left.len {
        stk := Cons(stk.v.left, true, stk);
      } else {
        off := off - stk.v.left.len;
        stk := Cons(stk.v.right, false, stk);
      }
    }
    stack := stk;
    offset := off;
    index := idx;
    return true;
  }
}
