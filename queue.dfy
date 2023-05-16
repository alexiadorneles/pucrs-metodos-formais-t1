ghost predicate ContentIsValid(Content: seq<int>, a: array<int>, head: nat, contentSize:nat, ArraySize: nat)
  requires a.Length == ArraySize
  requires ArraySize == 0 ==> contentSize == head == 0 && Content == []
  requires ArraySize != 0 ==> contentSize <= ArraySize && head < ArraySize
  reads a
{
  (Content == if head + contentSize <= ArraySize then a[head..head+contentSize]
              else a[head..] + a[..head+contentSize-ArraySize])
}


class {:autocontracts} Queue {

  ghost var Content: seq<int>;
  ghost var ArraySize: nat

  var a: array<int>
  var head: nat
  var contentSize: nat

  ghost predicate Valid() {
    (a.Length == ArraySize) &&
    (ArraySize == 0 ==> contentSize == head == 0 && Content == []) &&
    (ArraySize != 0 ==> contentSize <= ArraySize && head < ArraySize) &&
    (Content == if head + contentSize <= ArraySize then a[head..head+contentSize]
                else a[head..] + a[..head+contentSize-ArraySize])
  }

  constructor(initialSize: nat)
    ensures Content == []
    ensures ArraySize == initialSize
    ensures head == 0
  {
    a := new int[initialSize];
    head, contentSize := 0, 0;
    Content, ArraySize := [], initialSize;
  }

  method enqueue(e: int)
    ensures Content == old(Content) + [e]
    ensures ArraySize >= old(ArraySize)
  {
    if a.Length == contentSize {
      // duplica o size da array
      var additionalSpace := a.Length + 1;
      var newArray := new int[a.Length + additionalSpace];

      forall i | 0 <= i < a.Length {
        newArray[if i < head then i else i + additionalSpace] := a[i];
      }

      ArraySize := ArraySize + additionalSpace;
      a := newArray;
      head := if contentSize == 0 then 0 else head + additionalSpace;
    }

    var tail := if head + contentSize < a.Length then head + contentSize  else head + contentSize - a.Length;
    a[tail] := e;
    contentSize := contentSize + 1;
    Content := Content + [e];
  }

  method dequeue() returns (e: int)
    requires |Content| > 0
    ensures Content == old(Content)[1..]
    ensures old(Content)[0] == e
  {
    e := a[head];
    assert e == Content[0];
    head := if head + 1 == a.Length then 0 else head + 1;
    contentSize := contentSize - 1;
    Content := Content[1..];
  }

  method contains(el: int) returns (r: bool)
    requires |Content| > 0
    ensures Content == old(Content)
    ensures r <==> el in Content
  {
    var i := head;
    var ContentCopy := Content;
    r := false;

    var count := 0;
    while count < contentSize
      invariant 0 <= i < a.Length
      invariant 0 <= count <= contentSize
      invariant ContentIsValid(Content[count..], a, i, contentSize - count, ArraySize)

      invariant Content[count..] == ContentCopy
      invariant forall j : nat :: 0 <= j < count ==> Content[j] != el
    {
      var e := a[i];
      assert e == ContentCopy[0];
      assert e in Content;
      if (e == el) {
        r:= true;
        return;
      }
      count := count + 1;
      i:= if i + 1 == a.Length then 0 else i + 1;
      ContentCopy := ContentCopy[1..];
    }
  }

  function size(): nat
    ensures size() == |Content|
  {
    contentSize
  }

  function isEmpty(): bool
    ensures isEmpty() == (|Content| == 0) {
    contentSize == 0
  }

  method concat(queue: Queue) returns (newQueue: Queue)
    requires queue.Valid()
    requires |queue.Content| > 0
    requires |Content| > 0

    ensures queue.a == old(queue.a)
    ensures queue.Content == old(queue.Content)
    ensures Content == old(Content)
    ensures newQueue.Content == Content + queue.Content
  {
    newQueue := new Queue(contentSize + queue.contentSize);

    var count := 0;
    var i := head;

    while count < contentSize
      invariant 0 <= i < a.Length
      invariant 0 <= count <= contentSize

      invariant Content == old(Content)
      invariant a == old(a)
      invariant Valid()
      invariant Repr == old(Repr)

      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant queue.Valid()

      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count
      invariant newQueue.Valid()
    {
      var value := a[i];
      newQueue.enqueue(value);
      i := if i + 1 == a.Length then 0 else i + 1;
      count := count + 1;
    }

    count := 0;
    i := queue.head;
    var index := newQueue.contentSize;
    while count < queue.contentSize
      invariant 0 <= i < queue.a.Length
      invariant 0 <= index <= newQueue.a.Length

      invariant index - count == contentSize
      invariant Content == old(Content)
      invariant a == old(a)
      invariant Valid()
      invariant Repr == old(Repr)

      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant queue.Valid()

      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count + contentSize
      invariant newQueue.Valid()
    {
      var value := queue.a[i];
      newQueue.enqueue(value);

      i := if i + 1 == queue.a.Length then 0 else i + 1;
      count := count + 1;
      index := index + 1;
    }

    newQueue.Content := Content + queue.Content;

  }
}

method Print(fila: Queue) {
  print("\n\n");
  var i := 0;
  while i < fila.a.Length{
    print(fila.a[i]);
    print("  ");
    i := i + 1;
  }
}

method Main() {
  var fila := new Queue(3);

  // enqueue deve alocar mais espaço
  fila.enqueue(1);
  fila.enqueue(2);
  fila.enqueue(3);
  fila.enqueue(4);
  assert fila.Content == [1, 2, 3, 4];

  // size
  var q := fila.size();
  assert q == 4;

  // dequeue
  var e := fila.dequeue();
  assert e == 1;
  assert fila.Content == [2, 3, 4];
  assert fila.size() == 3;

  // contains
  assert fila.Content == [2, 3, 4];
  var r := fila.contains(1);
  assert r == false;
  var r2 := fila.contains(2);
  assert r2 == true;

  // isEmpty
  var vazia := fila.isEmpty();
  assert vazia == false;
  var outraFila := new Queue(3);
  vazia := outraFila.isEmpty();
  assert vazia == true;

  // concat
  assert fila.Content == [2, 3, 4];
  outraFila.enqueue(5);
  outraFila.enqueue(6);
  outraFila.enqueue(7);
  assert outraFila.Content == [5, 6, 7];
  var concatenada := fila.concat(outraFila);
  assert concatenada.Content == [2,3,4,5,6,7];
}