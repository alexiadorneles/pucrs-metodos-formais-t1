ghost predicate DifferentQueues(q1: Queue, q2: Queue)
  reads q1, q2
{
  q1.a != q2.a && q1.Content != q2.Content && q1 != q2
}

ghost predicate ContentIsValid(Content: seq<int>, a: array<int>, head: nat, contentSize:nat, MaxSize: nat)
  requires a.Length == MaxSize
  requires MaxSize == 0 ==> contentSize == head == 0 && Content == []
  requires MaxSize != 0 ==> contentSize <= MaxSize && head < MaxSize
  reads a
{
  (Content == if head + contentSize <= MaxSize then a[head..head+contentSize]
              else a[head..] + a[..head+contentSize-MaxSize])
}

class {:autocontracts} Queue {

  ghost var Content: seq<int>;
  ghost var MaxSize: nat

  var a: array<int>
  var head: nat
  var contentSize: nat

  ghost predicate Valid() {
    (a.Length == MaxSize) &&
    (MaxSize == 0 ==> contentSize == head == 0 && Content == []) &&
    (MaxSize != 0 ==> contentSize <= MaxSize && head < MaxSize) &&
    (Content == if head + contentSize <= MaxSize then a[head..head+contentSize]
              else a[head..] + a[..head+contentSize-MaxSize])
    }

    constructor(initialSize: nat)
      ensures Content == []
      ensures MaxSize == initialSize
      ensures head == 0
    {
    a := new int[initialSize];
    head, contentSize := 0, 0;
    Content, MaxSize := [], initialSize;
    }

  method enqueue(e: int)
    ensures Content == old(Content) + [e]
    ensures MaxSize >= old(MaxSize)
    {
    if a.Length == contentSize {
                           // duplica o tamanho da array
      var more := a.Length + 1;
      var d := new int[a.Length + more];
      forall i | 0 <= i < a.Length {
        d[if i < head then i else i + more] := a[i];
    }
      MaxSize, a, head := MaxSize + more, d, if contentSize == 0 then 0 else head + more;
    }
    var nextEmpty := if head + contentSize < a.Length
    then head + contentSize
    else head + contentSize - a.Length;
    a[nextEmpty] := e;
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
    head, contentSize := if head + 1 == a.Length then 0 else head + 1, contentSize - 1;
    Content := Content[1..];
    }

  method contains(el: int) returns (r: bool)
    requires |Content| > 0
    ensures Content == old(Content)
    ensures r <==> el in Content
    {
    var headCopy := head;
    var ContentCopy := Content;
    var contentSizeCopy := contentSize;
    r := false;

    var count := 0;
    while count < contentSize
      invariant 0 <= headCopy < a.Length
      invariant contentSizeCopy == contentSize - count
      invariant ContentIsValid(ContentCopy, a, headCopy, contentSizeCopy, MaxSize)
      invariant Content[count..] == ContentCopy
      invariant forall j : nat :: 0 <= j < count ==> Content[j] != el
    {
      var e := a[headCopy];
      assert e == ContentCopy[0];
      assert e in Content;
      if (e == el) {
        r:= true;
        return;
    }
      count := count + 1;
      headCopy, contentSizeCopy := if headCopy + 1 == a.Length then 0 else headCopy + 1, contentSizeCopy - 1;
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
    requires DifferentQueues(this, queue)

    ensures queue.a == old(queue.a)
    ensures queue.Content == old(queue.Content)
    ensures Content == old(Content)
    ensures newQueue.Content == Content + queue.Content
  {
    newQueue := new Queue(contentSize + queue.contentSize + 1);
    assert newQueue.MaxSize == contentSize + queue.contentSize + 1;
    assert newQueue.Valid();

    var count := 0;
    var i := head;

    while count < contentSize
      invariant 0 <= i < a.Length
      invariant 0 <= count < newQueue.a.Length
      invariant 0 <= count <= contentSize
      invariant contentSize == old(contentSize)
      invariant Content == old(Content)
      invariant a == old(a)
      invariant Valid()
      invariant Repr == old(Repr)

      invariant queue.contentSize == old(queue.contentSize)
      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant queue.Valid()

      invariant fresh(newQueue.a)
      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count
      invariant newQueue.contentSize == |newQueue.Content|
      invariant newQueue.head == 0
      invariant newQueue.Valid()
      invariant newQueue.a.Length == contentSize + queue.contentSize + 1
    {
      var value := a[i];

      newQueue.a[count] := value;
      newQueue.Content := newQueue.Content + [value];
      newQueue.contentSize := newQueue.contentSize + 1;

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
      invariant contentSize == old(contentSize)
      invariant Content == old(Content)
      invariant a == old(a)
      invariant Valid()
      invariant Repr == old(Repr)

      invariant queue.contentSize == old(queue.contentSize)
      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant queue.Valid()

      invariant fresh(newQueue.a)
      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count + contentSize
      invariant newQueue.contentSize == |newQueue.Content|
      invariant newQueue.head == 0
      invariant newQueue.Valid()
      invariant newQueue.a.Length == contentSize + queue.contentSize + 1
    {
      var value := queue.a[i];
      newQueue.a[index] := value;
      newQueue.Content := newQueue.Content + [value];
      newQueue.contentSize := newQueue.contentSize + 1;

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
  // add 2 items
  var queue := new Queue(3);
  assert queue.size() == 0;

  queue.enqueue(1);
  queue.enqueue(2);
  queue.enqueue(3);
  queue.enqueue(4);
  queue.enqueue(5);
  Print(queue);
  assert queue.Content == [1, 2, 3, 4, 5];

  // size check
  assert queue.size() == 5;
  assert !queue.isEmpty();

  // contains
  var result := queue.contains(2);
  assert result;
  result := queue.contains(10);
  assert !result;

  // dequeue
  var value := queue.dequeue();
  assert value == 1;
  assert queue.Content == [2, 3, 4, 5];
  // another size check after dequeue
  assert queue.size() == 4;

  // is empty
  var queue2 := new Queue(3);
  assert queue2.isEmpty();
  queue2.enqueue(6);
  var v := queue2.dequeue();
  assert queue2.isEmpty();
  queue2.enqueue(6);
  queue2.enqueue(7);

  // concat
  var newQueue := queue.concat(queue2);
  assert newQueue.Content == [2, 3, 4, 5, 6, 7];
  Print(newQueue);
  // assert newQueue.Content == [2, 3, 4, 5];
}