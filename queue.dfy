// Alunos: Aléxia Dorneles, Bruno Chanan, Lucas Susin, Clada D'ávila
ghost predicate ContentIsValid(Content: seq<int>, a: array<int>, head: nat)
  requires a.Length == a.Length
  requires a.Length == 0 ==> |Content| == head == 0 && Content == []
  requires a.Length != 0 ==> |Content| <= a.Length && head < a.Length
  reads a
{
  (Content == if head + |Content| <= a.Length then a[head..head+|Content|]
              else a[head..] + a[..head+|Content|-a.Length])
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
    (contentSize == |Content|) &&
    (contentSize <= a.Length) &&
    (ContentIsValid(Content, a, head))
    }

    constructor()
      ensures Content == []
    // inicia em 3 para facilitar os testes
      ensures ArraySize == 3
      ensures head == 0
    {
    a := new int[3];
    head, contentSize := 0, 0;
    Content, ArraySize := [], 3;
    }

  method enqueue(e: int)
    ensures Content == old(Content) + [e]
    ensures ArraySize >= old(ArraySize)
    {
    if a.Length == contentSize {
                             // duplica o size do array
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
      invariant ContentIsValid(Content[count..], a, i)

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

  method {:timeLimit 120} concat(queue: Queue) returns (newQueue: Queue)
    requires queue.Valid()
    requires |queue.Content| > 0
    requires |Content| > 0

    ensures queue.Content == old(queue.Content)
    ensures Content == old(Content)
    ensures newQueue.Content == Content + queue.Content
    ensures newQueue.Valid()
  {
    newQueue := new Queue();

    var count := 0;
    var i := head;
    var ContentCopy := Content;

    while count < contentSize
      invariant 0 <= i < a.Length
      invariant 0 <= count <= contentSize

      // this continua o mesmo
      invariant Content == old(Content)
      invariant a == old(a)
      invariant newQueue.a != a
      invariant forall j : nat :: j < a.Length ==> a[j] == old(a[j])
      invariant Valid()
      invariant Repr == old(Repr)

      invariant Content[count..] == ContentCopy
      invariant ContentIsValid(ContentCopy, a, i)
      invariant newQueue.Content == Content[..count]

      // queue continua a mesma
      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant forall k : nat :: k < queue.a.Length ==> queue.a[k] == old(queue.a[k])
      invariant queue.Valid()

      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count
      invariant newQueue.Valid()
    {
      var value := a[i];
      assert value in ContentCopy;
      newQueue.enqueue(value);
      ContentCopy := ContentCopy[1..];
      i := if i + 1 == a.Length then 0 else i + 1;
      count := count + 1;
    }

    ContentCopy := queue.Content;
    count := 0;
    i := queue.head;
    var index := newQueue.contentSize;
    while count < queue.contentSize
      invariant 0 <= i < queue.a.Length
      invariant 0 <= index <= newQueue.a.Length
      invariant 0 <= count <= |queue.Content|
      invariant index - count == contentSize

      // this continua o mesmo
      invariant Content == old(Content)
      invariant a == old(a)
      invariant Valid()
      invariant Repr == old(Repr)

      // queue continua a mesma
      invariant queue.Content == old(queue.Content)
      invariant queue.a == old(queue.a)
      invariant newQueue.a != a
      invariant forall k : nat :: k < queue.a.Length ==> queue.a[k] == old(queue.a[k])
      invariant queue.Valid()

      invariant queue.Content[count..] == ContentCopy
      invariant ContentIsValid(ContentCopy, queue.a, i)
      invariant newQueue.Content == Content + queue.Content[..count]

      invariant fresh(newQueue.Repr)
      invariant newQueue.contentSize == count + contentSize
      invariant newQueue.Valid()
    {
      var value := queue.a[i];
      assert value in ContentCopy;
      newQueue.enqueue(value);
      ContentCopy := ContentCopy[1..];
      i := if i + 1 == queue.a.Length then 0 else i + 1;
      count := count + 1;
      index := index + 1;
    }
  }
}

method Main() {
  // inicia com 3 espaços no array, para teste
  var fila := new Queue();

  // enqueue deve alocar mais espaço
  fila.enqueue(1);
  fila.enqueue(2);
  fila.enqueue(3);
  fila.enqueue(4);
  assert fila.Content == [1, 2, 3, 4];

  // size
  assert fila.size() == 4;

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
  assert !fila.isEmpty();
  var outraFila := new Queue();
  assert outraFila.isEmpty();

  // concat
  assert fila.Content == [2, 3, 4];
  outraFila.enqueue(5);
  outraFila.enqueue(6);
  outraFila.enqueue(7);
  assert outraFila.Content == [5, 6, 7];
  var concatenada := fila.concat(outraFila);
  assert concatenada.Content == [2,3,4,5,6,7];
  assert concatenada.Valid();
}