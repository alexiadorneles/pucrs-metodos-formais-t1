class {:autocontracts} CircularQueue
    {
    var elements: array<int>;
    var front: int;
    var count: int;
    const defaultSize: nat;


    constructor ()
    ensures front == 0
    ensures count == 0
    ensures elements.Length >= defaultSize
    ensures defaultSize == 5
    ensures fresh(elements)
    {
    elements := new int[5];
    front := 0;
    count := 0;
    defaultSize := 5;
    }

    ghost predicate Valid()
    reads this
    {
                        //   0 <= count <= elements.Length &&
     0 <= front < elements.Length
    }

  method Enqueue(element: int)
    ensures count == old(count) + 1
    {
    if count == elements.Length {
      var newElements := new int[2 * elements.Length];
      for i: int := 0 to elements.Length - 1
        invariant elements.Length > 0
        invariant count == old(count)
    {
        var index := (front + i) % elements.Length;
        newElements[i] := elements[index];
    }
      elements := newElements;
      front := 0;
    }

    var rear := (front + count) % elements.Length;
    elements[rear] := element;
    count := count + 1;
    }

  method Dequeue() returns (element: int)
    requires count > 0
  {
    element := elements[front];
    front := (front + 1) % elements.Length;
    count := count - 1;
  }

  function Size(): int
  {
    count
  }

  method Contains(element: int) returns (b: bool)
    requires elements.Length > 0
  {
    var i := front;
    var iterations := 0;
    b := false;

    while iterations < count
      invariant iterations <= count
      invariant 0 <= i < elements.Length
    {
      if elements[i] == element {
        b := true;
        return;
      }

      i := (i + 1) % elements.Length;
      iterations := iterations + 1;
    }
  }

  method Concat(queue: CircularQueue) returns (newQueue: CircularQueue)
    requires queue.Valid()
    requires queue.Size() > 0
    requires Size() > 0
    ensures newQueue.Valid()
    ensures newQueue.Size() == Size() + queue.Size()
  {
    newQueue := new CircularQueue();

    var thisSize := Size();
    var queueSize := queue.Size();

    assert newQueue.Size() == 0;

    // Copia o conteúdo da fila atual para newQueue
    for i: int := 0 to thisSize - 1
      invariant newQueue.count == i
      //   invariant i <= newQueue.elements.Length
      invariant fresh(newQueue.Repr)
      //   invariant Size() == thisSize - i
    {
      var index := (front + i) % elements.Length;
      var element := elements[index];
      newQueue.Enqueue(element);
    }

    // Copia o conteúdo da fila queue para newQueue
    for i: int := 0 to queueSize - 1
      invariant newQueue.Size() == thisSize + i
      invariant queue.Size() == queueSize - i
    {
      var index := (queue.front + i) % queue.elements.Length;
      var element := queue.elements[index];
      newQueue.Enqueue(element);
    }

    return newQueue;
  }


}
