    /*
    fila de tamanho ilimitado com arrays circulares
    representação ghost: coleção de elementos da fila e qualquer outra informação necessária
    predicate: invariante da representação abstrata associada à coleção do tipo fila

    Operações
        - construtor inicia fila fazia
        - adicionar novo elemento na fila -> enfileira()
        - remover um elemento da fila e retornar seu valor caso a fila contenha elementos  -> desenfileira()
        - verificar se um elemento pertence a fila  -> contem()
        - retornar numero de elementos da fila -> tamanho()
        - verificar se a fila é vazia ou não -> estaVazia()
        - concatenar duas filas retornando uma nova fila sem alterar nenhuma das outras -> concat()

    criar método main testando a implementação 
*/

//   ghost var Last: int;
// && Last == a[(tail - 1) % a.Length]
// && (|Content| > 0 ==> Content[0] == a[head])

class {:autocontracts} Queue {

  var a: array<int>;
  var head: nat;
  var tail: nat;
  var qSize: nat;

  ghost var Content: seq<int>;
  ghost var First: int;

  ghost predicate Valid()
    {
                        a.Length >= 3
    && (0 <= tail < a.Length)
    && (0 <= head < a.Length)
    && (tail == head <==> (head == 0 && tail == 0) || |Content| == a.Length)
    // && (|Content| > 0 ==> head != tail)
    && (
    (tail == head ==> (Content == [] || |Content| == a.Length)) &&
    (tail > head ==> (Content == a[head..tail])) &&
    (tail < head ==> (Content == a[head..] + a[0..tail]))
    )
    && qSize == |Content|
    // && (|Content| > 0 ==> First == Content[0])
    // && (|Content| > 0 ==> First == Content[0])
    }

    constructor() ensures Content == [] {
    a := new int[3];
    Content := [];
    head := 0;
    tail := 0;
    First := 0;
    qSize := 0;
    }

  method enqueue(e: int)
    // requires head == 0 ==> ((tail + 1) % a.Length) != 0
    // requires |Content| < a.Length
    ensures a.Length >= old(a.Length)
    ensures Content == old(Content) + [e]
    ensures head == old(head)
    ensures old(|Content|) > 0 ==> Content[0] == old(Content[0])
  {

    // primeiro enqueue
    if (qSize == 0) {
      assert head == 0;
      assert tail == 0;
      a[head] := e;
      Content := [e];
      assert a[head] == Content[0];
      qSize := qSize + 1;
      tail := (tail + 1) % a.Length;
      assert tail != 0;
      return;
    }

    // fila cheia, aloca mais espaço
    if (qSize == a.Length) {
      var newArr := new int[a.Length * 2];
      var iterations := 0;
      var i := head;

      while iterations < a.Length
        invariant 0 <= 0 <= a.Length
        invariant newArr.Length > a.Length
        invariant 0 <= i < a.Length
        invariant qSize == old(qSize)
        invariant Content == old(Content)
        invariant head == old(head)
        invariant fresh(newArr)
      {
        newArr[iterations] := a[i];
        iterations := iterations + 1;
        i := (i + 1) % a.Length;
      }

      tail := a.Length;
      head := 0;
      a := newArr;
      Content := a[head..tail];
    }

    assert |Content| > 0 ==> a[head] == Content[0];
    a[tail] := e;
    tail := (tail + 1) % a.Length;
    Content := Content + [e];
    qSize := qSize + 1;
    // First := Content[0];
  }

  // se fila vazia, head e tail no 0
  // method dequeue() returns (e: int)
  //   requires |Content| > 0
  //   ensures Content == old(Content)[1..]
  //   ensures e == old(First) {
  //   e := a[head];
  //   head := (head + 1) % a.Length;
  //   Content := Content[1..];
  //   if (|Content| > 0) {
  //     First := Content[0];
  //   }
  //   }

  // method contains(e: int) returns (r: bool) ensures Content == old(Content) ensures r <==> e in Content

  // method size() returns (r: nat) ensures Content == old(Content) ensures r == |Content|

  // method isEmpty() returns (r: bool) ensures Content == old(Content) ensures r == (|Content| == 0)

  // method concat(queue: Queue) returns (newQueue: Queue) requires queue.Valid() requires |queue.Content| > 0 requires |Content| > 0 ensures queue.Content == old(queue.Content) ensures Content == old(Content) ensures newQueue.Content == Content + queue.Content

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
  var queue := new Queue();

  // enfileirar
  queue.enqueue(1);
  queue.enqueue(2);
  queue.enqueue(3);
  queue.enqueue(4);
  queue.enqueue(5);
  assert queue.Content == [1,2,3,4,5];
  Print(queue);

  // desenfileirar
  // var value := queue.dequeue();
  // assert queue.Content == [2,3];
  // assert queue.a[queue.head] == 2;
  // assert queue.First == 2;
  // assert value == 1;
}