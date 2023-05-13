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
              else a[head..] + a[..head+contentSize-MaxSize]) &&
    (|Content| > 0 ==> a[head] == Content[0])
    }

    constructor()
      ensures Content == []
      ensures MaxSize == 5
    {
    a := new int[5];
    head, contentSize := 0, 0;
    Content, MaxSize := [], 5;
    }

  method enqueue(e: int)
    requires |Content| < MaxSize
    ensures Content == old(Content) + [e]
    ensures MaxSize == old(MaxSize)
    ensures head == old(head)
    {
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

  method contains(e: int) returns (r: bool)
    ensures Content == old(Content)
    ensures r <==> e in Content

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
    ensures queue.Content == old(queue.Content)
    ensures Content == old(Content)
    ensures newQueue.Content == Content + queue.Content

}

method Main() {
  // add 2 items
  var queue := new Queue();
  assert queue.size() == 0;

  queue.enqueue(1);
  queue.enqueue(2);
  assert queue.Content == [1, 2];

  // size check
  assert queue.size() == 2;
  assert !queue.isEmpty();

  // contains
  // var includes := queue.contains(2);
  // assert includes;
  // includes := queue.contains(3);
  // assert !includes;

  // dequeue
  var value := queue.dequeue();
  assert value == 1;
  assert queue.Content == [2];
  // another size check after dequeue
  assert queue.size() == 1;

  // is empty
  var el := queue.dequeue();
  assert queue.isEmpty();
}