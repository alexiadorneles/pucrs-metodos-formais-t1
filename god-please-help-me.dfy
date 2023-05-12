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

  ghost predicate Valid()

  constructor() ensures Content == []

  method enqueue(e: int) ensures Content == old(Content) + [e]

  method dequeue() returns (e: int) requires |Content| > 0 ensures Content == old(Content)[1..] ensures old(Content)[0] == e

  method contains(e: int) returns (r: bool) ensures Content == old(Content) ensures r <==> e in Content

  method size() returns (r: nat) ensures Content == old(Content) ensures r == |Content|

  method isEmpty() returns (r: bool) ensures Content == old(Content) ensures r == (|Content| == 0)

  method concat(queue: Queue) returns (newQueue: Queue) requires queue.Valid() requires |queue.Content| > 0 requires |Content| > 0 ensures queue.Content == old(queue.Content) ensures Content == old(Content) ensures newQueue.Content == Content + queue.Content


}