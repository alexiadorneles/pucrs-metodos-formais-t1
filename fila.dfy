/*
    fila de tamanho ilimitado com arrays circulares
    representação ghost: coleção de elementos da fila e qualquer outra informação necessária
    predicate: invariante da representação abstrata associada à coleção do tipo fila

    Operações
        - OK construtor inicia fila fazia
        - OK adicionar novo elemento na fila -> enfileira()
        - OK remover um elemento da fila e retornar seu valor caso a fila contenha elementos  -> desenfileira()
        - OK verificar se um elemento pertence a fila  -> contem()
        - OK retornar numero de elementos da fila -> tamanho()
        - EU verificar se a fila é vazia ou não -> vazia()
        - concatenar duas filas retornando uma nova fila sem alterar nenhuma das outras -> concat()

    criar método main testando a implementação 
*/

class {:autocontracts}  Fila
    {
  var a: array<nat>;
  var cauda: nat;
  const max: nat;

  ghost var Conteudo: seq<nat>;
  ghost const TamanhoMaximo: nat;

  // invariante
  ghost predicate Valid()  {
                        max > 0
    && a.Length == max
    && 0 <= cauda <= max
    && Conteudo == a[0..cauda]
    && TamanhoMaximo == max
    }

    constructor (m:nat)
      requires m > 0
      ensures TamanhoMaximo == m
      ensures Conteudo == []
    {
    max := m;
    a := new nat[m];
    cauda := 0;

    Conteudo := [];
    TamanhoMaximo := max;
    }


  // TODO: isso sai pq a fila vai ser ilimitada
  function QuantidadeMaxima():nat
    ensures QuantidadeMaxima() == TamanhoMaximo
    {
                             max
    }

  function tamanho():nat
    ensures tamanho() == |Conteudo|
    {
                    cauda
    }

    method estaVazio() returns (r:bool)
    ensures r <==> |Conteudo| == 0
    {
        return cauda == 0;
    }

  method enfileira(e:nat)
    requires |Conteudo| < TamanhoMaximo
    ensures Conteudo == old(Conteudo) + [e]
    {
    a[cauda] := e;
    cauda := cauda + 1;
    Conteudo := Conteudo + [e];
    }

  method desenfileira() returns (e:nat)
    requires |Conteudo| > 0
    ensures e == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    e := a[0];
    cauda := cauda - 1;
    forall i | 0 <= i < cauda
    {
      a[i] := a[i+1];
    }
    Conteudo := a[0..cauda];
  }

  method contem(e: nat) returns (r:bool)
    ensures r == true ==> exists i :: 0 <= i < cauda && e == a[i]
    ensures r == false ==> forall i :: 0 <= i < cauda ==> e != a[i]
  {
    var i := 0;

    while i < cauda
      invariant 0 <= i <= cauda
      invariant forall j: nat :: j < i ==> a[j] != e
    {
      if (a[i] == e) {
        return true;
      }

      i := i + 1;
    }

    return false;
  }

  //   method vazia() returns (r:bool) {}
  //   method concat() returns (f1: Fila, f2: Fila) returns (r:Fila) {}
}

method Main()
{
  var fila := new Fila(5);

  // enfileira
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  assert fila.Conteudo == [1,2, 3];

  // tamanho
  var q := fila.tamanho();
  assert q == 3;

  // desenfileira
  var e := fila.desenfileira();
  assert e == 1;
  assert fila.Conteudo == [2, 3];
  assert fila.tamanho() == 2;

  // contem
  var r := fila.contem(1);
  assert r == false;
  var r2 := fila.contem(2);
  assert r2 == true;

}