
// [] -- cauda = 0, inicio = 0
// [x, ] -- cauda = 1, inicio = 0

// [x, x, x, ] -- cauda = 3, inicio = 0
// desenfileira
// [ , x, x, ] -- cauda = 3, inicio = 1
// desenfileira
// [ , , x, ] -- cauda = 3, inicio = 2
// enfileira
// [ , , x, x] -- cauda = 0, inicio = 2
// ---
// [ , , x, ] -- cauda = 3, inicio = 2
// proxima cauda tem que ser 0
// a.Length = 4
// 

ghost predicate ConteudoValido(fila: Fila)
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  fila.Conteudo == ConteudoFila(fila)
}

ghost function ConteudoFila(fila: Fila): seq<int>
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  if (fila.cauda >= fila.inicio) then fila.a[fila.inicio..fila.cauda]
  else fila.a[fila.inicio..] + fila.a[0..fila.cauda]
}

class {:autocontracts}  Fila
    {
  var a: array<int>;
  var cauda: nat;
  var inicio: nat;
  var size: nat;

  const defaultSize: nat;

  ghost var Conteudo: seq<int>;

  // invariante
  ghost predicate Valid()  {
                        defaultSize > 0
    && a.Length >= defaultSize
    && 0 <= cauda < a.Length
    && 0 <= inicio < a.Length
       // && ConteudoValido(this)
    && size == |Conteudo|
    }

    // inicia fila com 3 elementos
    constructor ()
      ensures Conteudo == []
      ensures defaultSize == 3
      ensures a.Length == 3
      ensures inicio == 0
      ensures size == 0
      ensures fresh(a)
    {
    defaultSize := 3;
    a := new int[3];
    cauda := 0;
    inicio := 0;
    Conteudo := [];
    size := 0;
    }

  function tamanho():nat
    ensures tamanho() == |Conteudo|
    {
                    size
    }

  function estaVazia(): bool
    ensures estaVazia() <==> |Conteudo| == 0
    {
                      size == 0
    }

  method enfileira(e:int)
    // requires ConteudoValido(this)
    // ensures inicio == old (inicio)
    // ensures Conteudo == old(Conteudo) + [e]
    {

    if (size == a.Length) {
      var novoArray := new int[a.Length + defaultSize];
      var i := 0;

      while i < a.Length
        invariant 0 <= i <= a.Length
        invariant novoArray.Length > a.Length
        invariant cauda < novoArray.Length
        invariant Conteudo == old(Conteudo)
        invariant |Conteudo| == size
        invariant size == old(size)
    {
        novoArray[i] := a[i];
        inicio:=(inicio+1) % a.Length;
        i := i + 1;
    }
      inicio := 0;
      a := novoArray;
    }

    a[cauda] := e;
    cauda := (cauda + 1) % a.Length;
    // assert ConteudoFila(this) == Conteudo + [e];
    Conteudo := Conteudo + [e];
    // Conteudo := ConteudoFila(this);
    size := size + 1;
    }

  method desenfileira() returns (e:int)
    requires |Conteudo| > 0
    requires a[inicio] == Conteudo[0]
    ensures e == old(Conteudo)[0]
    ensures Conteudo == old(Conteudo)[1..]
  {
    e := a[inicio];
    a[inicio] := 0;
    Conteudo := Conteudo[1..];
    inicio := (inicio+1) % a.Length;
    size := size - 1;
  }

  method contem(e: int) returns (r:bool)
    ensures r <==> exists i :: 0 <= i < cauda && e == a[i]
  {
    var i := 0;
    r:= false;

    while i < cauda
      invariant 0 <= i <= cauda
      invariant forall j: nat :: j < i ==> a[j] != e
    {
      if (a[i] == e) {
        r:= true;
        return;
      }

      i := i + 1;
    }

    return r;
  }

  // method concat(f2: Fila) returns (r: Fila)
  //   requires Valid()
  //   requires f2.Valid()
  //   ensures r.Conteudo == Conteudo + f2.Conteudo
  // {
  //   r := new Fila();

  //   var i:= 0;

  //   while i < cauda
  //     invariant 0 <= i <= cauda
  //     invariant 0 <= i <= r.cauda
  //     invariant r.cauda <= r.a.Length
  //     invariant fresh(r.Repr)
  //     invariant r.Valid()
  //     invariant r.Conteudo == Conteudo[0..i]
  //   {
  //     var valor := a[i];
  //     r.enfileira(valor);
  //     i := i + 1;
  //   }

  //   var j := 0;
  //   while j < f2.cauda
  //     invariant 0 <= j <= f2.cauda
  //     invariant 0 <= j <= r.cauda
  //     invariant r.cauda <= r.a.Length
  //     invariant fresh(r.Repr)
  //     invariant r.Valid()
  //     invariant r.Conteudo == Conteudo + f2.Conteudo[0..j]
  //   {
  //     var valor := f2.a[j];
  //     r.enfileira(valor);
  //     j := j + 1;
  //   }
  // }
}

method Main()
{
  var fila := new Fila();

  // enfileira deve alocar mais espaço
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  fila.enfileira(4);
  fila.enfileira(5);
  fila.enfileira(6);
  fila.enfileira(7);
  fila.enfileira(8);

  var i := 0;
  while i < fila.a.Length{
    print(fila.a[i]);
    print(" ");
    i := i + 1;
  }

  // // tamanho
  // var q := fila.tamanho();
  // assert q == 4;

  // // desenfileira
  // var e := fila.desenfileira();
  // assert e == 1;
  // assert fila.Conteudo == [2, 3, 4];
  // assert fila.tamanho() == 3;

  // // contem
  // assert fila.Conteudo == [2, 3, 4];
  // var r := fila.contem(1);
  // assert r == false;
  // assert fila.a[0] == 2;
  // var r2 := fila.contem(2);
  // assert r2 == true;

  // // estaVazia
  // var vazia := fila.estaVazia();
  // assert vazia == false;
  // var outraFila := new Fila();
  // vazia := outraFila.estaVazia();
  // assert vazia == true;

  // // concat
  // assert fila.Conteudo == [2, 3, 4];
  // outraFila.enfileira(5);
  // outraFila.enfileira(6);
  // outraFila.enfileira(7);
  // assert outraFila.Conteudo == [5, 6, 7];
  // var concatenada := fila.concat(outraFila);
  // assert concatenada.Conteudo == [2,3,4,5,6,7];
}