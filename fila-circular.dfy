ghost predicate ConteudoValido(fila: Fila)
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  (fila.cauda >= fila.inicio ==> fila.Conteudo == fila.a[fila.inicio..fila.cauda])
  && (fila.cauda < fila.inicio ==> fila.Conteudo ==  fila.a[fila.inicio..] + fila.a[0..fila.cauda])
}

ghost function ConteudoFilaCircular(fila: Fila): seq<int>
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  if fila.cauda >= fila.inicio then fila.a[fila.inicio..fila.cauda]
  else fila.a[fila.inicio..] + fila.a[0..fila.cauda]
}


// OK [1, 2, ] -- inicio 0, cauda 3 --> size 2
// OK [1, 2, 3, ] -- inicio 0, cauda 4 --> size 3
// OK [ , 2, ] -- inicio 1, cauda 3 --> size 1
// OK [ , , 2, 3] -- inicio 2, cauda 0 --> size 2
// OK [1, , 2, 3] -- inicio 2, cauda 1 --> size 3
// OK [ , , ] -- inicio 0, cauda 0 --> size 0
ghost predicate TamanhoValido(fila: Fila)
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  if fila.cauda > fila.inicio then fila.size == ((fila.cauda - 1) - fila.inicio)
  else if fila.cauda == fila.inicio then fila.size == 0
  else fila.size == (fila.a.Length - fila.inicio + fila.cauda)
}

function TamanhoFilaCircular(fila: Fila): nat
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  if fila.cauda > fila.inicio then (fila.cauda - 1) - fila.inicio
  else if fila.cauda == fila.inicio then 0
  else fila.a.Length - fila.inicio + fila.cauda
}

class Node {
  var elem: int;
  constructor (data: int)
  {
    elem := data;
  }
}

class {:autocontracts}  Fila
    {
  var a: array<int>;
  var cauda: nat;
  var inicio: nat;
  var size: nat;

  const defaultSize: nat;

  ghost var Conteudo: seq<int>;
  ghost var Primeiro: Node?;
  ghost var Ultimo: Node?;

  ghost predicate Valid()  {
                        defaultSize > 0
    && 0 <= inicio < a.Length
       // && (Primeiro != null ==> Primeiro.elem == a[inicio])
    && a.Length >= defaultSize
    && 0 <= cauda < a.Length
    && (cauda >= inicio ==> Conteudo == a[inicio..cauda])
    && (cauda < inicio ==> Conteudo ==  a[inicio..] + a[0..cauda])
    && TamanhoValido(this)
    // && size == |Conteudo|
    // && ConteudoValido(this)
    }

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
    Primeiro := null;
    Ultimo := null;
    }

  method enfileira(e:int)
    // ensures Conteudo == old(Conteudo) + [e]
  {

    // if (size == a.Length) {
    //   var novoArray := new int[a.Length + defaultSize];
    //   var i := 0;
    //   var j := inicio;

    //   while i < a.Length
    //     invariant 0 <= i <= a.Length
    //     // invariant cauda < a.Length
    //     invariant Conteudo == old(Conteudo)
    // // invariant |Conteudo| == size
    // // invariant inicio < a.Length
    //     invariant inicio == old(inicio)
    // // invariant novoArray.Length > a.Length
    // // invariant cauda < novoArray.Length
    // {
    //                             // TODO: descobrir pq n funciona aqui
    //                             // novoArray[i] := a[i];
    //     j:=(j+1) % a.Length;
    //     i := i + 1;
    // }

    //   a := novoArray;
    //   inicio := 0;
    //   cauda := i;
    // }

    a[cauda] := e;
    cauda := (cauda + 1) % a.Length;
    // Conteudo := Conteudo + [e];

    if cauda >= inicio
    {
      Conteudo := a[inicio..cauda];
      size := TamanhoFilaCircular(this);
    } else {
      Conteudo := a[inicio..] + a[0..cauda];
      size := TamanhoFilaCircular(this);
    }

    size := size + 1;
  }

  // method desenfileira() returns (e:int)
  //   requires |Conteudo| > 0
  //   requires Conteudo[0] == a[inicio]
  //   ensures e == old(Conteudo)[0]
  //   ensures Conteudo == old(Conteudo)[1..]
  // {
  //   e := a[inicio];
  //   inicio :=  (inicio + 1) % a.Length;
  //   Conteudo := Conteudo[1..];
  //   size := size - 1;
  // }
}


method Print(fila: Fila) {
  print("\n\n");
  var i := 0;
  while i < fila.a.Length{
    print(fila.a[i]);
    print("  ");
    i := i + 1;
  }
}

method Main()
{
  var fila := new Fila();

  // enfileira deve alocar mais espaço
  fila.enfileira(1);
  fila.enfileira(2);
  fila.enfileira(3);
  // assert fila.Conteudo == [1, 2, 3];

  // desenfileira
  // assert fila.Conteudo[0] == 1;
  // assert fila.inicio == 0;
  // assert fila.Conteudo[0] == fila.a[fila.inicio];
  // var e := fila.desenfileira();
  // assert e == 1;
  // assert fila.Conteudo == [2, 3, 4];
}