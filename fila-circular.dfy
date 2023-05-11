ghost predicate ConteudoValido(fila: Fila)
  reads fila, fila.Repr, fila.a
  requires 0 <= fila.cauda <= fila.a.Length
  requires 0 <= fila.inicio <= fila.a.Length
{
  fila.cauda >= fila.inicio ==> fila.Conteudo == fila.a[fila.inicio..fila.cauda]
                                && fila.cauda < fila.inicio ==> fila.Conteudo ==  fila.a[fila.inicio..] + fila.a[0..fila.cauda]
}
class {:autocontracts}  Fila
    {
  var a: array<int>;
  var cauda: nat;
  var inicio: nat;
  var size: nat;

  const defaultSize: nat;

  ghost var Conteudo: seq<int>;

  ghost predicate Valid()  {
                        defaultSize > 0
    && a.Length >= defaultSize
    && 0 <= cauda < a.Length
    && 0 <= inicio < a.Length
    && ConteudoValido(this)
    && size == |Conteudo|
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
    }

  method enfileira(e:int)
    ensures Conteudo == old(Conteudo) + [e]
  {

    print("\nsize ");
    print(size);
    print("\na.Length ");
    print(a.Length);

    if (size == a.Length) {
      var novoArray := new int[a.Length + defaultSize];
      var i := 0;
      var j := inicio;

      while i < a.Length
        invariant 0 <= i <= a.Length
        invariant cauda < a.Length
        invariant Conteudo == old(Conteudo)
        invariant |Conteudo| == size
        invariant inicio < a.Length
        invariant inicio == old(inicio)
        invariant novoArray.Length > a.Length
        invariant cauda < novoArray.Length
      {
        // TODO: descobrir pq n funciona aqui
        // novoArray[i] := a[i];
        j:=(j+1) % a.Length;
        i := i + 1;
      }

      a := novoArray;
      inicio := 0;
    }

    a[cauda] := e;
    cauda := (cauda + 1) % a.Length;
    Conteudo := Conteudo + [e];
    size := size + 1;
  }
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
  Print(fila);
  fila.enfileira(2);
  Print(fila);
  fila.enfileira(3);
  Print(fila);
  fila.enfileira(4);
  Print(fila);
  fila.enfileira(5);
  Print(fila);
  fila.enfileira(6);
  Print(fila);
  fila.enfileira(7);
  Print(fila);
  fila.enfileira(8);
  Print(fila);

  // assert fila.Conteudo == [1, 2, 3, 4, 5, 6, 7, 8];
}