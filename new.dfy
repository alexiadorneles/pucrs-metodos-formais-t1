class {:autocontracts} FilaCircular {
  var fim: nat;
  var inicio: nat;
  var a: array<nat>;
  var tamanho: nat;

  ghost var Conteudo: seq<nat>;

  ghost predicate Valid() {
    (0 <= inicio < a.Length) &&
    (0 <= fim < a.Length) &&
    (a.Length > 0) &&
    ((fim >= inicio ==> Conteudo == a[inicio..fim]) ||
    (fim < inicio ==> Conteudo ==  a[inicio..] + a[0..fim])) &&
    (tamanho == |Conteudo|)
    }

    constructor()
      ensures Conteudo == []
      ensures inicio == 0
      ensures fim == 0
      ensures a.Length == 5
      ensures a.Length == 5
    {
    inicio := 0;
    fim := 0;
    a:= new nat[5];
    Conteudo := [];
    tamanho := 0;
    }

  method enqueue(e: nat)
    ensures Conteudo == old(Conteudo) + [e]
  {
    // if (tamanho == a.Length) {
    //   var novoA := new nat[2 * a.Length];

    //   var i := 0;

    //   while i < a.Length
    //     invariant novoA.Length > a.Length
    //     invariant novoA.Length > inicio
    //     invariant fim == old(fim)
    //     invariant Conteudo == old(Conteudo)
    //     invariant fresh(novoA)
    //   {
    //     var item := a[i];
    //     novoA[i] := item;
    //     i := i + 1;
    //   }

    //   a := novoA;
    // }

    a[fim] := e;
    fim := (fim + 1) % a.Length;
    Conteudo := Conteudo + [e];
    tamanho := tamanho + 1;
  }

  method contains(element: nat) returns (b: bool)
    requires |Conteudo| > 0
    requires fim != inicio
    // ensures b <==> exists i :: 0 <= i < |Conteudo| && element == Conteudo[i]
  {
    var i := inicio;
    var iterations := 0;
    b := false;

    // [1, , 2, 3] -- inicio 2, cauda 1 --> size 3
    // [2, 3, 1]
    // it = 0, i = 2
    // it = 1, i = 3
    // it = 2, i = 0
    // retorna


    // [, , 1, 2, 3] -- inicio 2, fim 3 --> size 3
    // [1, 2, 3]
    // it = 0, i = 2
    // it = 1, i = 3
    // it = 2, i = 4
    // retorna

    while iterations < tamanho
      invariant tamanho == |Conteudo|
      invariant 0 <= iterations <= tamanho
      invariant fim == old(fim)
      invariant inicio == old(inicio)
      invariant Conteudo == old(Conteudo)
      invariant fim > inicio && iterations > 0 ==> (inicio <= i <= fim < a.Length) && ((i - iterations) == (i - 1))
      invariant fim >= inicio ==> inicio <= i <= fim

      invariant ((fim >= inicio ==> Conteudo == a[inicio..fim]) ||
                (fim < inicio ==> Conteudo ==  a[inicio..] + a[0..fim]))

      // invariant forall j: nat :: j < iterations ==> Conteudo[j] != element
    {
      if a[i] == element {
        // assert Conteudo[iterations] == element;
        b := true;
        return;
      }
      var i := (i + 1) % a.Length;
      iterations := iterations + 1;
    }
  }
}

method Print(fila: FilaCircular) {
  print("\n\n");
  var i := 0;
  while i < fila.a.Length{
    print(fila.a[i]);
    print("  ");
    i := i + 1;
  }
}


method Main() {
  var fila := new FilaCircular();
  fila.enqueue(1);
  fila.enqueue(2);
  fila.enqueue(3);
  fila.enqueue(4);
  fila.enqueue(5);
  assert fila.Conteudo == [1, 2, 3, 4, 5];

  assert fila.Conteudo[0] == 1;
  assert fila.a[0] == 1;
  var contem := fila.contains(1);
  assert contem == true;

  Print(fila);
}