class {:autocontracts} Fila {

  var start: nat;
  var end: nat;
  var size: nat;
  var a: array<int>;

    constructor()
      ensures 0 == start
      ensures 0 ==end
      ensures a.Length == 5
      ensures size == 0
    {
    start := 0;
    end := 0;
    a := new int[5];
    size := 0;
    }

  ghost predicate Valid() {
                        0 <= start < a.Length
    && 0 <= end < a.Length
    && a.Length >= 5
    && size <= a.Length
    }

  method enfileira(e: nat)
    ensures size == old(size) + 1
    ensures fresh(this)
    // ensures a[old(end)] == e
  {

    if (size == a.Length) {
      var newArr := new int[a.Length * 2];
      var iterations := 0;
      var i := start;

      while iterations < a.Length
        invariant 0 <= 0 <= a.Length
        invariant newArr.Length > a.Length
        invariant 0 <= i < a.Length
        invariant size == old(size)
        invariant fresh(newArr)
      {
        newArr[iterations] := a[i];
        iterations := iterations + 1;
        i := (i + 1) % a.Length;
      }

      end := a.Length;
      start := 0;
      a := newArr;
    }

    a[end] := e;
    end := (end + 1) % a.Length;
    size := size + 1;
  }

}