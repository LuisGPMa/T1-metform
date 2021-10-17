class {:autocontracts} Conjunto{
    //implementacao
    var arr: array<int>;
    //tamanho do conjunto, pode ser usado como o atributo cauda da Fila
    var tamanho: nat;
    //abstracao
    ghost var Conteudo: set<int> ;

    predicate Valid(){
        arr.Length > 0 &&
        tamanho <= arr.Length &&
        (forall i, j :: 0 <= i < tamanho && 0 <= j < tamanho && i != j ==> arr[i] != arr[j]) &&
        (forall num: int :: num in Conteudo <==> exists i: nat :: i < tamanho && arr[i] == num)

    }
    constructor()
    ensures Conteudo == {};
    {
        arr := new int[20];
        tamanho := 0;
        Conteudo := {};
    }

    //to do: abaixo
    method add(num: int) returns (b : bool)
    ensures Conteudo == (old(Conteudo) + {num});
    {

    }

    method remove() returns (b: bool)

    method contains(i: int) returns (b: bool)

    method getSize() returns (s: int)

    method isEmpty() returns (b: bool)

    method union(set2: Conjunto) returns (c: Conjunto)

    method intersec(set2: Conjunto) returns (c: Conjunto)

    method minus(sec2: Conjunto) returns (c: Conjunto)
}