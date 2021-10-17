class {:autocontracts} Conjunto{
    //implementacao
    var arr: array<int>
    //tamanho do conjunto
    var tamanho: nat
    //abstracao
    ghost var Conteudo: set<int>
    ghost var ConteudoSeq: seq<int>

    //wip
    predicate Valid(){
        arr.Length > 0 &&
        0 <= tamanho <=arr.Length &&
        forall i, j :: 0 <= i < tamanho && 0 <= j < tamanho && i != j ==> arr[i] != arr[j] &&
        Conteudo == 

    }

    constructor()

    method Add() returns (b : bool)

    method Remove() returns (b: bool)

    method contains(i: int) returns (b: bool)

    method Size() returns (s: int)

    method isEmpty() returns (b: bool)

    method Union(set2: Conjunto) returns (c: Conjunto)

    method Intersec(set2: Conjunto) returns (c: Conjunto)

    method Minus(sec2: Conjunto) returns (c: Conjunto)
}