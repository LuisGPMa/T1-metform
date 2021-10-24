function toset(s: seq<int>): set<int>
{
    set x | x in s
}

function method tosetMethod(arr: array<int>): set<int>
reads arr
{
    var s := arr[..];
    set x | x in s
}

class {:autocontracts} ConjuntoInt {
    //Implementação
    var a: array<int>;
    var tamanho: nat;
    //Abstração
    ghost var conteudo: seq<int>;

    //invariante de classe
    predicate Valid()
    {
        a.Length > 0
        && 0 <= tamanho <= a.Length
        && |conteudo| == tamanho
        && conteudo == a[..tamanho]
        && (forall i, j :: 0 <= i < j < tamanho ==> a[i] != a[j])
    }

    constructor()
    ensures conteudo == []
    {
        a := new int[5];
        tamanho := 0;
        conteudo := [];
    }

    method pertence(e:int) returns (r:bool)
    ensures r <==> e in toset(conteudo)
    ensures toset(conteudo) == toset(old(conteudo))
    ensures |conteudo| == old(|conteudo|)
    ensures conteudo == old(conteudo)
    {
        var i := 0;
        while i < tamanho
        invariant 0 <= i <= tamanho
        invariant forall j :: 0 <= j < i ==> a[j] != e
        {
            if a[i] == e
            {
                return true;
            }
            i := i + 1;
        }
        return false;
    }

    method adicionar(e:int) returns (r:bool)
    ensures r <==> e !in toset(old(conteudo))
    ensures r ==> toset(conteudo) == toset(old(conteudo)) + {e}
    ensures !r ==> toset(conteudo) == toset(old(conteudo))
    {
        var p := pertence(e);
        if p
        {
            r := false;
        }
        else
        {
            if tamanho == a.Length
            {
                var b := new int[2 * tamanho];
                forall i | 0 <= i < tamanho
                {
                    b[i] := a[i];
                }
                a := b;
            }
            a[tamanho] := e;
            tamanho := tamanho + 1;
            conteudo := conteudo + [e];
            r := true;
        }
    }

    method buscaNoArray(e: int) returns (pos: int)
    ensures conteudo == old(conteudo)
    ensures |conteudo| == |old(conteudo)|
    ensures (e !in toset(conteudo)) <==> pos == -1    
    ensures (e in toset(conteudo)) <==> 0 <= pos < tamanho && conteudo[pos] == e
    ensures -1 <= pos < tamanho
    {
        pos := -1;
        var i:nat := 0;
        
        while i < tamanho
        invariant 0 <= i <= tamanho
        invariant forall j :: 0 <= j < i ==> a[j] != e
        {
            if (a[i] == e) {
                return i;
            }
            i := i + 1;
        }
    }

    method remover(e:int) returns (r:bool)
    ensures r <==> e in toset(old(conteudo))
    ensures r  ==> toset(conteudo) == toset(old(conteudo)) - {e} && |conteudo| == |old(conteudo)| - 1
    ensures !r ==> toset(conteudo) == toset(old(conteudo)) && |conteudo| == |old(conteudo)|
    {
        var p := pertence(e);
        if !p
        {
            r := false;
        }
        else
        {
            assert e in conteudo;
            var pos := buscaNoArray(e);
            assert 0 <= pos < tamanho;
            assert |conteudo| == tamanho;
            tamanho := tamanho-1;
            a[pos] := a[tamanho];
            conteudo := a[..tamanho];
            assert pos < old(|conteudo|);
            assert conteudo[..pos] == old(conteudo)[..pos];
            assert conteudo[pos] == old(conteudo)[|old(conteudo)|-1];
            if pos < old(tamanho)-1{
                assert 0 <= pos < |old(conteudo)|;
                assert |old(conteudo)| == old(tamanho);
                assert conteudo[..pos] == old(conteudo)[..pos];
                //assert conteudo == old(conteudo)[..pos] + [old(conteudo)[old(tamanho)-1]] + old(conteudo)[pos+1..];
            }
            else if pos == old(tamanho)-1{
                assert pos == |old(conteudo)|-1;
                //assert conteudo == old(conteudo)[..pos] + [old(conteudo)[old(tamanho)-1]];
            }
            r := true;
        }
    }

    method getSize() returns (s: int)
    ensures s == |conteudo|
    ensures conteudo == old(conteudo)
    {
        return tamanho;
    }

    method isEmpty() returns (b: bool)
    ensures b <==> (|conteudo| == 0)
    ensures conteudo == old(conteudo)
    {
        return (tamanho==0);
    }

    method union(set2: ConjuntoInt) returns (c: ConjuntoInt)
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) + toset(set2.conteudo)
    ensures forall e :: (e in conteudo) || (e in set2.conteudo) <==> (e in c.conteudo)
    //{
    //    c := new ConjuntoInt();
    //    var conj1 := (set x | x in tosetMethod(a));
    //    var conj2 := (set x | x in tosetMethod(set2.a));
    //    var conjResp := conj1 + conj2;
    //    while conjResp != {}
    //    decreases |conjResp|
    //    {
    //      var i: int :| i in conjResp;
    //      conjResp := conjResp - {i};
    //      c.adicionar(i);
    //    }
    //}

    method intersec(set2: ConjuntoInt) returns (c: ConjuntoInt)
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) * toset(set2.conteudo)
    ensures forall e :: (e in conteudo) && (e in set2.conteudo) <==> (e in c.conteudo)
    //{
    //    c := new ConjuntoInt();
    //    var conj1 := (set x | x in tosetMethod(a));
    //    var conj2 := (set x | x in tosetMethod(set2.a));
    //    var conjResp := conj1 * conj2;
    //    while conjResp != {}
    //    decreases |conjResp|
    //    {
    //      var i: int :| i in conjResp;
    //      conjResp := conjResp - {i};
    //      c.adicionar(i);
    //    }
    //}

    method minus(set2: ConjuntoInt) returns (c: ConjuntoInt)
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) - toset(set2.conteudo)
    ensures forall e :: (e in conteudo) && (e !in set2.conteudo) <==> (e in c.conteudo)
    //{
    //    c := new ConjuntoInt();
    //    var conj1 := (set x | x in tosetMethod(a));
    //    var conj2 := (set x | x in tosetMethod(set2.a));
    //    var conjResp := conj1 - conj2;
    //    while conjResp != {}
    //    decreases |conjResp|
    //    {
    //      var i: int :| i in conjResp;
    //      conjResp := conjResp - {i};
    //      c.adicionar(i);
    //    }
    //}
}

method Main(){
    var conj := new ConjuntoInt();
}