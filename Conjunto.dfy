function toset(s: seq<int>): set<int>
{
    set x | x in s
}

method tosetMethod(arr: array<int>) returns (s: set<int>)
ensures arr == old(arr)
ensures arr.Length == old(arr.Length)
{
    var sequence := arr[..];
    s := set x | x in sequence;
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
    ensures toset(conteudo) == toset(old(conteudo))
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
        var pos := buscaNoArray(e); 
        if pos == -1 
        {
            r := false;
        }
        else
        {
            assert e in conteudo;
            a[pos] := a[tamanho-1];
            conteudo := a[..tamanho-1];
            assert 0 <= pos < tamanho;
            assert conteudo[..pos] == old(conteudo)[..pos];
            if pos < tamanho-1{
                assert 0 <= pos < tamanho-1;
                assert |old(conteudo)| == old(tamanho);
                assert conteudo[..pos] == old(conteudo)[..pos];
                assert conteudo[pos] == old(conteudo)[tamanho-1];
                assert conteudo[pos+1..] == conteudo[pos+1..];
                //assert conteudo == old(conteudo)[..pos] + [old(conteudo)[old(tamanho)-1]] + old(conteudo)[pos+1..];
            }
            else if pos == tamanho-1{
                assert conteudo[..pos] == old(conteudo)[..pos];
                //assert conteudo == old(conteudo)[..pos] + [a[tamanho-1]];
            }
            tamanho := tamanho - 1;
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
    requires set2.Valid()
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) + toset(set2.conteudo)
    ensures forall e :: (e in conteudo) || (e in set2.conteudo) <==> (e in c.conteudo)
    ensures set2.Valid()
    {
        c := new ConjuntoInt();
        var set1 := tosetMethod(a);
        var set2 := tosetMethod(set2.a);
        var conj1 := (set x | x in set1);
        var conj2 := (set x | x in set2);
        var conjResp := conj1 + conj2;
        while conjResp != {}
        decreases |conjResp|
        {
          var i: int :| i in conjResp;
          conjResp := conjResp - {i};
          var r := c.adicionar(i);
          assert conteudo == old(conteudo);
        }
    }

    method intersec(set2: ConjuntoInt) returns (c: ConjuntoInt)
    requires set2.Valid()
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) * toset(set2.conteudo)
    ensures forall e :: (e in conteudo) && (e in set2.conteudo) <==> (e in c.conteudo)
    ensures set2.Valid()
    {
        c := new ConjuntoInt();
        var set1 := tosetMethod(a);
        var set2 := tosetMethod(set2.a);
        var conj1 := (set x | x in set1);
        var conj2 := (set x | x in set2);
        var conjResp := conj1 * conj2;
        while conjResp != {}
        decreases |conjResp|
        {
          var i: int :| i in conjResp;
          conjResp := conjResp - {i};
          var r := c.adicionar(i);
        }
    }

    method minus(set2: ConjuntoInt) returns (c: ConjuntoInt)
    requires set2.Valid()
    ensures conteudo == old(conteudo)
    ensures set2.conteudo == old(set2.conteudo)
    ensures toset(c.conteudo) == toset(conteudo) - toset(set2.conteudo)
    ensures forall e :: (e in conteudo) && (e !in set2.conteudo) <==> (e in c.conteudo)
    ensures set2.Valid()
    {
        c := new ConjuntoInt();
        var set1 := tosetMethod(a);
        var set2 := tosetMethod(set2.a);
        var conj1 := (set x | x in set1);
        var conj2 := (set x | x in set2);
        var conjResp := conj1 - conj2;
        while conjResp != {}
        decreases |conjResp|
        {
          var i: int :| i in conjResp;
          conjResp := conjResp - {i};
          var r := c.adicionar(i);
        }
    }
}

method Main(){
    var conj := new ConjuntoInt();
}