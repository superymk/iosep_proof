function method MapSubmap<T, U> (m:map<T, U>, keys:set<T>) : map<T, U>
    requires keys <= MapGetKeys<T, U>(m)
    ensures MapGetKeys<T, U>(MapSubmap<T, U>(m, keys)) == keys
{
    map k | k in keys :: m[k]
}

function method MapConcat<T(!new), U>(m1:map<T, U>, m2:map<T, U>) : map<T, U>
	requires forall k1, k2 :: k1 in m1 && k2 in m2 ==> k1 != k2

    ensures forall k :: k in MapConcat(m1, m2) <==> k in m1 || k in m2
	ensures forall k :: k in MapConcat(m1, m2) 
				==> (k in m1 ==> MapConcat(m1, m2)[k] == m1[k]) &&
					(k in m2 ==> MapConcat(m1, m2)[k] == m2[k])
{
	map i | i in (MapGetKeys(m1) + MapGetKeys(m2)) :: if i in m1 then m1[i] else m2[i]
}

function method MapRemoveKey<T, U> (m:map<T, U>, key:T) :map<T, U>
    requires key in m
    ensures MapGetKeys<T, U>(MapRemoveKey<T, U>(m, key)) == MapGetKeys<T, U>(m) - {key}
    ensures |MapGetKeys<T, U>(m)| - |MapGetKeys<T, U>(MapRemoveKey<T, U>(m, key))| == 1
    ensures MapGetKeys<T, U>(MapRemoveKey<T, U>(m, key)) < MapGetKeys<T, U>(m)
    ensures key !in MapRemoveKey<T, U>(m, key)
    ensures forall k :: (k in MapRemoveKey<T, U>(m, key) ==> k in m)
    ensures forall k :: k in MapRemoveKey<T, U>(m, key) ==> (MapRemoveKey<T, U>(m, key)[k] == m[k])
{
    map i | i in m && i != key :: m[i]
}

function method MapRemoveKeys<T(!new), U> (m:map<T, U>, keys:set<T>) : map<T, U>
    ensures forall key :: key in m && key !in keys
                <==> key in MapRemoveKeys<T, U>(m, keys)
    ensures forall key :: key in MapRemoveKeys<T, U>(m, keys)
                ==> MapRemoveKeys<T, U>(m, keys)[key] == m[key]
{
    map k | k in m && k !in keys :: m[k]
}

// Get the domain of a map into a set.
function method MapGetKeys<T(!new), U> (m:map<T, U>) : set<T>
    ensures forall key :: key in m <==> key in MapGetKeys<T, U>(m)
{
    set p|p in m::p
}

function method MapSubstract<T(!new), U> (m1:map<T, U>, m2:map<T, U>) : map<T, U>
    ensures forall key :: key in m1 && key !in m2 
                <==> key in MapSubstract<T, U>(m1, m2)
    ensures forall key :: key in MapSubstract<T, U>(m1, m2)
                ==> MapSubstract<T, U>(m1, m2)[key] == m1[key]
{
    map k | k in m1 && k !in m2 :: m1[k]
}

// Create Map, such as the keys are provided in <s>, and the value is provided 
// in <value>
method MapCreateFromSet<T, U>(m:map<T, U>, s:set<T>, value:U) returns (m':map<T, U>)
    requires (forall k :: k in m ==> m[k] == value)
    ensures (forall e:: e in m' <==> e in m || e in s)
    ensures (forall k :: k in m' ==> m'[k] == value)
    decreases s
{
    if(s == {})
    { m' := m; }
    else
    {
        var e :| e in s;
        var m_step := m[ e := value];
        var s_step := s - {e};

        m' := MapCreateFromSet(m_step, s_step, value);
    }
}

// Convert a set to a sequence
method SetToSeq<T>(s:set<T>) returns (q:seq<T>)
    ensures (forall e :: e in s <==> e in q)
    ensures (forall i, j :: 0 <= i < |q| && 0 <= j < |q|
                ==> (i == j <==> q[i] == q[j]))
    ensures (|s| == |q|)
{
    if(|s| == 0)
    {    q := [];}
    else
    {
        var e:| e in s;
        var s_step := s - {e};

        var q1 := SetToSeq<T>(s_step);
        q := [e] + q1;
    }
}

// Convert a sequence to a set
function method SeqToSet<T(!new)>(q:seq<T>) : set<T>
    ensures forall e :: e in q <==> e in SeqToSet<T>(q)
    ensures (forall i, j :: 0 <= i < |q| && 0 <= j < |q|
                ==> (i == j <==> q[i] == q[j]))
            ==> |q| == |SeqToSet<T>(q)|
{
    if(|q| == 0) then
        {}
    else
        {q[0]} + SeqToSet<T>(q[1..])
}

function method SetConcat<T>(s1:set<T>, s2:set<T>) : set<T>
    ensures s1 <= SetConcat<T>(s1, s2)
    ensures s2 <= SetConcat<T>(s1, s2)
{
    s1 + s2
}

function method SeqConcat<T>(s1:seq<T>, s2:seq<T>) : seq<T>
    ensures |SeqConcat<T>(s1, s2)| == |s1| + |s2|
    ensures SeqConcat<T>(s1, s2)[..|s1|] == s1
    ensures SeqConcat<T>(s1, s2)[|s1|..] == s2
{
    s1 + s2
}

function method SeqAppend<T>(s1:seq<T>, v:T) : seq<T>
    ensures |SeqAppend<T>(s1, v)| == |s1| + 1
    ensures SeqAppend<T>(s1, v)[..|s1|] == s1
    ensures SeqAppend<T>(s1, v)[|s1|] == v
{
    SeqConcat<T>(s1, [v])
}




//******** Utility Lemmas ********//
lemma SubsetIntersectionLemma<T>(a : set<T>, b : set<T>)
    ensures |a * b| <= |a|
{
    assert |a - b| == |a| - |a * b|;
}

lemma SubsetCardinalityLemma<T>(a : set<T>, b : set<T>)
    requires (b <= a)
    ensures (|b| <= |a|)
{
    assert(b == a*b);
    SubsetIntersectionLemma<T>(a,b);
}

lemma ProperSubsetCardinalityLemma<T>(a : set<T>, b : set<T>)
    requires (b < a)
    ensures (|b| < |a|)
{
    assert |a - b| == |a| - |a * b|;
}

lemma Lemma_EmptySetIsSubsetOfAnySet<T>(a : set<T>)
    ensures {} <= a
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SetsWithoutSameElemHaveEmptyIntersection<T>(a : set<T>, b : set<T>)
    requires forall e :: e in a ==> e !in b
    ensures a * b == {}
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SetsHaveEmptyIntersectionHasNoCommonElems<T>(a : set<T>, b : set<T>)
    requires a * b == {}
    ensures forall e1, e2 :: e1 in a && e2 in b ==> e1 != e2
{
    if(exists e :: e in a && e in b)
    {
        var e_temp :| e_temp in a && e_temp in b;

        assert a * b == {e_temp};
        assert a * b != {};
    }
}

lemma Lemma_SetSubstractionLemma<T>(a : set<T>, b : set<T>)
    ensures (a-b) * b == {}
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SetDistributiveProperty<T>(a : set<T>, b : set<T>, c : set<T>)
    ensures a * (b + c) == (a * b) + (a * c)
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_UnionOfSubsetIsSubset<T>(a : set<T>, b : set<T>, c : set<T>)
    requires a <= c && b <= c
    ensures a + b <= c
    ensures SetConcat<T>(a, b) <= c
{
    // Danfy can automatically prove this lemma
}

lemma SetRemoveElemsLemma<T> (s:set<T>, s':set<T>, removed_elems:set<T>)
    requires (forall k :: k in s <==> k in s' || k in removed_elems)
    requires s' !! removed_elems
    requires (|removed_elems| >= 0)
    ensures s == s' + removed_elems
    ensures |s| - |s'| == |removed_elems|
{
    assert(s == s' + removed_elems);
    assert(s' <= s);
}

lemma MapRemoveKeysLemma<T, U> (m:map<T, U>, m':map<T, U>, removed_keys:set<T>)
    requires (forall k :: k in m <==> k in m' || k in removed_keys)
    requires MapGetKeys<T, U>(m') !! removed_keys
    requires (|removed_keys| >= 0)
    ensures MapGetKeys<T, U>(m) == MapGetKeys<T, U>(m') + removed_keys
    ensures |MapGetKeys<T, U>(m)| - |MapGetKeys<T, U>(m')| == |removed_keys|
{
    var m_set := MapGetKeys<T, U>(m);
    var m'_set := MapGetKeys<T, U>(m');

    SetRemoveElemsLemma<T>(m_set, m'_set, removed_keys);
}

// Lemma: m and m' has the same set of keys, iff
// (1) MapGetKeys<T, U>(m) == MapGetKeys<T, U>(m')
lemma Lemma_MapSameKeys<T, U>(m:map<T, U>, m':map<T, U>) 
    ensures (forall k :: (k in m <==> k in m')) 
            <==> MapGetKeys<T, U>(m) == MapGetKeys<T, U>(m')
{
    assert forall k :: k in m <==> k in MapGetKeys<T, U>(m);
    assert forall k :: k in m' <==> k in MapGetKeys<T, U>(m');
}

lemma Lemma_TransitiveSubSequence<T>(a:seq<T>, b:seq<T>, c:seq<T>)
    requires |b| >= |c| && |a| >= |b|
    requires b[..|c|] == c && a[..|b|] == b 
    ensures a[..|c|] == c 
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SequenceHighlightFirstElem<T>(a:seq<T>)
    requires |a| > 0
    ensures a[..] == [a[0]] + a[1..]
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SequenceHighlightLastElem<T>(a:seq<T>)
    requires |a| > 0
    ensures a[..] == a[..|a|-1] + [a[|a|-1]]
    ensures forall e :: e in a
                ==> e == a[|a|-1] || e in a[..|a|-1]
{
    // Danfy can automatically prove this lemma
}

// Lemma: If b == a[..|a| - 1], then a[|a| - 2] == b[|b| - 1]
lemma Lemma_SequenceHighlightLastElemOfSubSeq<T>(a:seq<T>, b:seq<T>)
    requires |a| > 1
    requires b == a[..|a| - 1]
    ensures a[|a| - 2] == b[|b| - 1]
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SeqElemInSeqIfNotLastOneThenInOthers<T>(a:seq<T>, e:T)
    requires exists i :: 0 <= i < |a| && a[i] == e
    requires a[|a|-1] != e
    ensures e in a[..|a|-1]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Sequence_LastElemOfSubSequenceIsFromOriginalSequence<T>(a:seq<T>, b:seq<T>, i:int)
    requires 1 <= i <= |a| 
    requires a[..i] == b

    ensures b[|b|-1] == a[i-1]
{
    // Dafny can automatically prove this lemma
}

// Lemma: If a sequence starts from small_set and end into a super_set (superset 
// includes small_set), then there exists an element in the sequence, the element 
// is in the small_set and the next element is in the super_set
lemma Lemma_AChainOfElemsAcrossFromSmallSetToSuperSet_MustHaveOneElemInSmallSetAsLastElem<T>(s:seq<T>, small_set:set<T>, super_set:set<T>)
    requires super_set >= small_set
    requires forall e :: e in s 
                ==> e in super_set

    requires |s| > 1 &&
                s[0] in small_set &&
                s[|s|-1] in super_set && s[|s|-1] !in small_set

    ensures exists i :: 0 <= i < |s| - 1 &&
                s[i] in small_set &&
                s[i+1] in super_set && s[i+1] !in small_set
    ensures exists i :: 0 <= i < |s| - 1 &&
                (forall e :: e in s[..i+1] ==> e in small_set) &&
                s[i+1] !in small_set
    
    decreases |s|
{
    assert s[0] in small_set;

    if(s[1] !in small_set)
    {
        var i := 0;
        assert 0 <= i < |s| - 1;
        assert (forall e :: e in s[..i+1] ==> e in small_set);
        assert s[i+1] !in small_set;
    }
    else
    {
        var next_s := s[1..];
        Lemma_AChainOfElemsAcrossFromSmallSetToSuperSet_MustHaveOneElemInSmallSetAsLastElem(next_s, small_set, super_set);
        var i :| 0 <= i < |next_s| - 1 &&
                (forall e :: e in next_s[..i+1] ==> e in small_set) &&
                next_s[i+1] !in small_set;

        assert s[1..] == next_s;

        assert s[0] in small_set;

        var result_i := i + 1;
        assert 0 <= result_i < |s| - 1;
        assert forall e :: e in s[..result_i+1] ==> e in small_set;
        assert s[result_i+1] !in small_set;
    }
}

lemma Lemma_AllElemsIndexedInSeqAreInSeq<T>(s:seq<T>)
    ensures forall i ::  0 <= i < |s|
                ==> s[i] in s
    ensures forall e :: e in s
                ==> (exists i :: 0 <= i < |s| && s[i] == e)
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SetIncludeMoreElemsFormStrictSuperset<T>(a:set<T>, b:set<T>, c:set<T>)
    requires a == b + c
    requires b * c == {}
    requires c != {}
    ensures a > b
{
    // Danfy can automatically prove this lemma
}

lemma Lemma_SetsMinusProperty<T>(a:set<T>, b:set<T>, c:set<T>)
    requires a == b + c
    requires b * c == {}
    ensures b == a - c
    ensures c == a - b
{
    Lemma_SetsHaveEmptyIntersectionHasNoCommonElems(b, c);
}

lemma Lemma_SetsAddProperty<T>(a:set<T>, b:set<T>, c:set<T>)
    requires b <= a
    requires c == a - b
    requires b * c == {}
    ensures a == b + c
{
    // Danfy can automatically prove this lemma
}