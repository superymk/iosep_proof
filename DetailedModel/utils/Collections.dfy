include "../../Abstract/utils/Collections.dfy"

lemma Lemma_Equality_Property<T>(a:T, b:T, p:T, q:T)
    requires a == b
    requires a == p
    requires b == q

    ensures p == q
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Equality_Reflexive<T>(a:T, b:T)
    requires a == b

    ensures b == a
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Set_Equal<T>(s1:set<T>, s2:set<T>, e:T)
    requires s1 == s2
    requires e in s1

    ensures e in s2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Map_Equality<T, U>(m1:map<T,U>, m2:map<T,U>)
    requires forall e :: e in m1
                ==> e in m2 &&
                    m1[e] == m2[e]
    requires forall e :: e in m2
                ==> e in m1 &&
                    m1[e] == m2[e]

    ensures m1 == m2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_MapsWithSameKeysValuesAreSameMap<T, U>(m1:map<T, U>, m2:map<T, U>)
    requires MapGetKeys(m1) == MapGetKeys(m2)
    requires forall k :: k in m1
                ==>m1[k] == m2[k]

    ensures m1 == m2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_MapRemoveKeyResultsSubmap<T, U> (m1:map<T, U>, remove_key:T, m2:map<T, U>)
    requires remove_key in m1
    requires m2 == MapRemoveKey(m1, remove_key)

    ensures m2 == MapSubmap(m1, MapGetKeys(m2))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SubmapOfSubmapIsSubmap<T, U> (m1:map<T, U>, m2:map<T, U>, m3:map<T, U>)
    requires MapGetKeys(m2) <= MapGetKeys(m1)
    requires MapGetKeys(m3) <= MapGetKeys(m2)
    requires m2 == MapSubmap(m1, MapGetKeys(m2))
    requires m3 == MapSubmap(m2, MapGetKeys(m3))

    ensures MapGetKeys(m3) <= MapGetKeys(m1)
    ensures m3 == MapSubmap(m1, MapGetKeys(m3))
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetUnionFromTwoSets<T>(s:set<T>, a:T, b:T)
    requires a != b
    requires s == {a} + {b}

    ensures s == {a, b}
    ensures |s| == 2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetUnionFromThreeSets<T>(s:set<T>, a:T, b:T, c:T)
    requires a != b
    requires b != c
    requires a != c
    requires s == {a} + {b} + {c}

    ensures s == {a, b, c}
    ensures |s| == 3
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetEquivilant<T>(s1:set<T>, s2:set<T>)
    requires forall e :: e in s1 ==> e in s2
    requires forall e :: e in s2 ==> e in s1

    ensures s1 == s2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetNoIntesection_Prove<T>(s1:set<T>, s2:set<T>)
    requires !(exists e :: e in s1 && e in s2)
    ensures s1 * s2 == {}
{
}

lemma Lemma_MapGetKeys_EmptyMap<T(!new), U> (m:map<T, U>)
    requires m == map[]
    ensures MapGetKeys(m) == {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_MapGetKeys_OneElemMap<T(!new), U> (k:T, v:U)
    ensures MapGetKeys(map[k := v]) == {k}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OneElemSet_Property<T, U>(m:map<T,U>, e:T)
    requires MapGetKeys(m) == {e}
    ensures forall k :: k in m
                ==> k == e
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OneElemSet_IfElemInMap_ThenOneElemSetIsAlsoInMap<T, U>(m:map<T,U>, e:T)
    requires e in m
    ensures forall e2 :: e2 in {e} ==> e2 in m
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KeyInMapIffKeyInMapGetKeys<T, U>(m:map<T, U>)
    ensures forall k :: k in m <==> k in MapGetKeys(m)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_KeyInMapIffKeyInMapGetKeys_GivenKeys<T, U>(m:map<T,U>, keys:set<T>)
    requires MapGetKeys(m) == keys

    ensures forall k :: k in m <==> k in keys
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_UnionSetIncludesAllElemsInTwoSets<T>(s:set<T>, s1:set<T>, s2:set<T>)
    requires s == s1 + s2

    ensures forall e :: e in s1 ==> e in s
    ensures forall e :: e in s2 ==> e in s
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetRemoveOneElem_Property<T>(s1:set<T>, s2:set<T>, remove_e:T)
    requires remove_e in s1
    requires s2 == s1- {remove_e}

    ensures forall e :: e in s1 && e != remove_e
                ==> e in s2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetInclusion_Prove<T>(s1:set<T>, s2:set<T>)
    requires forall e :: e in s1 ==> e in s2
    ensures s1 <= s2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SetInclusion_Property<T>(s1:set<T>, s2:set<T>)
    requires s1 <= s2
    ensures forall e :: e in s1 ==> e in s2
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_MapGetKeys_PropertyForTwoMaps<T, U, U1, U2>(m:map<T, U>, m1:map<T, U1>, m2:map<T, U2>, k:T)
    requires MapGetKeys(m) == MapGetKeys(m1) + MapGetKeys(m2)
    requires k in m1 || k in m2

    ensures k in m
{
    // Dafny can automatically prove this lemma
}

function method SeqLastElem<T>(s:seq<T>) : T
    requires |s| > 0
{
    s[|s|-1]
}

lemma Lemma_Seq_LastElemIsUnchanged_IfInsertElemAtFirst<T>(a:seq<T>, b:seq<T>, e:T)
    requires a == [e] + b
    requires |b| > 0

    ensures SeqLastElem(a) == SeqLastElem(b)
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_SeqLastElem_Property<T>(a:seq<T>, b:seq<T>)
    requires |a| > 0
    requires |b| > 0
    requires a[|a|-1] == b[|b|-1]
    ensures SeqLastElem(a) == SeqLastElem(b)
{
    // Dafny can automatically prove this lemma
}

lemma Seq_AllElemsEqualToVal_ThenLastElemEqualsToVal<T>(s:seq<T>, v:T)
    requires |s| > 0
    requires forall e :: e in s
                ==> e == v
    ensures s[|s|-1] == v
{
    assert s[|s|-1] in s;
}

lemma Lemma_SeqWithTwoElem_HighlightEachOne<T>(s:seq<T>)
    requires |s| == 2
    ensures forall e :: e in s
                ==> e == s[0] || e == s[1]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_OneElemSeq_AllElemsAreTheElem<T>(s:seq<T>)
    requires |s| == 1
    ensures forall e :: e in s
                ==> e == s[0]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Seq_JumpFirstElem<T>(a:seq<T>, b:seq<T>, e:T)
    requires a == [e] + b

    ensures forall i :: 1 <= i < |a| ==> a[i] == b[i-1]
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_NonEmptySetIsNotEmpty<T>(s:set<T>, e:T)
    requires e in s
    ensures s != {}
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_ThreeSet_Elem<T>(s1:set<T>, s2:set<T>, s3:set<T>, e:T)
    requires e in (s1 + s2 + s3)
    ensures e in s1 || e in s2 || e in s3
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Map_IfNotEmpty_ThenExistKey<T, U>(m:map<T, U>)
    requires m != map[]

    ensures exists k :: k in m
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Set_NextElemIsInSet_ThenAllElemInSet<T>(sequence:seq<T>, i:int, elem_set:set<T>)
    requires 0 <= i < |sequence|
    requires forall e :: e in sequence[..i]
                        ==> e in elem_set
    requires sequence[i] in elem_set

    ensures forall e :: e in sequence[..i+1]
                        ==> e in elem_set
{
    // Dafny can automatically prove this lemma
}

lemma Lemma_Set_Equality<T>(s1:set<T>, s2:set<T>)
    requires forall e :: e in s1 ==> e in s2
    requires forall e :: e in s2 ==> e in s1

    ensures s1 == s2
{
    // Dafny can automatically prove this lemma
}