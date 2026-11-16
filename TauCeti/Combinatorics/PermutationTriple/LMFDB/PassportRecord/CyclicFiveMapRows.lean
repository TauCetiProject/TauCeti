/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.LMFDB.CertificationLevel
public import TauCeti.Combinatorics.PermutationTriple.LMFDB.PassportRecord.Examples
public import TauCeti.Combinatorics.PermutationTriple.Passport.Cyclic

/-!
# The three map rows of the passport `5T1-5_5_5`

The passport `5T1-5_5_5` of degree five, with cyclic monodromy and totally ramified over `0`, `1`
and `∞`, has three isomorphism classes, represented by the triples `(r, r, r³)`, `(r, r², r²)` and
`(r, r³, r)` for the rotation `r` of the five sheets. The LMFDB tabulates it as three map rows
`5T1-5_5_5-a`, `5T1-5_5_5-b` and `5T1-5_5_5-c`, each a single Galois orbit stored over `ℚ` with one
embedding entry. This file carries reconstructions of these rows, described below, through the
map-row certificates: each is valid for the passport
(`TauCeti.PermutationTriple.LMFDB.BelyiRecord.IsValidFor`), and each stored map label extends the
stored passport label and agrees with the stored partitions.

Together with the passport row
`TauCeti.PermutationTriple.LMFDB.cyclicFivePassportRecord`, the three rows certify the
aggregations of the passport row: three map rows carry its label, and their largest stored orbit
size is one. They also exercise the sum formula
`TauCeti.PermutationTriple.LMFDB.PassportRecord.IsValidAt.sum_orbitSize_eq_passSize_iff`: the
stored triples of the three rows are pairwise non-isomorphic, and they represent every
class of the passport, so the stored orbit sizes sum to the stored passport size `3`. Neither fact
is asserted by the rows themselves; both are proved here from the classification of the passport.

The stored triple of each row is the database form, under
`TauCeti.PermutationTriple.equivOppositeConvention`, of the corresponding stored triple
`TauCeti.PermutationTriple.cyclicPowTriple 5 k` of the passport row; its components are the
inverses of those of `cyclicPowTriple 5 k`. These triples, and the order in which the orbit letters
`a`, `b`, `c` enumerate them, are a choice made in this file and are not checked against the
literal stored permutations of the frozen records. The three rows are therefore reconstructions
of the rows `5T1-5_5_5-a`, `5T1-5_5_5-b` and `5T1-5_5_5-c` from the passport row, not copies of
the frozen records, and the certificates here are certificates of these reconstructions: they do
not by themselves carry the frozen records. The orbit letters are carrier data, as are the
equations, the curve links and the labels of related objects, which validity does not read
(`TauCeti.PermutationTriple.LMFDB.BelyiRecord.isValidFor_congr`); they are left empty here rather
than reproduced. The equality of each stored orbit size with the size of the Galois orbit of the
corresponding isomorphism class is an orbit certificate, which these rows do not carry.

## Main results

* `TauCeti.PermutationTriple.LMFDB.isValidFor_cyclicFiveBelyiRecordA` and its companions for the
  rows `b` and `c`: the three map rows are valid for the passport.
* `TauCeti.PermutationTriple.LMFDB.isAggregatedFrom_cyclicFivePassportRecord`: the aggregations
  `num_orbits = 3` and `maxdegbf = 1` of the passport row are computed from the three map rows.
* `TauCeti.PermutationTriple.LMFDB.mapRowClasses_cyclicFivePassportRecord`: the stored triples of
  the three map rows represent exactly the classes of the passport.
* `TauCeti.PermutationTriple.LMFDB.sum_orbitSize_cyclicFivePassportRecord`: the stored orbit sizes
  of the three map rows sum to the stored passport size.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, §2.
* LMFDB, [Belyi maps](https://www.lmfdb.org/Belyi/).
-/

open Equiv

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-! ### The three map rows -/

/-- A reconstruction of the map row `5T1-5_5_5-a`, with stored triple the database form
`(r⁻¹, r⁻¹, r²)` of `cyclicPowTriple 5 1 = (r, r, r³)`, over the base field stored as the
root `1` of `X - 1`. The stored triple is derived from the passport row rather than copied from
the frozen record, and the assignment of the orbit letter `a` to it is not checked against that
record. The equations, the curve link and the labels of related objects are carrier data that
validity does not read, and are left empty rather than reproduced. -/
@[expose] def cyclicFiveBelyiRecordA : BelyiRecord 5 where
  label := "5T1-5_5_5-a"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (cyclicPowTriple 5 1)]
  triplesCyc := [([[0, 4, 3, 2, 1]], [[0, 4, 3, 2, 1]], [[0, 2, 4, 1, 3]])]
  curve := ""
  map := ""
  planeModel := ""
  planeConstant := ""
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- A reconstruction of the map row `5T1-5_5_5-b`, with stored triple the database form
`(r⁻¹, r³, r³)` of `cyclicPowTriple 5 2 = (r, r², r²)`, over the base field stored as the
root `1` of `X - 1`. The stored triple is derived from the passport row rather than copied from
the frozen record, and the assignment of the orbit letter `b` to it is not checked against that
record. The equations, the curve link and the labels of related objects are carrier data that
validity does not read, and are left empty rather than reproduced. -/
@[expose] def cyclicFiveBelyiRecordB : BelyiRecord 5 where
  label := "5T1-5_5_5-b"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (cyclicPowTriple 5 2)]
  triplesCyc := [([[0, 4, 3, 2, 1]], [[0, 3, 1, 4, 2]], [[0, 3, 1, 4, 2]])]
  curve := ""
  map := ""
  planeModel := ""
  planeConstant := ""
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- A reconstruction of the map row `5T1-5_5_5-c`, with stored triple the database form
`(r⁻¹, r², r⁴)` of `cyclicPowTriple 5 3 = (r, r³, r)`, over the base field stored as the
root `1` of `X - 1`. The stored triple is derived from the passport row rather than copied from
the frozen record, and the assignment of the orbit letter `c` to it is not checked against that
record. The equations, the curve link and the labels of related objects are carrier data that
validity does not read, and are left empty rather than reproduced. -/
@[expose] def cyclicFiveBelyiRecordC : BelyiRecord 5 where
  label := "5T1-5_5_5-c"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (cyclicPowTriple 5 3)]
  triplesCyc := [([[0, 4, 3, 2, 1]], [[0, 2, 4, 1, 3]], [[0, 4, 3, 2, 1]])]
  curve := ""
  map := ""
  planeModel := ""
  planeConstant := ""
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- A map row storing the database form of `cyclicPowTriple 5 k`, for `k` and `k + 1` prime to
`5`, written by its single cycle-notation entry, with orbit size one, the partitions `[5]` at each
branch point and genus two, is valid for the passport `5T1-5_5_5`. -/
private theorem isValidFor_of_triples_eq_cyclicPowTriple {q : BelyiRecord 5} {k : ℕ}
    (hk : k.Coprime 5) (hk' : (k + 1).Coprime 5) {c : CycleNotationTriple 5} (hdeg : q.deg = 5)
    (horbitSize : q.orbitSize = 1)
    (htriples : q.triples = [equivOppositeConvention 5 (cyclicPowTriple 5 k)])
    (htriplesCyc : q.triplesCyc = [c]) (h0 : (finRotate 5)⁻¹.IsCycleNotation c.1)
    (h1 : (finRotate 5 ^ k)⁻¹.IsCycleNotation c.2.1)
    (hinf : (finRotate 5 ^ (k + 1)).IsCycleNotation c.2.2)
    (hlambdas : q.lambdas = ({5}, {5}, {5})) (hg : q.g = 2) :
    q.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  BelyiRecord.isValidFor_of_triples_eq_singleton hdeg horbitSize htriples htriplesCyc
    ⟨by simpa using h0, by simpa using h1, by simpa using hinf⟩
    (by simpa using isConnected_cyclicPowTriple (k := k) (by decide))
    (by simpa using PassportSpec.hasPassport_cyclicPowTriple hk hk')
    (by rw [hlambdas, StoredTriple.toTriple_equivOppositeConvention,
      cycleData_cyclicPowTriple hk hk'])
    (by rw [hg, StoredTriple.toTriple_equivOppositeConvention, genus_cyclicPowTriple hk hk'])

/-- The reconstructed map row `5T1-5_5_5-a` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordA :
    cyclicFiveBelyiRecordA.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_cyclicPowTriple (k := 1) (by decide) (by decide) rfl rfl rfl rfl
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ rfl rfl

/-- The reconstructed map row `5T1-5_5_5-b` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordB :
    cyclicFiveBelyiRecordB.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_cyclicPowTriple (k := 2) (by decide) (by decide) rfl rfl rfl rfl
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ rfl rfl

/-- The reconstructed map row `5T1-5_5_5-c` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordC :
    cyclicFiveBelyiRecordC.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_cyclicPowTriple (k := 3) (by decide) (by decide) rfl rfl rfl rfl
    ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ rfl rfl

/-! ### The map labels -/

namespace BelyiRecord

/-- The map label `5T1-5_5_5-a` parses to the passport `5T1-5_5_5` and the orbit `a`. -/
theorem parseMapLabel_cyclicFiveBelyiRecordA :
    parseMapLabel 5 cyclicFiveBelyiRecordA.label = some (⟨⟨0, by simp⟩, {5}, {5}, {5}⟩, "a") := by
  rw [parseMapLabel_eq_some_iff_append]
  exact ⟨cyclicFivePassportRecord.plabel, by decide +kernel, by decide +kernel,
    by simp, PassportRecord.parsePassportLabel_cyclicFivePassportRecord⟩

/-- The map label `5T1-5_5_5-b` parses to the passport `5T1-5_5_5` and the orbit `b`. -/
theorem parseMapLabel_cyclicFiveBelyiRecordB :
    parseMapLabel 5 cyclicFiveBelyiRecordB.label = some (⟨⟨0, by simp⟩, {5}, {5}, {5}⟩, "b") := by
  rw [parseMapLabel_eq_some_iff_append]
  exact ⟨cyclicFivePassportRecord.plabel, by decide +kernel, by decide +kernel,
    by simp, PassportRecord.parsePassportLabel_cyclicFivePassportRecord⟩

/-- The map label `5T1-5_5_5-c` parses to the passport `5T1-5_5_5` and the orbit `c`. -/
theorem parseMapLabel_cyclicFiveBelyiRecordC :
    parseMapLabel 5 cyclicFiveBelyiRecordC.label = some (⟨⟨0, by simp⟩, {5}, {5}, {5}⟩, "c") := by
  rw [parseMapLabel_eq_some_iff_append]
  exact ⟨cyclicFivePassportRecord.plabel, by decide +kernel, by decide +kernel,
    by simp, PassportRecord.parsePassportLabel_cyclicFivePassportRecord⟩

/-- The stored label of the map row `5T1-5_5_5-a` extends its passport label and agrees with its
stored partitions. -/
theorem hasValidLabel_cyclicFiveBelyiRecordA : cyclicFiveBelyiRecordA.HasValidLabel :=
  (hasValidLabel_iff_of_parse parseMapLabel_cyclicFiveBelyiRecordA).mpr ⟨by decide +kernel, rfl⟩

/-- The stored label of the map row `5T1-5_5_5-b` extends its passport label and agrees with its
stored partitions. -/
theorem hasValidLabel_cyclicFiveBelyiRecordB : cyclicFiveBelyiRecordB.HasValidLabel :=
  (hasValidLabel_iff_of_parse parseMapLabel_cyclicFiveBelyiRecordB).mpr ⟨by decide +kernel, rfl⟩

/-- The stored label of the map row `5T1-5_5_5-c` extends its passport label and agrees with its
stored partitions. -/
theorem hasValidLabel_cyclicFiveBelyiRecordC : cyclicFiveBelyiRecordC.HasValidLabel :=
  (hasValidLabel_iff_of_parse parseMapLabel_cyclicFiveBelyiRecordC).mpr ⟨by decide +kernel, rfl⟩

-- The group component `5T1` of a map label, which a map row does not certify by itself, is
-- certified by the passport row sharing its passport label.
example (P : PassportSpec 5) :
    P.HasLabel ⟨⟨0, by simp⟩, {5}, {5}, {5}⟩ ↔
      PassportSpec.HasPassport
        ⟨cyclicPowTriple 5 1, isConnected_cyclicPowTriple (by decide)⟩ P :=
  hasValidLabel_cyclicFiveBelyiRecordB.hasLabel_iff_hasPassport
    parseMapLabel_cyclicFiveBelyiRecordB isValidAt_cyclicFivePassportRecord
    PassportRecord.hasValidLabel_cyclicFivePassportRecord rfl P

end BelyiRecord

/-! ### Reconciliation with the passport row -/

/-- All three map rows carry the passport label `5T1-5_5_5`. -/
theorem mapRows_cyclicFivePassportRecord :
    cyclicFivePassportRecord.mapRows
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC] =
      [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC] := by
  rw [PassportRecord.mapRows_def, List.filter_eq_self]
  simp [cyclicFivePassportRecord, cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB,
    cyclicFiveBelyiRecordC]

/-- The aggregations of the passport row `5T1-5_5_5` are computed from its three map rows: three
rows carry its label, and their largest stored orbit size is one. -/
theorem isAggregatedFrom_cyclicFivePassportRecord :
    cyclicFivePassportRecord.IsAggregatedFrom
      [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC] where
  numOrbits_eq := by rw [mapRows_cyclicFivePassportRecord]; rfl
  maxdegbf_eq := by rw [mapRows_cyclicFivePassportRecord]; rfl

/-- The stored triples of the three map rows are pairwise non-isomorphic: they are the database
forms of the pairwise non-isomorphic triples of the passport row. -/
theorem pairwise_not_equivalent_flatMap_triples_cyclicFivePassportRecord :
    ((cyclicFivePassportRecord.mapRows
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC]).flatMap
          BelyiRecord.triples).Pairwise fun s s' ↦ ¬ s.toTriple.Equivalent s'.toTriple := by
  have h : (cyclicFivePassportRecord.mapRows
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC]).flatMap
          BelyiRecord.triples =
        cyclicFivePassportRecord.triples.map (equivOppositeConvention 5) := by
    rw [mapRows_cyclicFivePassportRecord]
    rfl
  rw [h, List.pairwise_map]
  simpa only [StoredTriple.toTriple_equivOppositeConvention] using
    pairwise_not_equivalent_triples_cyclicFivePassportRecord

open scoped Classical in
/-- The stored triples of the three map rows represent exactly the isomorphism classes of the
passport `5T1-5_5_5`. -/
theorem mapRowClasses_cyclicFivePassportRecord :
    cyclicFivePassportRecord.mapRowClasses
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC] =
      (PassportSpec.cyclicTotallyRamified 5).classSet.image ConnectedIsoClass.forget := by
  ext c
  rw [PassportRecord.mem_mapRowClasses, mapRows_cyclicFivePassportRecord,
    PassportSpec.classSet_cyclicTotallyRamified_five]
  simp only [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC,
    BelyiRecord.mem_storedClasses, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp,
    exists_eq_left, StoredTriple.toTriple_equivOppositeConvention, Finset.image_insert,
    Finset.image_singleton, ConnectedIsoClass.forget_mk, Finset.mem_insert,
    Finset.mem_singleton, eq_comm]

/-- **The sum formula for `5T1-5_5_5`.** The stored orbit sizes of the three map rows sum to the
stored passport size `3`: their stored triples are pairwise non-isomorphic, and represent every
class of the passport. -/
theorem sum_orbitSize_cyclicFivePassportRecord :
    ((cyclicFivePassportRecord.mapRows
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC]).map
          BelyiRecord.orbitSize).sum = cyclicFivePassportRecord.passSize := by
  refine (isValidAt_cyclicFivePassportRecord.sum_orbitSize_eq_passSize_iff
    (PassportSpec.hasPassport_cyclicPowTriple (by decide) (by decide)) (fun q hq ↦ ?_)
    pairwise_not_equivalent_flatMap_triples_cyclicFivePassportRecord).mpr
    mapRowClasses_cyclicFivePassportRecord
  rw [mapRows_cyclicFivePassportRecord] at hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact isValidFor_cyclicFiveBelyiRecordA
  · exact isValidFor_cyclicFiveBelyiRecordB
  · exact isValidFor_cyclicFiveBelyiRecordC

end LMFDB
end PermutationTriple
end TauCeti
