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
embedding entry. The stored permutations, cycle notation, and carrier strings are transcribed from
the LMFDB downloads dated 21 November 2026. Each row is valid for the passport
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

The passport row is primitive, its degree being prime, and stores the map row `5T1-5_5_5-a` as its
own primitivization; that row certifies it.

Writing `r = finRotate 5`, the stored triples of rows `a`, `b`, `c` are respectively
`(r, r³, r)`, `(r, r, r³)`, and `(r, r², r²)`. Componentwise inversion followed by the sheet
reversal `Fin.revPerm` identifies them with `cyclicPowTriple 5 k` for `k = 3, 1, 2`, respectively.
Thus the database's orbit letters do not enumerate the exponent parameter in increasing order.
The literal cycle notation is checked against each stored permutation; the orbit letters are
external data, not an invariant derived from the exponent.

The equation and map strings are carried without an algebraic interpretation. The rows contain
no curve links or related-object labels. In particular, validity does not certify that the
displayed equation and map realize the stored monodromy.
The equality of each stored orbit size with the size of its true Galois orbit also requires
an orbit certificate, which these rows do not carry.

## Main results

* `TauCeti.PermutationTriple.LMFDB.isValidFor_cyclicFiveBelyiRecordA` and its companions for the
  rows `b` and `c`: the three map rows are valid for the passport.
* `TauCeti.PermutationTriple.LMFDB.isAggregatedFrom_cyclicFivePassportRecord`: the aggregations
  `num_orbits = 3` and `maxdegbf = 1` of the passport row are computed from the three map rows.
* `TauCeti.PermutationTriple.LMFDB.mapRowClasses_cyclicFivePassportRecord`: the stored triples of
  the three map rows represent exactly the classes of the passport.
* `TauCeti.PermutationTriple.LMFDB.sum_orbitSize_cyclicFivePassportRecord`: the stored orbit sizes
  of the three map rows sum to the stored passport size.
* `TauCeti.PermutationTriple.LMFDB.isPrimitivizationOf_cyclicFivePassportRecord`: the map row
  `5T1-5_5_5-a` certifies the stored primitivization of the passport row.

## References

* M. Musty, S. Schiavone, J. Sijsling, J. Voight, *A database of Belyi maps*, Proceedings of the
  Thirteenth Algorithmic Number Theory Symposium, Open Book Series 2, 2019, §2.
* LMFDB, map-row downloads, accessed 21 November 2026:
  [row a](https://www.lmfdb.org/Belyi/download_galmap_to_text/5T1-5_5_5-a),
  [row b](https://www.lmfdb.org/Belyi/download_galmap_to_text/5T1-5_5_5-b),
  [row c](https://www.lmfdb.org/Belyi/download_galmap_to_text/5T1-5_5_5-c).
-/

open Equiv

public section

namespace TauCeti
namespace PermutationTriple
namespace LMFDB

/-! ### The three map rows -/

/-- The map row `5T1-5_5_5-a`, with literal stored triple `(r, r³, r)`, for `r = finRotate 5`,
over the base field stored as the root `1` of `X - 1`. Its curve and map strings are transcribed
carrier data; their algebraic meaning is not certified here. -/
def cyclicFiveBelyiRecordA : BelyiRecord 5 where
  label := "5T1-5_5_5-a"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (Fin.revPerm (n := 5) • cyclicPowTriple 5 3)]
  triplesCyc := [([[0, 1, 2, 3, 4]], [[0, 3, 1, 4, 2]], [[0, 1, 2, 3, 4]])]
  curve := "y^2=x^6+2*x"
  map := "x^2*y+x^5+1"
  planeModel := "(-2)*t^2 - 2*t + x^5"
  planeConstant := "-1"
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- The map row `5T1-5_5_5-b`, with literal stored triple `(r, r, r³)`, for `r = finRotate 5`,
over the base field stored as the root `1` of `X - 1`. Its curve and map strings are transcribed
carrier data; their algebraic meaning is not certified here. -/
def cyclicFiveBelyiRecordB : BelyiRecord 5 where
  label := "5T1-5_5_5-b"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (Fin.revPerm (n := 5) • cyclicPowTriple 5 1)]
  triplesCyc := [([[0, 1, 2, 3, 4]], [[0, 1, 2, 3, 4]], [[0, 3, 1, 4, 2]])]
  curve := "y^2=x^6-2*x"
  map := "1/2/x^3*y+1/2"
  planeModel := "2*t^2 - 2*t + x^5"
  planeConstant := "1"
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- The map row `5T1-5_5_5-c`, with literal stored triple `(r, r², r²)`, for `r = finRotate 5`,
over the base field stored as the root `1` of `X - 1`. Its curve and map strings are transcribed
carrier data; their algebraic meaning is not certified here. -/
def cyclicFiveBelyiRecordC : BelyiRecord 5 where
  label := "5T1-5_5_5-c"
  plabel := "5T1-5_5_5"
  deg := 5
  lambdas := ({5}, {5}, {5})
  g := 2
  orbitSize := 1
  baseField := [-1, 1]
  embeddings := [(1, 0)]
  triples := [equivOppositeConvention 5 (Fin.revPerm (n := 5) • cyclicPowTriple 5 2)]
  triplesCyc := [([[0, 1, 2, 3, 4]], [[0, 2, 4, 1, 3]], [[0, 2, 4, 1, 3]])]
  curve := "y^2=4*x^5+1/4"
  map := "-1/4/x^5*y-1/8/x^5"
  planeModel := "(-1)*t^2 + t + 4*x^5"
  planeConstant := "1"
  curveLabel := none
  friends := []
  storedEmbeddingCount_eq_triplesLength := rfl

/-- The literal stored permutations of the map row `5T1-5_5_5-a`. -/
theorem cyclicFiveBelyiRecordA_triples :
    cyclicFiveBelyiRecordA.triples =
      [⟨(finRotate 5, finRotate 5 ^ 3, finRotate 5), by decide⟩] := by
  apply congrArg List.singleton
  apply Subtype.ext
  simp only [equivOppositeConvention_apply_coe,
    smul_σ0, smul_σ1, smul_σinf, cyclicPowTriple_σ0, cyclicPowTriple_σ1,
    cyclicPowTriple_σinf]
  decide +kernel

/-- The literal stored cycle notation of the map row `5T1-5_5_5-a`. -/
theorem cyclicFiveBelyiRecordA_triplesCyc :
    cyclicFiveBelyiRecordA.triplesCyc =
      [([[0, 1, 2, 3, 4]], [[0, 3, 1, 4, 2]], [[0, 1, 2, 3, 4]])] := by
  simp only [cyclicFiveBelyiRecordA]

/-- The literal stored permutations of the map row `5T1-5_5_5-b`. -/
theorem cyclicFiveBelyiRecordB_triples :
    cyclicFiveBelyiRecordB.triples =
      [⟨(finRotate 5, finRotate 5, finRotate 5 ^ 3), by decide⟩] := by
  apply congrArg List.singleton
  apply Subtype.ext
  simp only [equivOppositeConvention_apply_coe,
    smul_σ0, smul_σ1, smul_σinf, cyclicPowTriple_σ0, cyclicPowTriple_σ1,
    cyclicPowTriple_σinf]
  decide +kernel

/-- The literal stored cycle notation of the map row `5T1-5_5_5-b`. -/
theorem cyclicFiveBelyiRecordB_triplesCyc :
    cyclicFiveBelyiRecordB.triplesCyc =
      [([[0, 1, 2, 3, 4]], [[0, 1, 2, 3, 4]], [[0, 3, 1, 4, 2]])] := by
  simp only [cyclicFiveBelyiRecordB]

/-- The literal stored permutations of the map row `5T1-5_5_5-c`. -/
theorem cyclicFiveBelyiRecordC_triples :
    cyclicFiveBelyiRecordC.triples =
      [⟨(finRotate 5, finRotate 5 ^ 2, finRotate 5 ^ 2), by decide⟩] := by
  apply congrArg List.singleton
  apply Subtype.ext
  simp only [equivOppositeConvention_apply_coe,
    smul_σ0, smul_σ1, smul_σinf, cyclicPowTriple_σ0, cyclicPowTriple_σ1,
    cyclicPowTriple_σinf]
  decide +kernel

/-- The literal stored cycle notation of the map row `5T1-5_5_5-c`. -/
theorem cyclicFiveBelyiRecordC_triplesCyc :
    cyclicFiveBelyiRecordC.triplesCyc =
      [([[0, 1, 2, 3, 4]], [[0, 2, 4, 1, 3]], [[0, 2, 4, 1, 3]])] := by
  simp only [cyclicFiveBelyiRecordC]

/-- A map row storing the database form of the sheet reversal of
`cyclicPowTriple 5 k`, for `k` and `k + 1` prime to `5`, written by its single cycle-notation entry,
with orbit size one, the partitions `[5]` at each branch point and genus two, is valid for the
passport `5T1-5_5_5`. -/
private theorem isValidFor_of_triples_eq_revPerm_smul_cyclicPowTriple {q : BelyiRecord 5} {k : ℕ}
    (hk : k.Coprime 5) (hk' : (k + 1).Coprime 5) {c : CycleNotationTriple 5} (hdeg : q.deg = 5)
    (horbitSize : q.orbitSize = 1)
    (htriples : q.triples =
      [equivOppositeConvention 5 (Fin.revPerm (n := 5) • cyclicPowTriple 5 k)])
    (htriplesCyc : q.triplesCyc = [c])
    (h0 : (Fin.revPerm * (finRotate 5)⁻¹ * Fin.revPerm⁻¹).IsCycleNotation c.1)
    (h1 : (Fin.revPerm * (finRotate 5 ^ k)⁻¹ * Fin.revPerm⁻¹).IsCycleNotation c.2.1)
    (hinf : (Fin.revPerm * finRotate 5 ^ (k + 1) * Fin.revPerm⁻¹).IsCycleNotation c.2.2)
    (hlambdas : q.lambdas = ({5}, {5}, {5})) (hg : q.g = 2) :
    q.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  BelyiRecord.isValidFor_of_triples_eq_singleton hdeg horbitSize htriples htriplesCyc
    ⟨by simpa only [equivOppositeConvention_apply_coe, smul_σ0, cyclicPowTriple_σ0,
        mul_inv_rev, inv_inv, mul_assoc] using h0,
      by simpa only [equivOppositeConvention_apply_coe, smul_σ1, cyclicPowTriple_σ1,
        mul_inv_rev, inv_inv, mul_assoc] using h1,
      by simpa only [equivOppositeConvention_apply_coe, smul_σinf, cyclicPowTriple_σinf,
        mul_inv_rev, inv_inv, mul_assoc] using hinf⟩
    (by simpa using isConnected_cyclicPowTriple (k := k) (by decide))
    (by simpa only [PassportSpec.hasPassport_iff, ConnectedTriple.coe_smul,
      StoredTriple.toTriple_equivOppositeConvention] using
      (PassportSpec.hasPassport_smul_iff Fin.revPerm
        ⟨cyclicPowTriple 5 k, isConnected_cyclicPowTriple (by decide)⟩ _).mpr
          (PassportSpec.hasPassport_cyclicPowTriple hk hk'))
    (by rw [hlambdas, StoredTriple.toTriple_equivOppositeConvention,
      cycleData_smul, cycleData_cyclicPowTriple hk hk'])
    (by rw [hg, StoredTriple.toTriple_equivOppositeConvention, genus_smul,
      genus_cyclicPowTriple hk hk'])

/-- The map row `5T1-5_5_5-a` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordA :
    cyclicFiveBelyiRecordA.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_revPerm_smul_cyclicPowTriple (k := 3) (by decide) (by decide)
    rfl rfl rfl rfl ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ rfl rfl

/-- The map row `5T1-5_5_5-b` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordB :
    cyclicFiveBelyiRecordB.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_revPerm_smul_cyclicPowTriple (k := 1) (by decide) (by decide)
    rfl rfl rfl rfl ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
    ⟨by decide, by decide, by decide⟩ rfl rfl

/-- The map row `5T1-5_5_5-c` is valid for the passport `5T1-5_5_5`. -/
theorem isValidFor_cyclicFiveBelyiRecordC :
    cyclicFiveBelyiRecordC.IsValidFor (PassportSpec.cyclicTotallyRamified 5) :=
  isValidFor_of_triples_eq_revPerm_smul_cyclicPowTriple (k := 2) (by decide) (by decide)
    rfl rfl rfl rfl ⟨by decide, by decide, by decide⟩ ⟨by decide, by decide, by decide⟩
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

/-- The stored triples of the three map rows are pairwise non-isomorphic: translation and
sheet reversal give the three pairwise non-isomorphic triples of the passport row, reordered. -/
theorem pairwise_not_equivalent_flatMap_triples_cyclicFivePassportRecord :
    ((cyclicFivePassportRecord.mapRows
        [cyclicFiveBelyiRecordA, cyclicFiveBelyiRecordB, cyclicFiveBelyiRecordC]).flatMap
          BelyiRecord.triples).Pairwise fun s s' ↦ ¬ s.toTriple.Equivalent s'.toTriple := by
  rw [mapRows_cyclicFivePassportRecord]
  change ((cyclicFivePassportRecord.triples.rotate 2).map
    (fun t ↦ equivOppositeConvention 5 (Fin.revPerm • t))).Pairwise _
  simp only [List.pairwise_map, StoredTriple.toTriple_equivOppositeConvention,
    ← IsoClass.mk_eq_mk_iff, ← IsoClass.quotient_mk,
    MulAction.orbitRel.Quotient.quotient_smul_eq]
  apply (List.rotate_perm _ 2).pairwise_iff (fun h ↦ Ne.symm h) |>.mpr
  simpa only [← IsoClass.mk_eq_mk_iff, ← IsoClass.quotient_mk] using
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
  simp only [← IsoClass.quotient_mk, MulAction.orbitRel.Quotient.quotient_smul_eq]
  tauto

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

/-- The map row `5T1-5_5_5-a` certifies the stored primitivization of the passport row
`5T1-5_5_5`, which is primitive. -/
theorem isPrimitivizationOf_cyclicFivePassportRecord :
    cyclicFiveBelyiRecordA.IsPrimitivizationOf cyclicFivePassportRecord
      ⟨cyclicPowTriple 5 1, isConnected_cyclicPowTriple (by decide)⟩ :=
  .of_card_primitivizationBlock_eq_one
    (isValidAt_cyclicFivePassportRecord.card_primitivizationBlock_eq_one_iff.mpr rfl) rfl
    (PassportSpec.hasPassport_cyclicPowTriple (by decide) (by decide))
    isValidFor_cyclicFiveBelyiRecordA

end LMFDB
end PermutationTriple
end TauCeti
