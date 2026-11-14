/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Simple
import TauCeti.FieldTheory.Finite.Frobenius
import TauCeti.FieldTheory.Finite.PowAddSelf

/-!
# Simplicity of the twisted type-`A` groups on the classification list

For every valid `²A_r(q)` (`2 ≤ r`, and `3 ≤ q` when `r = 2`), this file proves that the finite
special unitary group `SU_{r+1}(q)` is perfect, identifies `(ofTwistedA r q hv).Group` with
`PSU_{r+1}(q)`, and deduces that every `²A_r(q)` on the classification list is simple.

## Main definitions and results

* `TauCeti.TypeALieIndex.commutator_specialUnitary_eq_top` and
  `TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroup`.
* `TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA` and
  `TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA`.

## References

* R. W. Carter, *Simple Groups of Lie Type* (1972), §14.1; D. E. Taylor (1992), Thms. 11.28--11.29.
-/

public section

noncomputable section

open Matrix
namespace TauCeti.TypeALieIndex
private theorem two_le_and_three_le_card_of_valid {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) : 2 ≤ r ∧ (r = 2 → 3 ≤ q.card) :=
  (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
private theorem witt_two_of_three_le_rank {d : ValidLieTypeIndex} {r : ℕ} (hr : 3 ≤ r) :
    ∃ u w : Fin (r + 1) → GaloisField d.characteristic (d.fieldExponent * 2),
      u ≠ 0 ∧ w ∉ GaloisField d.characteristic (d.fieldExponent * 2) ∙ u ∧
      (iterateFrobenius _ d.characteristic d.fieldExponent ∘ u) ⬝ᵥ
        ((typeAGraphConjugator r _).val *ᵥ u) = 0 ∧
      (iterateFrobenius _ d.characteristic d.fieldExponent ∘ w) ⬝ᵥ
        ((typeAGraphConjugator r _).val *ᵥ w) = 0 ∧
      (iterateFrobenius _ d.characteristic d.fieldExponent ∘ u) ⬝ᵥ
        ((typeAGraphConjugator r _).val *ᵥ w) = 0 := by
  let i₀ : Fin (r + 1) := ⟨0, by omega⟩; let i₁ : Fin (r + 1) := ⟨1, by omega⟩
  refine ⟨Pi.single i₀ 1, Pi.single i₁ 1, Pi.single_ne_zero_iff.mpr one_ne_zero, fun hmem ↦ ?_,
    ?_, ?_, ?_⟩
  · obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 := congrFun ha i₁; simp [i₀, i₁] at h1
  · rw [← d.unitaryForm_apply]; exact d.unitaryForm_single_single (by simp [i₀, Fin.ext_iff]; omega)
  · rw [← d.unitaryForm_apply]; exact d.unitaryForm_single_single (by simp [i₁, Fin.ext_iff]; omega)
  · have hs : iterateFrobenius (GaloisField d.characteristic (d.fieldExponent * 2))
        d.characteristic d.fieldExponent ∘ Pi.single i₀ 1 = Pi.single i₀ 1 := funext fun j ↦ by
      rcases eq_or_ne j i₀ with rfl | hj
      · simp only [Function.comp_apply, Pi.single_eq_same, map_one]
      · simp only [Function.comp_apply, Pi.single_eq_of_ne hj, map_zero]
    have hne : i₁ ≠ i₀.rev := by simp [i₀, i₁, Fin.ext_iff]; omega
    rw [hs, single_dotProduct, one_mul, mulVec_single_one, col_apply, typeAGraphConjugator_apply]
    simp [hne]
private theorem isSimpleGroup_and_commutator_specialIsometryGroup_ofTwistedA (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid) :
    let d := (ofTwistedA r q hv).1
    let G := (typeAGraphConjugator d.rank
      (GaloisField d.characteristic (d.fieldExponent * 2))).val.specialIsometryGroup
      (iterateFrobenius _ d.characteristic d.fieldExponent)
    commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G) := by
  intro d G
  have hr_eq : d.rank = r := by simp [d, ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]
  have hpow_eq : d.characteristic ^ d.fieldExponent = q.card := by
    simp [d, ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent, PrimePower.card_def]
  obtain ⟨hr2, hq3⟩ := two_le_and_three_le_card_of_valid hv
  have : NeZero d.rank := ⟨by omega⟩; have := d.nonempty_isotropicPoints_galoisField (r := d.rank)
  have hcard : Nat.card (GaloisField d.characteristic (d.fieldExponent * 2)) =
      (d.characteristic ^ d.fieldExponent) ^ 2 := by
    rw [GaloisField.card _ _ (Nat.mul_ne_zero d.fieldExponent_pos.ne' two_ne_zero), pow_mul]
  have htr (s : GaloisField d.characteristic (d.fieldExponent * 2))
      (hs : iterateFrobenius _ d.characteristic d.fieldExponent s = (-1) ^ d.rank * s) :
      ∃ t, t + (-1) ^ d.rank * iterateFrobenius _ d.characteristic d.fieldExponent t = s := by
    simp_rw [iterateFrobenius_def] at hs ⊢
    exact FiniteField.exists_add_neg_one_pow_mul_pow_eq hcard d.rank hs
  have hadm : ∃ a ≠ (0 : GaloisField d.characteristic (d.fieldExponent * 2)),
      a + (-1) ^ d.rank * iterateFrobenius _ d.characteristic d.fieldExponent a = 0 := by
    simp_rw [iterateFrobenius_def]
    exact FiniteField.exists_ne_zero_add_neg_one_pow_mul_pow_eq_zero hcard d.rank
  have hpg : ((3 ≤ Fintype.card (Fin (d.rank + 1)) ∧ ∃ c : GaloisField d.characteristic
      (d.fieldExponent * 2), c ≠ 0 ∧ c * iterateFrobenius _ d.characteristic d.fieldExponent c ≠ 1))
      ∨ ∃ u w : Fin (d.rank + 1) → GaloisField d.characteristic (d.fieldExponent * 2),
        u ≠ 0 ∧ w ∉ GaloisField d.characteristic (d.fieldExponent * 2) ∙ u ∧
        (iterateFrobenius _ d.characteristic d.fieldExponent ∘ u) ⬝ᵥ
          ((typeAGraphConjugator d.rank _).val *ᵥ u) = 0 ∧
        (iterateFrobenius _ d.characteristic d.fieldExponent ∘ w) ⬝ᵥ
          ((typeAGraphConjugator d.rank _).val *ᵥ w) = 0 ∧
        (iterateFrobenius _ d.characteristic d.fieldExponent ∘ u) ⬝ᵥ
          ((typeAGraphConjugator d.rank _).val *ᵥ w) = 0 := by
    rcases (hr_eq ▸ hr2 : 2 ≤ d.rank).eq_or_lt with h2 | hr3
    · obtain ⟨c, hc0, hc1⟩ := FiniteField.exists_ne_zero_mul_pow_ne_one hcard
        (hpow_eq.symm ▸ hq3 (hr_eq ▸ h2.symm))
      exact Or.inl ⟨by rw [Fintype.card_fin]; omega, c, hc0,
        by simpa [iterateFrobenius_def] using hc1⟩
    · exact Or.inr (witt_two_of_three_le_rank hr3)
  have hcomm := Matrix.commutator_specialIsometryGroup_eq_top
    d.involutive_iterateFrobenius_galoisField d.transpose_map_typeAGraphConjugator_galoisField
    (isUnits_det_units _).ne_zero htr hadm (hpg.elim (Or.inr ∘ Or.inr) (Or.inr ∘ Or.inl))
  refine ⟨hcomm, Matrix.isSimpleGroup_quotient_center_specialIsometryGroup
    d.involutive_iterateFrobenius_galoisField d.transpose_map_typeAGraphConjugator_galoisField
    (isUnits_det_units _).ne_zero htr hadm ?_ hcomm⟩
  rcases hpg with ⟨_, c, hc0, hc1⟩ | hwitt
  · exact Or.inl ⟨c * iterateFrobenius _ d.characteristic d.fieldExponent c,
      mul_ne_zero hc0 ((map_ne_zero _).mpr hc0), hc1,
      by rw [map_mul, d.involutive_iterateFrobenius_galoisField c, mul_comm _ c]⟩
  · exact Or.inr (Or.inr hwitt)
/-- **The finite special unitary group of `²A_r(q)` is perfect.** -/
theorem commutator_specialUnitary_eq_top (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    commutator (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank)) = ⊤ := by
  rw [(ofTwistedA r q hv).1.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
  exact (isSimpleGroup_and_commutator_specialIsometryGroup_ofTwistedA r q hv).1
/-- **The group attached to `²A_r(q)` is the projective special unitary group `PSU_{r+1}(q)`.** -/
def projectiveSpecialUnitaryEquivGroup (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    (fixedSubgroup ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank) ⧸
      Subgroup.center (fixedSubgroup
        ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank))) ≃*
      (ofTwistedA r q hv).Group :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect (commutator_specialUnitary_eq_top r q hv)
    (specialUnitaryEquivFixedPoints r q hv)
/-- The isomorphism with `PSU_{r+1}(q)` sends the central quotient class of an element of the
derived subgroup to the class of the corresponding Steinberg fixed point. -/
@[simp]
theorem projectiveSpecialUnitaryEquivGroup_mk (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid)
    (x : commutator (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank))) :
    projectiveSpecialUnitaryEquivGroup r q hv (QuotientGroup.mk (s := Subgroup.center _)
        (x : fixedSubgroup
          ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank))) =
      ((MulEquiv.commutatorCongr (specialUnitaryEquivFixedPoints r q hv) x :
        commutator (ofTwistedA r q hv).FixedPoints) : (ofTwistedA r q hv).Group) :=
  DerivedCentralQuotient.quotientCenterEquivOfPerfect_mk _ _ x
/-- **The group attached to `²A_r(q)` is simple**, for every valid index. -/
theorem isSimpleGroup_group_ofTwistedA (r : ℕ) (q : PrimePower)
    (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ofTwistedA r q hv).Group := by
  have : IsSimpleGroup (fixedSubgroup
      ((ofTwistedA r q hv).1.galoisFieldTwistedFrobenius (ofTwistedA r q hv).1.rank) ⧸
        Subgroup.center _) := by
    rw [(ofTwistedA r q hv).1.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup]
    exact (isSimpleGroup_and_commutator_specialIsometryGroup_ofTwistedA r q hv).2
  exact (projectiveSpecialUnitaryEquivGroup r q hv).symm.isSimpleGroup
end TauCeti.TypeALieIndex
namespace TauCeti.ValidLieTypeIndex
/-- **Every `²A_r(q)` on the classification list is simple.** On the constructor `twistedA r q` the
Steinberg endomorphism of the assembly is that of the type-`A` family, so the assembled candidate
group is the `²A_r(q)` one. -/
theorem isSimpleGroup_twistedA {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group
  rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA r q hv
end TauCeti.ValidLieTypeIndex

end
