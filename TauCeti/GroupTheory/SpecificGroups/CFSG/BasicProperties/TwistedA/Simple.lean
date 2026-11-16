/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.SpecificGroups.CFSG.Assembly.LieType
public import TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TwistedA.Basic
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Isometry.Simple
import TauCeti.FieldTheory.Finite.PowNeOne

/-!
# Simplicity of the twisted type-`A` groups on the classification list

For every valid `²A_r(q)` (`2 ≤ r`, and `3 ≤ q` when `r = 2`), this file proves that the finite
special unitary group `SU_{r+1}(q)` is perfect
(`TauCeti.TypeALieIndex.commutator_specialUnitary_eq_top`), identifies `(ofTwistedA r q hv).Group`
with `PSU_{r+1}(q)` (`TauCeti.TypeALieIndex.projectiveSpecialUnitaryEquivGroup`) via
`TauCeti.TypeALieIndex.specialUnitaryEquivFixedPoints` and
`TauCeti.DerivedCentralQuotient.quotientCenterEquivOfPerfect`, and deduces from
`Matrix.isSimpleGroup_quotient_center_specialIsometryGroup` that every `²A_r(q)` on the
classification list is simple (`TauCeti.TypeALieIndex.isSimpleGroup_group_ofTwistedA` and
`TauCeti.ValidLieTypeIndex.isSimpleGroup_twistedA`), following the transport pattern of
`TauCeti.GroupTheory.SpecificGroups.CFSG.BasicProperties.TypeA`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Wiley (1972), §14.1.
* D. E. Taylor, *The Geometry of the Classical Groups*, Heldermann (1992), Chapter 10, Theorems
  10.9 and 10.20.
* L. C. Grove, *Classical Groups and Geometric Algebra* (2002), Chapter 11.
-/

public section

noncomputable section

open Matrix

namespace TauCeti.TypeALieIndex

private theorem isSimpleGroup_and_commutator_specialIsometryGroup_ofTwistedA (r : ℕ)
    (q : PrimePower) (hv : (LieTypeIndex.twistedA r q).Valid) :
    let d := (ofTwistedA r q hv).1
    let G := (typeAGraphConjugator d.rank
      (GaloisField d.characteristic (d.fieldExponent * 2))).val.specialIsometryGroup
      (iterateFrobenius _ d.characteristic d.fieldExponent)
    commutator G = ⊤ ∧ IsSimpleGroup (G ⧸ Subgroup.center G) := by
  intro d G; let K := GaloisField d.characteristic (d.fieldExponent * 2)
  let σ := iterateFrobenius K d.characteristic d.fieldExponent
  let Q := (typeAGraphConjugator d.rank K).val
  have hr_eq : d.rank = r := by simp [d, ValidLieTypeIndex.rank, ValidLieTypeIndex.dynkinType]
  have hpow_eq : d.characteristic ^ d.fieldExponent = q.card := by
    simp [d, ValidLieTypeIndex.characteristic, ValidLieTypeIndex.fieldExponent, PrimePower.card_def]
  obtain ⟨hr2, hq3⟩ := (LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1
  have : NeZero d.rank := ⟨by omega⟩; have := d.nonempty_isotropicPoints_galoisField (r := d.rank)
  have hperf : (∃ c : K, c ≠ 0 ∧ c ^ 2 ≠ 1 ∧ σ c = c) ∨
      (∃ u w : Fin (d.rank + 1) → K, u ≠ 0 ∧ w ∉ K ∙ u ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ u) = 0 ∧
        (σ ∘ w) ⬝ᵥ (Q *ᵥ w) = 0 ∧ (σ ∘ u) ⬝ᵥ (Q *ᵥ w) = 0) ∨
      (3 ≤ Fintype.card (Fin (d.rank + 1)) ∧ ∃ c : K, c ≠ 0 ∧ c * σ c ≠ 1) := by
    rcases (hr_eq ▸ hr2 : 2 ≤ d.rank).eq_or_lt with h2 | hr3
    · have h3 : 3 ≤ d.characteristic ^ d.fieldExponent := hpow_eq.symm ▸ hq3 (hr_eq ▸ h2.symm)
      obtain ⟨c, hc0, hc1⟩ := FiniteField.exists_ne_zero_pow_ne_one
        (k := d.characteristic ^ d.fieldExponent + 1) (Nat.succ_ne_zero _)
        (by rw [d.natCard_galoisField_mul_two]; nlinarith)
      exact .inr (.inr ⟨by rw [Fintype.card_fin]; omega, c, hc0,
        by simpa [σ, pow_succ', iterateFrobenius_def] using hc1⟩)
    · exact .inr (.inl (d.exists_notMem_span_and_comp_dotProduct_mulVec_eq_zero_of_three_le hr3))
  have hσ := d.involutive_iterateFrobenius_galoisField
  have hQ := d.transpose_map_typeAGraphConjugator_galoisField (r := d.rank)
  have hdet := (isUnits_det_units (typeAGraphConjugator d.rank K)).ne_zero
  have htr s := d.exists_add_neg_one_pow_mul_iterateFrobenius_eq (r := d.rank) (s := s)
  have hadm := d.exists_ne_zero_add_neg_one_pow_mul_iterateFrobenius_eq_zero (r := d.rank)
  exact ⟨commutator_specialIsometryGroup_eq_top hσ hQ hdet htr hadm hperf,
    isSimpleGroup_quotient_center_specialIsometryGroup hσ hQ hdet htr hadm hperf⟩

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
        Subgroup.center _) :=
    (ofTwistedA r q hv).1.fixedSubgroup_galoisFieldTwistedFrobenius_eq_specialIsometryGroup _ ▸
      (isSimpleGroup_and_commutator_specialIsometryGroup_ofTwistedA r q hv).2
  exact (projectiveSpecialUnitaryEquivGroup r q hv).symm.isSimpleGroup

end TauCeti.TypeALieIndex

namespace TauCeti.ValidLieTypeIndex

/-- **Every `²A_r(q)` on the classification list is simple.** -/
theorem isSimpleGroup_twistedA {r : ℕ} {q : PrimePower} (hv : (LieTypeIndex.twistedA r q).Valid) :
    IsSimpleGroup (ValidLieTypeIndex.Group ⟨_, hv⟩) := by
  unfold ValidLieTypeIndex.Group; rw [steinberg_twistedA, GraphTwistedIndex.steinberg_twistedA]
  exact TypeALieIndex.isSimpleGroup_group_ofTwistedA r q hv

end TauCeti.ValidLieTypeIndex

end
