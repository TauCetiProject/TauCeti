/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Golay.Basic
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.CoordinateDiscriminant
public import TauCeti.LinearAlgebra.IntegralLattice.ConstructionA.Discriminant
public import TauCeti.LinearAlgebra.IntegralLattice.CoordinatePower.Unit
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum

import TauCeti.Data.Int.SumSquares

/-!
# Roots of the Golay Construction A lattice

The norm-two vectors of `TauCeti.BinaryGolay.constructionALattice` are precisely the
forty-eight vectors `±2 eᵢ`. Its twenty-four positive coordinate roots have Gram matrix `2 I`,
so these roots form twenty-four mutually orthogonal copies of `A₁`. In particular its
minimum is two and its kissing number is forty-eight.

## References

* G. Nebe,
  [*Extremal lattices*](https://www.math.rwth-aachen.de/homes/Gabriele.Nebe/talks/OW12.pdf),
  slides 10–11, for the Golay code lattice and its minimal vectors.
-/

public section

namespace TauCeti.BinaryGolay

open Finset Matrix

private theorem golay_norm_intCast (z : Fin 24 → ℤ) :
    constructionALattice.norm (fun i ↦ (z i : ℚ)) = ((∑ i, z i ^ 2 : ℤ) : ℚ) / 2 := by
  rw [constructionALattice_eq_integralLattice]
  exact ConstructionA.integralLattice_norm_intCast 2 code.toAddSubgroup _ z

/-- The positive coordinate root `2 eᵢ` of the Golay Construction A lattice. -/
def coordinateRoot (i : Fin 24) : constructionALattice :=
  ⟨Pi.single i 2, by
    rw [constructionALattice_carrier]
    exact ConstructionA.single_mem_lattice 2 code.toAddSubgroup i⟩

/-- The coordinates of a positive Golay lattice root. -/
@[simp]
theorem coe_coordinateRoot (i : Fin 24) :
    (coordinateRoot i : Fin 24 → ℚ) = Pi.single i 2 := by rw [coordinateRoot]

/-- The positive coordinate roots have Gram matrix `2 I`: different coordinates give
orthogonal copies of the root system `A₁`. -/
@[simp↓]
theorem form_coordinateRoot_coordinateRoot (i j : Fin 24) :
    constructionALattice.form (coordinateRoot i) (coordinateRoot j) =
      if i = j then 2 else 0 := by
  rw [coe_coordinateRoot, coe_coordinateRoot, constructionALattice_form, ConstructionA.form_apply]
  by_cases h : i = j <;> simp [h, dotProduct_single]

/-- Every positive coordinate root has norm two. -/
@[simp↓]
theorem norm_coordinateRoot (i : Fin 24) :
    constructionALattice.norm (coordinateRoot i) = 2 := by
  rw [IntegralLattice.norm_apply, form_coordinateRoot_coordinateRoot]
  simp

/-- Every positive coordinate root has integral norm two. -/
@[simp]
theorem integralNorm_coordinateRoot (i : Fin 24) :
    constructionALattice.integralNorm (coordinateRoot i) = 2 := by
  exact_mod_cast (constructionALattice.integralNorm_cast (coordinateRoot i)).trans
    (norm_coordinateRoot i)

/-- **Classification of the Golay lattice roots.** With the halved dot product, an ambient
vector in the Golay lattice has norm two exactly when it is `2 eᵢ` or `-2 eᵢ`. -/
theorem norm_eq_two_iff {x : Fin 24 → ℚ} (hx : x ∈ constructionALattice.carrier) :
    constructionALattice.norm x = 2 ↔
      ∃ i : Fin 24, x = Pi.single i 2 ∨ x = -Pi.single i 2 := by
  constructor
  · intro hnorm
    have hx' : x ∈ ConstructionA.lattice 2 code.toAddSubgroup := constructionALattice_carrier ▸ hx
    obtain ⟨z, hz, rfl⟩ := (ConstructionA.mem_lattice 2).mp hx'
    have hsum : ∑ i, z i ^ 2 = 4 := by
      rw [golay_norm_intCast] at hnorm
      have hq : ((∑ i, z i ^ 2 : ℤ) : ℚ) = 4 := by linarith
      exact_mod_cast hq
    have hw : hammingNorm (fun i ↦ (z i : ZMod 2)) ∈
        ({0, 8, 12, 16, 24} : Finset ℕ) := hammingNorm_mem hz
    have hle := hammingNorm_intCast_le_sum_sq z
    simp only [mem_insert, mem_singleton] at hw
    have hzero : hammingNorm (fun i ↦ (z i : ZMod 2)) = 0 := by omega
    have hcast := hammingNorm_eq_zero.mp hzero
    have heven (i : Fin 24) : (2 : ℤ) ∣ z i := by
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hcast i)
    choose w hw using heven
    have hsumw : ∑ i, w i ^ 2 = 1 := by
      have h : ∑ i, z i ^ 2 = 4 * ∑ i, w i ^ 2 := by
        simp_rw [hw, mul_pow]
        simp [mul_sum]
      omega
    obtain ⟨i, hi⟩ := exists_eq_single_or_neg_single_of_sum_sq_eq_one w hsumw
    refine ⟨i, hi.imp (fun h ↦ ?_) (fun h ↦ ?_)⟩ <;>
      funext j <;> by_cases hj : j = i
    · subst j
      simp [hw, h]
    · simp [hw, h, hj]
    · subst j
      simp [hw, h]
    · simp [hw, h, hj]
  · rintro ⟨i, rfl | rfl⟩
    · exact norm_coordinateRoot i
    · rw [IntegralLattice.norm_neg]
      exact norm_coordinateRoot i

/-- The norm-two shell consists of the positive coordinate roots and their negatives. -/
theorem mem_vectorsOfNorm_two_iff (x : constructionALattice) :
    x ∈ constructionALattice.vectorsOfNorm 2 ↔
      ∃ i : Fin 24, x = coordinateRoot i ∨ x = -coordinateRoot i := by
  rw [IntegralLattice.mem_vectorsOfNorm, norm_eq_two_iff x.2]
  simp only [← coe_coordinateRoot, ← Submodule.coe_neg, Subtype.ext_iff]

/-- The roots generate exactly the zero-code sublattice `2 ℤ²⁴`. Thus the root lattice has
no additional glue coming from nonzero Golay codewords. -/
theorem span_vectorsOfNorm_two :
    Submodule.span ℤ
      ((fun x : constructionALattice ↦ (x : Fin 24 → ℚ)) ''
        constructionALattice.vectorsOfNorm 2) =
      (ConstructionA.zeroLattice 2 (Fin 24)).carrier := by
  refine le_antisymm (Submodule.span_le.mpr ?_) ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, rfl | rfl⟩ := (mem_vectorsOfNorm_two_iff x).mp hx
    · rw [ConstructionA.zeroLattice_carrier]
      simpa only [SetLike.mem_coe, coe_coordinateRoot, Nat.cast_ofNat] using
        ConstructionA.single_mem_lattice 2 ⊥ i
    · rw [ConstructionA.zeroLattice_carrier]
      simpa only [SetLike.mem_coe, Submodule.coe_neg, coe_coordinateRoot,
        Nat.cast_ofNat] using
        Submodule.neg_mem _ (ConstructionA.single_mem_lattice 2 ⊥ i)
  · intro x hx
    obtain ⟨z, _, rfl⟩ := (ConstructionA.mem_lattice 2).mp
      ((ConstructionA.zeroLattice_carrier 2 (Fin 24)) ▸ hx)
    have heven := (ConstructionA.intCast_mem_zeroLattice_carrier_iff 2 (Fin 24) z).mp hx
    choose w hw using heven
    have hsum : (fun i ↦ (z i : ℚ)) =
        ∑ i, w i • (coordinateRoot i : Fin 24 → ℚ) := by
      funext j
      simp [Pi.single_apply, hw, mul_comm]
    rw [hsum]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ (w i)
      (Submodule.subset_span ⟨coordinateRoot i,
        IntegralLattice.mem_vectorsOfNorm.mpr (norm_coordinateRoot i), rfl⟩)

/-- **The Golay root lattice is `A₁²⁴`.** The zero-code lattice generated by all Golay roots
is isometric to the orthogonal sum of twenty-four copies of the existing `A₁` lattice.
The ambient isometry doubles every coordinate. -/
noncomputable def rootLatticeIsometry :
    IntegralLattice.Isometry (IntegralLattice.a1.coordinatePower (Fin 24))
      (ConstructionA.zeroLattice 2 (Fin 24)) := by
  -- The zero lattice's definition is opaque across modules; use its exported carrier and form.
  have hzero : ConstructionA.integralLattice 2 (⊥ : AddSubgroup (Fin 24 → ZMod 2))
      (by rw [(AddSubgroup.toZModSubmodule 2).map_bot]; exact bot_le) =
      ConstructionA.zeroLattice 2 (Fin 24) := by
    apply IntegralLattice.ext
    · rw [ConstructionA.integralLattice_carrier, ConstructionA.zeroLattice_carrier]
    · rw [ConstructionA.integralLattice_form, ConstructionA.zeroLattice_form]
  -- Match the natural modulus cast in the Construction A isometry's source.
  have hpower : IntegralLattice.a1.coordinatePower (Fin 24) =
      ((2 : ℕ) : ℤ) • IntegralLattice.unitLattice (Fin 24) := by
    simpa only [Nat.cast_ofNat] using
      IntegralLattice.coordinatePower_a1_eq_smul_unitLattice (Fin 24)
  exact (IntegralLattice.Isometry.ofEq hpower).trans
    ((ConstructionA.scaledStandardIsometry 2).trans (IntegralLattice.Isometry.ofEq hzero))

/-- The `A₁²⁴` root-lattice identification doubles the standard coordinates. -/
@[simp]
theorem rootLatticeIsometry_apply (x : Fin 24 → ℚ) : rootLatticeIsometry x = (2 : ℚ) • x := by
  rw [rootLatticeIsometry]
  simp only [IntegralLattice.Isometry.trans_apply, IntegralLattice.Isometry.ofEq_apply,
    ConstructionA.scaledStandardIsometry_apply]
  ext i
  simp

/-- The forty-eight roots, indexed by a coordinate and a sign. The Boolean value `false`
selects `2 eᵢ`, and `true` selects `-2 eᵢ`. -/
noncomputable def rootsEquiv :
    Fin 24 × Bool ≃ constructionALattice.vectorsOfNorm 2 :=
  Equiv.ofBijective
    (fun p ↦ ⟨if p.2 then -coordinateRoot p.1 else coordinateRoot p.1, by
      rw [IntegralLattice.mem_vectorsOfNorm]
      cases p.2
      · exact norm_coordinateRoot p.1
      · simpa only [ite_true, Submodule.coe_neg, IntegralLattice.norm_neg] using
          norm_coordinateRoot p.1⟩) (by
    constructor
    · rintro ⟨i, b⟩ ⟨j, c⟩ h
      have hi := congrArg (fun x : constructionALattice.vectorsOfNorm 2 ↦
        (x.1 : Fin 24 → ℚ) i) h
      have hij : i = j := by
        by_contra hij
        cases b <;> cases c <;>
          norm_num only [Bool.false_eq_true, ite_false, ite_true,
            Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same,
            Pi.single_eq_of_ne hij] at hi
      apply Prod.ext hij
      subst j
      cases b <;> cases c
      · rfl
      · norm_num only [Bool.false_eq_true, ite_false, ite_true,
          Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same] at hi
      · norm_num only [Bool.false_eq_true, ite_false, ite_true,
          Submodule.coe_neg, coe_coordinateRoot, Pi.neg_apply, Pi.single_eq_same] at hi
      · rfl
    · rintro ⟨x, hx⟩
      obtain ⟨i, h | h⟩ := (mem_vectorsOfNorm_two_iff x).mp hx
      · exact ⟨(i, false), Subtype.ext h.symm⟩
      · exact ⟨(i, true), Subtype.ext h.symm⟩)

/-- The explicit root indexing recovers the chosen signed coordinate root. -/
@[simp]
theorem rootsEquiv_apply (i : Fin 24) (b : Bool) :
    (rootsEquiv (i, b)).1 = if b then -coordinateRoot i else coordinateRoot i := by
  rw [rootsEquiv]
  rfl

/-- The Golay lattice has forty-eight norm-two vectors. -/
theorem representationNumber_constructionALattice_two :
    constructionALattice.representationNumber 2 = 48 := by
  rw [IntegralLattice.representationNumber_def, ← Nat.card_coe_set_eq,
    ← Nat.card_congr rootsEquiv]
  simp [Nat.card_eq_fintype_card]

/-- The Golay lattice has minimum two. -/
theorem minimum_constructionALattice : constructionALattice.minimum = 2 :=
  isPosDef_constructionALattice.minimum_eq_two isEven_constructionALattice
    (integralNorm_coordinateRoot 0)

/-- The forty-eight coordinate roots are precisely the shortest nonzero Golay lattice
vectors, so its kissing number is forty-eight. -/
theorem kissingNumber_constructionALattice : constructionALattice.kissingNumber = 48 := by
  rw [IntegralLattice.kissingNumber_eq_representationNumber
    (by rw [minimum_constructionALattice]; decide), minimum_constructionALattice]
  exact representationNumber_constructionALattice_two

end TauCeti.BinaryGolay
