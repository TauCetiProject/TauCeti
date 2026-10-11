/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Examples
public import TauCeti.LinearAlgebra.IntegralLattice.Scaling
public import TauCeti.LinearAlgebra.IntegralLattice.Unimodular

/-!
# Rank-one integral lattices

The lattice `rankOne a` is `ℤ ⊂ ℚ` with bilinear form `B(x,y) = axy`, for any integer `a`.
Integer representatives evaluate the integral form as `akl` and the integral norm as `ak²`.
Its rank is one, its signed determinant is `a`, and it is even exactly when `a` is even.
It is unimodular exactly when `a` is a unit. The sign of `a` determines definiteness and
signature, including the degenerate zero form.

This family includes odd lattices as well as the root lattices `A₁ = ⟨2⟩` and `⟨-2⟩`.
Duality, the cyclic discriminant group, and the level are computed in
`TauCeti.LinearAlgebra.IntegralLattice.RankOne.Discriminant`.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti.IntegralLattice

open Module

private def rankOneMatrix (a : ℤ) : Matrix (Fin 1) (Fin 1) ℤ := fun _ _ ↦ a

private theorem isSymm_rankOneMatrix (a : ℤ) : (rankOneMatrix a).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  rfl

/-- The integral lattice `⟨a⟩`: the integers in `ℚ`, with `B(1,1) = a`.
The parameter may vanish, giving a degenerate lattice of rank one. -/
noncomputable def rankOne (a : ℤ) : IntegralLattice ℚ :=
  ofGramMatrix (Basis.singleton (Fin 1) ℚ) (rankOneMatrix a) (isSymm_rankOneMatrix a)

/-- The carrier of `⟨a⟩` consists of the integers. -/
@[simp]
theorem mem_rankOne_carrier_iff (a : ℤ) (x : ℚ) :
    x ∈ (rankOne a).carrier ↔ ∃ z : ℤ, (z : ℚ) = x := by
  classical
  rw [rankOne, ofGramMatrix_carrier, Module.Basis.mem_span_iff_repr_mem]
  simp [Basis.singleton_repr]

/-- The bilinear form of `⟨a⟩` is `axy`. -/
@[simp]
theorem rankOne_form_apply (a : ℤ) (x y : ℚ) : (rankOne a).form x y = a * x * y := by
  let _ : DecidableEq (Fin 1) := Classical.decEq _
  rw [rankOne, ofGramMatrix_form, Matrix.toBilin_apply]
  simp only [Fin.sum_univ_one, Basis.singleton_repr, Matrix.map_apply, rankOneMatrix,
    eq_intCast]
  ring

/-- The norm of `⟨a⟩` is `ax²`. -/
@[simp]
theorem rankOne_norm_apply (a : ℤ) (x : ℚ) : (rankOne a).norm x = a * x ^ 2 := by
  rw [norm_apply, rankOne_form_apply]
  ring

/-- Evaluate the integral restriction using integer representatives of actual carrier vectors. -/
theorem integralForm_rankOne_eq {a : ℤ} (w x : rankOne a) {k l : ℤ}
    (hw : (w : ℚ) = k) (hx : (x : ℚ) = l) :
    (rankOne a).integralForm w x = a * k * l := by
  have h : ((rankOne a).integralForm w x : ℚ) = (a * k * l : ℤ) := by
    rw [integralForm_cast, rankOne_form_apply, hw, hx]
    push_cast
    rfl
  exact_mod_cast h

/-- Evaluate the integral norm using an integer representative in the actual carrier. -/
theorem integralNorm_rankOne_eq {a : ℤ} (w : rankOne a) {k : ℤ}
    (hw : (w : ℚ) = k) : (rankOne a).integralNorm w = a * k ^ 2 := by
  rw [integralNorm_apply, integralForm_rankOne_eq w w hw hw, pow_two, mul_assoc]

/-- Every member of the family has rank one, including the zero form. -/
@[simp]
theorem finrank_rankOne (a : ℤ) : finrank ℤ (rankOne a) = 1 := by
  rw [(rankOne a).finrank_carrier]
  exact Module.finrank_self ℚ

/-- The lattice `⟨a⟩` is even exactly when `a` is even. -/
@[simp]
theorem isEven_rankOne_iff (a : ℤ) : (rankOne a).IsEven ↔ Even a := by
  rw [rankOne, isEven_ofGramMatrix_iff]
  simp [rankOneMatrix]

/-- The rank-one lattice `⟨2m⟩` is even for every integer `m`. -/
theorem isEven_rankOne_two_mul (m : ℤ) : (rankOne (2 * m)).IsEven :=
  (isEven_rankOne_iff _).mpr (even_two_mul m)

/-- The signed determinant of `⟨a⟩` is `a`. -/
@[simp]
theorem rankOne_determinant (a : ℤ) : (rankOne a).determinant = a := by
  rw [rankOne, determinant_ofGramMatrix]
  simp [rankOneMatrix]

/-- The nonnegative discriminant of `⟨a⟩` is `|a|`. -/
@[simp]
theorem rankOne_discriminant (a : ℤ) : (rankOne a).discriminant = a.natAbs := by
  rw [discriminant_def, rankOne_determinant]

/-- Nonzero parameters give nondegenerate rank-one lattices. -/
instance instIsNondegenerateRankOne (a : ℤ) [NeZero a] : (rankOne a).IsNondegenerate := by
  exact ⟨(rankOne a).determinant_ne_zero_iff.mp (by simpa using NeZero.ne a)⟩

/-- The rank-one Gram-matrix lattice on the standard basis of `ℚ` with entry `a` is `⟨a⟩`. -/
theorem ofGramMatrix_singleton_eq_rankOne (a : ℤ) {c : ℤ} (hc : c = a)
    (h : (Matrix.of fun (_ _ : Fin 1) ↦ c).IsSymm) :
    ofGramMatrix (Basis.singleton (Fin 1) ℚ) (Matrix.of fun _ _ ↦ c) h = rankOne a := by
  subst c
  have hmatrix : (Matrix.of fun (_ _ : Fin 1) ↦ a) = rankOneMatrix a := by
    ext i j
    simp only [Matrix.of_apply, rankOneMatrix]
  simp only [rankOne, hmatrix]

/-- `⟨a⟩` is the negative of `⟨-a⟩`. -/
theorem rankOne_eq_neg_rankOne_neg (a : ℤ) : rankOne a = -rankOne (-a) := by
  refine IntegralLattice.ext ?_ ?_
  · ext x
    simp [neg_carrier]
  · refine LinearMap.BilinForm.ext fun x y ↦ ?_
    simp only [neg_form, LinearMap.neg_apply, rankOne_form_apply]
    push_cast
    ring

/-- The lattice `⟨a⟩` is unimodular exactly when `a` is a unit of `ℤ`. -/
@[simp high]
theorem isUnimodular_rankOne_iff (a : ℤ) : (rankOne a).IsUnimodular ↔ IsUnit a := by
  by_cases ha : a = 0
  · subst a
    constructor
    · intro h
      have := (rankOne 0).determinant_ne_zero_iff.mpr h.nondegenerate
      simp at this
    · simp
  · let : NeZero a := ⟨ha⟩
    rw [(rankOne a).isUnimodular_iff_isUnit_determinant, rankOne_determinant]

/-- The positive rank-one root lattice is `⟨2⟩`. -/
theorem rankOne_two : rankOne 2 = a1 := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦ ?_) (LinearMap.ext₂ fun x y ↦ ?_)
  · rw [mem_rankOne_carrier_iff, mem_a1_carrier_iff]
  · simp only [rankOne_form_apply, a1_form_apply, Int.cast_ofNat]

/-- The negative rank-one root lattice is `⟨-2⟩`. -/
theorem rankOne_neg_two : rankOne (-2) = negativeA1 := by
  refine IntegralLattice.ext (Submodule.ext fun x ↦ ?_) (LinearMap.ext₂ fun x y ↦ ?_)
  · rw [mem_rankOne_carrier_iff, mem_negativeA1_carrier_iff]
  · simp only [rankOne_form_apply, negativeA1_form_apply, Int.cast_neg, Int.cast_ofNat]

/-- A positive parameter gives a positive definite rank-one lattice. -/
theorem isPosDef_rankOne {a : ℤ} (ha : 0 < a) : (rankOne a).IsPosDef := by
  rw [(rankOne a).isPosDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  nlinarith [sq_pos_of_ne_zero hx]

/-- A negative parameter gives a negative definite rank-one lattice. -/
theorem isNegDef_rankOne {a : ℤ} (ha : a < 0) : (rankOne a).IsNegDef := by
  rw [(rankOne a).isNegDef_iff]
  intro x hx
  rw [rankOne_form_apply]
  have haq : (a : ℚ) < 0 := by exact_mod_cast ha
  nlinarith [sq_pos_of_ne_zero hx]

/-- Positive rank-one lattices have signature `(1,0,0)`. -/
theorem rankOne_signature_of_pos {a : ℤ} (ha : 0 < a) : (rankOne a).signature = (1, 0, 0) := by
  have hvanish := (rankOne a).isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp
    (isPosDef_rankOne ha)
  have hsum := (rankOne a).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- Negative rank-one lattices have signature `(0,0,1)`. -/
theorem rankOne_signature_of_neg {a : ℤ} (ha : a < 0) : (rankOne a).signature = (0, 0, 1) := by
  have hvanish := (rankOne a).isNegDef_iff_sigPos_eq_zero_and_sigNull_eq_zero.mp
    (isNegDef_rankOne ha)
  have hsum := (rankOne a).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- Positive definiteness is equivalent to positivity of the parameter. -/
@[simp]
theorem isPosDef_rankOne_iff (a : ℤ) : (rankOne a).IsPosDef ↔ 0 < a := by
  refine ⟨fun h ↦ ?_, isPosDef_rankOne⟩
  have hone := (rankOne a).isPosDef_iff.mp h 1 one_ne_zero
  rw [rankOne_form_apply] at hone
  exact_mod_cast (by simpa using hone : (0 : ℚ) < a)

/-- Negative definiteness is equivalent to negativity of the parameter. -/
@[simp]
theorem isNegDef_rankOne_iff (a : ℤ) : (rankOne a).IsNegDef ↔ a < 0 := by
  refine ⟨fun h ↦ ?_, isNegDef_rankOne⟩
  have hone := (rankOne a).isNegDef_iff.mp h 1 one_ne_zero
  rw [rankOne_form_apply] at hone
  exact_mod_cast (by simpa using hone : (a : ℚ) < 0)

/-- The zero parameter gives a degenerate rank-one lattice. -/
theorem isDegenerate_rankOne_zero : (rankOne 0).IsDegenerate := by
  rw [(rankOne 0).isDegenerate_iff_not_nondegenerate]
  intro h
  exact (rankOne 0).determinant_ne_zero_iff.mpr h (by simp)

/-- The zero rank-one form has signature `(0,1,0)`. -/
@[simp]
theorem rankOne_zero_signature : (rankOne 0).signature = (0, 1, 0) := by
  have hsigNeg : (rankOne 0).sigNeg = 0 :=
    (rankOne 0).isPosSemidef_iff_sigNeg_eq_zero.mp
      ((rankOne 0).isPosSemidef_iff.mpr fun x ↦ by simp)
  have hsigPos : (rankOne 0).sigPos = 0 :=
    (rankOne 0).isNegSemidef_iff_sigPos_eq_zero.mp
      ((rankOne 0).isNegSemidef_iff.mpr fun x ↦ by simp)
  have hsum := (rankOne 0).signature_sum_eq_finrank
  simp only [Module.finrank_self] at hsum
  simp only [signature, Prod.mk.injEq]
  omega

end TauCeti.IntegralLattice
