/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Root discriminants of composita

Taking degree-normalized roots of Mathlib's absolute-discriminant formula
`NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow` gives a product
formula for root discriminants. Coprime discriminants give the linear disjointness
required by that formula when one of the two fields is Galois.
-/

public section

open Module

namespace TauCeti.NumberField

open _root_.NumberField (discr rootDiscr rootDiscr_def)

/-- The root discriminant is invariant under field isomorphisms. -/
theorem _root_.RingEquiv.rootDiscr_eq {K L : Type*} [Field K] [Field L]
    [NumberField K] [NumberField L] (e : K ≃+* L) : rootDiscr K = rootDiscr L := by
  rw [rootDiscr_def, rootDiscr_def, _root_.NumberField.discr_eq_discr_of_ringEquiv K e,
    e.toRatAlgEquiv.toLinearEquiv.finrank_eq]

/-- A compositum of two number fields of coprime discriminants, one Galois, has root
discriminant equal to the product of their root discriminants. -/
theorem rootDiscr_eq_mul_of_isCoprime_discr {L : Type*} [Field L] [NumberField L]
    {K F : IntermediateField ℚ L} [IsGalois ℚ K] (htop : K ⊔ F = ⊤)
    (hcop : IsCoprime (discr K) (discr F)) : rootDiscr L = rootDiscr K * rootDiscr F := by
  have hld := _root_.NumberField.linearDisjoint_of_isGalois_isCoprime_discr (L := L) K F hcop
  have hdeg := hld.finrank_sup
  rw [htop, IntermediateField.finrank_top'] at hdeg
  have hd := _root_.NumberField.natAbs_discr_eq_natAbs_discr_pow_mul_natAbs_discr_pow
    L K F hld htop (_root_.NumberField.isCoprime_differentIdeal_of_isCoprime_discr L hcop)
  have hK : (finrank ℚ K : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  have hF : (finrank ℚ F : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr finrank_pos.ne'
  simp only [rootDiscr_def, Int.abs_eq_natAbs]
  rw [hdeg, hd]
  push_cast
  rw [Real.mul_rpow (by positivity) (by positivity)]
  simp only [← Real.rpow_natCast_mul (abs_nonneg (_ : ℝ))]
  congr 2 <;> field_simp

end TauCeti.NumberField
