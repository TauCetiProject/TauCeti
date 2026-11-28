/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
import Mathlib.Algebra.Module.Rat
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.NumberTheory.NumberField.Discriminant.Basic
import TauCeti.NumberTheory.NumberField.Discriminant.Compositum

/-!
# Root discriminants after adjoining roots of unity

If the cyclotomic level is coprime to the discriminant of the base, their contributions
factor exactly as a product of root discriminants. This isolates the entire dependence on
the base field in a fixed factor when bounding root discriminants in a cyclotomic tower.
-/

public section

open NumberField

namespace IsCyclotomicExtension

/-- The root discriminant of an `n`-th cyclotomic field over `ℚ` is at most `n`. -/
theorem Rat.rootDiscr_le (n : ℕ) [NeZero n] (F : Type*) [Field F] [NumberField F]
    [IsCyclotomicExtension {n} ℚ F] : rootDiscr F ≤ n := by
  simp only [rootDiscr_def, Rat.finrank n F, ← Int.natCast_natAbs, Int.cast_natCast,
    Rat.natAbs_discr (n := n) (K := F)]
  calc
    _ ≤ ((n : ℝ) ^ n.totient) ^ (n.totient : ℝ)⁻¹ := by
      refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
      exact_mod_cast Nat.div_le_self _ _
    _ = n := Real.pow_rpow_inv_natCast (Nat.cast_nonneg n)
      (Nat.totient_pos.mpr (NeZero.pos n)).ne'

/-- Adjoining the `n`-th roots of unity to a number field whose discriminant is coprime to `n`
multiplies the root discriminant by the root discriminant of `ℚ(μₙ)`. -/
theorem rootDiscr_eq_mul_of_coprime_level (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L]
    (n : ℕ) [IsCyclotomicExtension {n} K L] (hcop : (discr K).natAbs.Coprime n) :
    rootDiscr L = rootDiscr K * rootDiscr (CyclotomicField n ℚ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · let eK := AlgEquiv.ofBijective (Algebra.ofId K L)
      ⟨(algebraMap K L).injective, isCyclotomicExtension_zero_iff.mp inferInstance⟩
    -- Use the splitting-field algebra, for which the cyclotomic instance is registered.
    let : Algebra ℚ (CyclotomicField 0 ℚ) := CyclotomicField.algebra 0 ℚ
    let eQ := AlgEquiv.ofBijective (Algebra.ofId ℚ (CyclotomicField 0 ℚ))
      ⟨(algebraMap ℚ (CyclotomicField 0 ℚ)).injective,
        isCyclotomicExtension_zero_iff.mp inferInstance⟩
    rw [← eK.toRingEquiv.rootDiscr_eq, ← eQ.toRingEquiv.rootDiscr_eq, rootDiscr_rat, mul_one]
  have : NeZero n := ⟨hn⟩
  let ζ := zeta n K L
  have hζ : IsPrimitiveRoot ζ n := zeta_spec n K L
  let F := IntermediateField.adjoin ℚ ({ζ} : Set L)
  let B := (IsScalarTower.toAlgHom ℚ K L).fieldRange
  let eB : K ≃ₐ[ℚ] B := AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom ℚ K L)
  have : IsCyclotomicExtension {n} ℚ F := hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : IsGalois ℚ F := isGalois {n} ℚ F
  have htop : F ⊔ B = ⊤ :=
    TauCeti.IntermediateField.adjoin_sup_fieldRange_eq_top ℚ K L
      (IntermediateField.adjoin_eq_top_of_algebra _ _ (adjoin_primitive_root_eq_top hζ))
  let : Algebra ℚ (CyclotomicField n ℚ) := CyclotomicField.algebra n ℚ
  let eF := algEquiv {n} ℚ F (CyclotomicField n ℚ)
  rw [TauCeti.NumberField.rootDiscr_eq_mul_of_isCoprime_discr htop
    (hζ.isCoprime_discr_adjoin_fieldRange K hcop), ← eB.toRingEquiv.rootDiscr_eq,
    eF.toRingEquiv.rootDiscr_eq, mul_comm]

end IsCyclotomicExtension
