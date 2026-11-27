/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.Compositum
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop
import Mathlib.Algebra.Algebra.Hom.Rat

/-!
# Root discriminants after adjoining roots of unity

If the cyclotomic level is coprime to the discriminant of the base, their contributions
factor exactly as a product of root discriminants. This isolates the entire dependence on
the base field in a fixed factor when bounding root discriminants in a cyclotomic tower.
-/

public section

open NumberField

namespace IsCyclotomicExtension

/-- Adjoining the `n`-th roots of unity to a number field whose discriminant is coprime to `n`
multiplies the root discriminant by the root discriminant of `ℚ(μₙ)`. -/
theorem rootDiscr_eq_mul_of_coprime_level (K L : Type*) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [IsScalarTower ℚ K L]
    (n : ℕ) [IsCyclotomicExtension {n} K L] (hcop : (discr K).natAbs.Coprime n) :
    rootDiscr L = rootDiscr K * rootDiscr (CyclotomicField n ℚ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · let eK := AlgEquiv.ofBijective (Algebra.ofId K L)
      ⟨(algebraMap K L).injective, isCyclotomicExtension_zero_iff.mp inferInstance⟩
    let eQ := AlgEquiv.ofBijective (Algebra.ofId ℚ (CyclotomicField 0 ℚ))
      ⟨(algebraMap ℚ (CyclotomicField 0 ℚ)).injective,
        isCyclotomicExtension_zero_iff.mp
          (CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfNat ℚ)⟩
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
  have hcop' : n.Coprime (discr B).natAbs := by
    rw [← discr_eq_discr_of_ringEquiv K eB.toRingEquiv]
    exact hcop.symm
  have : NeZero (n : ℚ) := ⟨Nat.cast_ne_zero.mpr hn⟩
  let eF := @algEquiv {n} ℚ F _ _ _ ‹_› (CyclotomicField n ℚ) _ _
    (CyclotomicField.isCyclotomicExtension n ℚ)
  have hF := eF.toRingEquiv.rootDiscr_eq
  rw [TauCeti.NumberField.rootDiscr_eq_mul_of_isCoprime_discr htop
    (Rat.isCoprime_discr_of_coprime_level F hcop'), ← eB.toRingEquiv.rootDiscr_eq, hF, mul_comm]

end IsCyclotomicExtension
