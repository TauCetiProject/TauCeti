/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Integral

/-!
# Integral closures and base change of the fraction field

Let `A` be a domain with fraction field `K`, and let `L` be an algebraic extension of `K`. Every
element of `L` is an element of the integral closure of `A` in `L` divided by an element of `A`.
Hence, for any `K`-algebra `K'`, the tensor product `K' ⊗[K] L` is spanned over `K'` by the
elements `1 ⊗ b` with `b` in the integral closure of `A` in `L`.

## Main results

* `TauCeti.span_one_tmul_integralClosure_eq_top`: the elements `1 ⊗ b`, for `b` in the integral
  closure of `A` in `L`, span `K' ⊗[K] L` over `K'`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {A K L K' : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [Field L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L] [CommRing K'] [Algebra K K']

/-- The elements `1 ⊗ b`, for `b` in the integral closure of `A` in `L`, span `K' ⊗[K] L` over
`K'`: every element of `L` is an element of the integral closure divided by an element of `A`. -/
theorem span_one_tmul_integralClosure_eq_top :
    Submodule.span K' (Set.range fun b : integralClosure A L => (1 : K') ⊗ₜ[K] (b : L)) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  induction y using TensorProduct.inductionOn with
  | add t₁ t₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | tmul k l =>
    have hl : IsAlgebraic A l :=
      (IsFractionRing.isAlgebraic_iff A K L).mpr (Algebra.IsAlgebraic.isAlgebraic l)
    obtain ⟨a, ha, hint⟩ := hl.exists_integral_multiple
    have ha' : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
    let b : integralClosure A L := ⟨a • l, hint⟩
    have hbl : (b : L) = algebraMap A K a • l := (algebraMap_smul K a l).symm
    have key : k ⊗ₜ[K] l =
        (k * algebraMap K K' (algebraMap A K a)⁻¹) • ((1 : K') ⊗ₜ[K] (b : L)) := by
      have h : k * algebraMap K K' (algebraMap A K a)⁻¹ *
          (algebraMap A K a • (1 : K')) = k := by
        rw [Algebra.smul_def, mul_one, mul_assoc, ← map_mul, inv_mul_cancel₀ ha', map_one, mul_one]
      rw [hbl, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, h]
    rw [key]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

end TauCeti
