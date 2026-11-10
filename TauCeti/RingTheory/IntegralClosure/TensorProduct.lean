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
Hence the integral closure spans `L` over `K`, and, for any `K`-algebra `K'`, the tensor product
`K' ⊗[K] L` is spanned over `K'` by the elements `1 ⊗ b` with `b` in the integral closure of `A`
in `L`.

## Main results

* `TauCeti.span_integralClosure_eq_top`: the integral closure of `A` in `L` spans `L` over `K`.
* `TauCeti.span_one_tmul_integralClosure_eq_top`: the elements `1 ⊗ b`, for `b` in the integral
  closure of `A` in `L`, span `K' ⊗[K] L` over `K'`.
-/

public section

open scoped TensorProduct

namespace TauCeti

variable {A K L K' : Type*} [CommRing A] [IsDomain A] [Field K] [Algebra A K]
  [IsFractionRing A K] [CommRing L] [Algebra A L] [Algebra K L] [IsScalarTower A K L]
  [Algebra.IsAlgebraic K L]

/-- The integral closure of `A` in `L` spans `L` over `K`: every element of `L` is an element of
the integral closure divided by a nonzero element of `A`. -/
theorem span_integralClosure_eq_top :
    Submodule.span K (integralClosure A L : Set L) = ⊤ := by
  refine eq_top_iff.2 fun x _ => ?_
  obtain ⟨a, ha, hint⟩ := ((IsFractionRing.isAlgebraic_iff A K L).mpr
    (Algebra.IsAlgebraic.isAlgebraic x)).exists_integral_multiple
  have ha' : algebraMap A K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr ha
  have hmem : a • x ∈ Submodule.span K (integralClosure A L : Set L) :=
    Submodule.subset_span hint
  convert Submodule.smul_mem _ (algebraMap A K a)⁻¹ hmem using 1
  rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ ha', one_smul]

variable [CommRing K'] [Algebra K K']

/-- The elements `1 ⊗ b`, for `b` in the integral closure of `A` in `L`, span `K' ⊗[K] L` over
`K'`. -/
theorem span_one_tmul_integralClosure_eq_top :
    Submodule.span K' (Set.range fun b : integralClosure A L => (1 : K') ⊗ₜ[K] (b : L)) = ⊤ := by
  have h := congrArg (Submodule.baseChange K')
    (span_integralClosure_eq_top (A := A) (K := K) (L := L))
  rw [Submodule.baseChange_top, Submodule.baseChange_span] at h
  rw [← h]
  congr 1
  ext x
  simp

end TauCeti
