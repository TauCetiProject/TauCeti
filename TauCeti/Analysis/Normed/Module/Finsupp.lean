/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Analysis.Normed.MulAction
public import TauCeti.Analysis.Normed.Group.Finsupp
import TauCeti.LinearAlgebra.Finsupp.LSum

/-!
# The `ℓ¹`-sum of norms under scalar actions and linear maps on free modules

For a finitely supported function `f : α →₀ E` acted on by a bounded scalar action, scaling by `r`
multiplies the `ℓ¹`-sum of norms by at most `‖r‖` (`Finsupp.sum_norm_smul_le`). Consequently, a
linear map `f : (α →₀ R) →ₗ[R] (β →₀ E)` out of a free module whose basis images have `ℓ¹`-sum of
norms uniformly bounded by `C` is `ℓ¹`-bounded with constant `C` (`LinearMap.sum_norm_apply_le`).
-/

public section

namespace Finsupp

/-- Scaling a finitely supported function by `r` multiplies its `ℓ¹`-sum of norms by at most
`‖r‖`. -/
theorem sum_norm_smul_le {α R E : Type*} [SeminormedAddGroup R] [SeminormedAddCommGroup E]
    [SMulZeroClass R E] [IsBoundedSMul R E] (r : R) (f : α →₀ E) :
    ((r • f).sum fun _ a ↦ ‖a‖) ≤ ‖r‖ * f.sum fun _ a ↦ ‖a‖ := by
  rw [sum_norm_eq_sum_of_support_subset (r • f) support_smul, sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun a _ ↦ by
    simpa only [coe_smul, Pi.smul_apply] using norm_smul_le r (f a)

end Finsupp

namespace LinearMap

/-- **Uniform `ℓ¹`-bound for a linear map out of a free module.** If every basis vector
`Finsupp.single a 1` maps to a vector of `ℓ¹`-sum of norms at most `C`, then `f` multiplies the
`ℓ¹`-sum of norms by at most `C`. -/
theorem sum_norm_apply_le {α β R E : Type*} [SeminormedRing R] [SeminormedAddCommGroup E]
    [Module R E] [IsBoundedSMul R E] (f : (α →₀ R) →ₗ[R] (β →₀ E)) {C : ℝ}
    (hC : ∀ a, (f (Finsupp.single a 1)).sum (fun _ x ↦ ‖x‖) ≤ C) (v : α →₀ R) :
    ((f v).sum fun _ x ↦ ‖x‖) ≤ C * v.sum fun _ r ↦ ‖r‖ := by
  rw [f.apply_eq_finsuppSum_smul v, Finsupp.sum]
  refine (Finsupp.sum_norm_sum_le _ _).trans ?_
  calc
    ∑ a ∈ v.support, ((RingHom.id R (v a) • f (Finsupp.single a 1)).sum fun _ x ↦ ‖x‖)
        ≤ ∑ a ∈ v.support, ‖v a‖ * C := Finset.sum_le_sum fun a _ ↦
          (Finsupp.sum_norm_smul_le (v a) _).trans
            (mul_le_mul_of_nonneg_left (hC a) (norm_nonneg _))
    _ = C * v.sum fun _ r ↦ ‖r‖ := by rw [← Finset.sum_mul, mul_comm, Finsupp.sum]

end LinearMap
