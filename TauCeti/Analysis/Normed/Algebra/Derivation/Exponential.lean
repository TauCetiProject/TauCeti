/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The exponential of a bounded derivation

A derivation of a normed algebra `B` is a linear map `D : B → B` satisfying the Leibniz rule
`D (x * y) = x * D y + D x * y`. Here `B` need not be commutative or unital, so Mathlib's
`Derivation`, which requires a commutative algebra, does not apply, and the Leibniz rule is a
hypothesis on a continuous linear map.

When `D` is bounded and `B` is complete, the exponential `exp D` of `D` in the Banach algebra
`B →L[𝕜] B` of bounded operators is multiplicative. As `exp D` is invertible in that algebra,
with inverse `exp (-D)`, it is an algebra automorphism of `B`. Applied to `z • D` for complex `z`,
this gives the entire family of automorphisms `exp (z • D)` used in the Singer–Wermer theorem.

## Main results

* `ContinuousLinearMap.exp_apply_mul_of_derivation`: if `D` is a bounded derivation of a Banach
  algebra, then `exp D (x * y) = exp D x * exp D y`.

## References

* H. G. Dales, *Banach Algebras and Automatic Continuity*, §2.7, for derivations of Banach
  algebras and the automorphisms `exp (z • D)`.
-/

public section

open NormedSpace

namespace ContinuousLinearMap

variable {𝕜 B : Type*} [RCLike 𝕜] [NonUnitalNormedRing B] [NormedSpace 𝕜 B]
  [IsScalarTower 𝕜 B B] [SMulCommClass 𝕜 B B] [CompleteSpace B]

/-- **The exponential of a bounded derivation is multiplicative.** If `D` is a bounded linear map
on a Banach algebra satisfying the Leibniz rule `D (x * y) = x * D y + D x * y`, then its
exponential in the algebra of bounded operators satisfies `exp D (x * y) = exp D x * exp D y`. -/
theorem exp_apply_mul_of_derivation (D : B →L[𝕜] B)
    (hD : ∀ x y, D (x * y) = x * D y + D x * y) (x y : B) :
    exp D (x * y) = exp D x * exp D y := by
  -- Each orbit `t ↦ exp (t • D) z` solves `u' = D u`, and by the Leibniz rule so does the
  -- product `g t = exp (t • D) x * exp (t • D) y`.
  have hU (z : B) (t : 𝕜) :
      HasDerivAt (fun t : 𝕜 ↦ exp (t • D) z) (D (exp (t • D) z)) t := by
    simpa using (hasDerivAt_exp_smul_const' D t).clm_apply (hasDerivAt_const t z)
  have hg (t : 𝕜) : HasDerivAt (fun t : 𝕜 ↦ exp (t • D) x * exp (t • D) y)
      (D (exp (t • D) x * exp (t • D) y)) t := by
    simpa [hD] using (mul 𝕜 B).hasDerivAt_of_bilinear (fun _ ↦ hU x t) (fun _ ↦ hU y t)
  -- Hence `exp (t • -D) (g t)` has zero derivative, so it is constant.
  have hF (t : 𝕜) : HasDerivAt
      (fun t : 𝕜 ↦ exp (t • -D) (exp (t • D) x * exp (t • D) y)) 0 t := by
    simpa using (hasDerivAt_exp_smul_const (-D) t).clm_apply (hg t)
  have h := is_const_of_deriv_eq_zero (fun t ↦ (hF t).differentiableAt) (fun t ↦ (hF t).deriv)
    1 0
  simp only [one_smul, zero_smul, exp_zero, one_apply_eq_self] at h
  -- Apply `exp D`, the inverse of `exp (-D)`.
  have hball (T : B →L[𝕜] B) : T ∈ Metric.eball 0 (expSeries 𝕜 (B →L[𝕜] B)).radius :=
    (expSeries_radius_eq_top 𝕜 (B →L[𝕜] B)).symm ▸ edist_lt_top _ _
  rw [← h, ← mul_apply_eq_comp, ← exp_add_of_commute_of_mem_ball (Commute.refl D).neg_right
    (hball _) (hball _), add_neg_cancel, exp_zero, one_apply_eq_self]

end ContinuousLinearMap
