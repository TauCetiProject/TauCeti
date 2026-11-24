/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.Unitary
public import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Star

/-!
# Derivatives of unitary families at the identity

If a family `f` of elements of a normed star algebra is unitary near `x` and `f x = 1`, then
differentiating `f y * star (f y) = 1` shows that every derivative of `f` at `x` is skew-adjoint:
`star (df(x) v) = -df(x) v` (`TauCeti.star_fderiv_apply_eq_neg_of_mem_unitary`). So the tangent
vectors of the unitary group at the identity are skew-adjoint.
-/

public section

open scoped Topology

namespace TauCeti

variable {𝕜 E 𝔸 : Type*} [NontriviallyNormedField 𝕜] [StarRing 𝕜] [TrivialStar 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedRing 𝔸] [NormedAlgebra 𝕜 𝔸] [StarRing 𝔸]
  [StarModule 𝕜 𝔸] [ContinuousStar 𝔸]

/-- **Derivatives of a unitary family at the identity are skew-adjoint.** If `f y` is unitary for
all `y` near `x` and `f x = 1`, then `star (df(x) v) = -df(x) v` for every `v`. No
differentiability is needed: where `f` is not differentiable its derivative is zero. -/
theorem star_fderiv_apply_eq_neg_of_mem_unitary {f : E → 𝔸} {x : E}
    (h : ∀ᶠ y in 𝓝 x, f y ∈ unitary 𝔸) (hx : f x = 1) (v : E) :
    star (fderiv 𝕜 f x v) = -fderiv 𝕜 f x v := by
  by_cases hf : DifferentiableAt 𝕜 f x
  · -- The product `f * star f` has derivative `df + star df` at `x` by the product rule, and `0`
    -- since it is locally constant.
    have hprod := hf.hasFDerivAt.mul' hf.hasFDerivAt.star
    have hc : HasFDerivAt (fun y ↦ f y * star (f y)) (0 : E →L[𝕜] 𝔸) x :=
      (hasFDerivAt_const (1 : 𝔸) x).congr_of_eventuallyEq
        (h.mono fun y hy ↦ Unitary.mul_star_self_of_mem hy)
    have hv := congrArg (fun L : E →L[𝕜] 𝔸 ↦ L v) (hprod.unique hc)
    simp only [hx, star_one] at hv
    simpa [eq_neg_iff_add_eq_zero, add_comm] using hv
  · simp [fderiv_zero_of_not_differentiableAt hf]

end TauCeti
