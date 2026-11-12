/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Analysis.Calculus.ContinuousLinearMapInverse
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Jacobi operator equations and their logarithmic derivative

For operator curves satisfying `J' = V` and `V' = -K ∘ J`, the logarithmic derivative
`V ∘ J⁻¹` satisfies the Riccati equation wherever `J` is invertible. If `K` is symmetric,
the mutual Wronskian is constant; when it vanishes at an initial point this makes
`V ∘ J⁻¹` symmetric. The Wronskian statements apply on arbitrary convex parameter sets,
including closed intervals, without finite dimensionality or completeness.

The Riccati identity holds over any nontrivially normed field. The Wronskian and symmetry
statements use a real inner product space. Applying them to geodesic variations
requires a parallel trivialization identifying the curvature and ordinary operator equations.
The native covariant Jacobi-field Wronskian is in
`TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic`.

## Main results

* `TauCeti.hasDerivAt_jacobi_logDeriv`: the operator Riccati equation.
* `TauCeti.hasDerivWithinAt_jacobi_wronskian`: the Wronskian has zero derivative.
* `TauCeti.jacobi_wronskian_eq`: conservation of the mutual Wronskian.
* `TauCeti.jacobi_wronskian_eq_zero`: initial vanishing on a convex set gives zero Wronskian.
* `TauCeti.isSymmetric_jacobi_logDeriv`: symmetry before singularity.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Theorem 11.4.
* Public formalization references:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace TauCeti

section Normed

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]

/-- The logarithmic derivative of a nonsingular Jacobi operator satisfies
the Riccati equation, with the curvature sign inherited from `J'' = -K J`. -/
theorem hasDerivAt_jacobi_logDeriv
    {J V : 𝕜 → E →L[𝕜] E} {K : E →L[𝕜] E} {t : 𝕜}
    (hJ : HasDerivAt J (V t) t)
    (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hinv : (J t).IsInvertible) :
    HasDerivAt (fun s ↦ (V s).comp (J s).inverse)
      (-(((V t).comp (J t).inverse).comp ((V t).comp (J t).inverse)) - K) t := by
  have hcancel := hinv.self_apply_inverse
  have hdi := hJ.clm_inverse_of_completeSpace hinv
  convert hV.clm_comp hdi using 1
  ext x
  simp only [add_apply, sub_apply,
    neg_apply, ContinuousLinearMap.comp_apply, map_neg,
    hcancel]
  abel

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Wronskian of two columns of a Jacobi operator has zero derivative within its
parameter set. -/
theorem hasDerivWithinAt_jacobi_wronskian
    {J V : ℝ → E →L[ℝ] E} {K : E →L[ℝ] E} {s : Set ℝ} {t : ℝ}
    (hJ : HasDerivWithinAt J (V t) s t)
    (hV : HasDerivWithinAt V (-(K.comp (J t))) s t)
    (hK : LinearMap.IsSymmetric K.toLinearMap) (u v : E) :
    HasDerivWithinAt (fun s ↦ inner ℝ (J s u) (V s v) - inner ℝ (V s u) (J s v))
      0 s t := by
  have hJu : HasDerivWithinAt (fun s ↦ J s u) (V t u) s t := by
    simpa using hJ.clm_apply (hasDerivWithinAt_const t s u)
  have hJv : HasDerivWithinAt (fun s ↦ J s v) (V t v) s t := by
    simpa using hJ.clm_apply (hasDerivWithinAt_const t s v)
  have hVu : HasDerivWithinAt (fun s ↦ V s u) (-K (J t u)) s t := by
    simpa using hV.clm_apply (hasDerivWithinAt_const t s u)
  have hVv : HasDerivWithinAt (fun s ↦ V s v) (-K (J t v)) s t := by
    simpa using hV.clm_apply (hasDerivWithinAt_const t s v)
  have hz : (inner ℝ (J t u) (-K (J t v)) + inner ℝ (V t u) (V t v)) -
      (inner ℝ (V t u) (V t v) + inner ℝ (-K (J t u)) (J t v)) = 0 := by
    have hk : inner ℝ (K (J t u)) (J t v) = inner ℝ (J t u) (K (J t v)) :=
      hK (J t u) (J t v)
    rw [inner_neg_left, inner_neg_right, hk]
    ring
  exact hz ▸ HasDerivWithinAt.sub (hJu.inner ℝ hVv) (hVu.inner ℝ hJv)

/-- The mutual Wronskian of a Jacobi operator is constant on a convex parameter set. -/
theorem jacobi_wronskian_eq
    {J V K : ℝ → E →L[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hJ : ∀ r ∈ s, HasDerivWithinAt J (V r) s r)
    (hV : ∀ r ∈ s, HasDerivWithinAt V (-((K r).comp (J r))) s r)
    (hK : ∀ r ∈ s, LinearMap.IsSymmetric (K r).toLinearMap)
    (hs : Convex ℝ s) (ha : a ∈ s) (ht : t ∈ s) (u v : E) :
    inner ℝ (J t u) (V t v) - inner ℝ (V t u) (J t v) =
      inner ℝ (J a u) (V a v) - inner ℝ (V a u) (J a v) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr ↦ hasDerivWithinAt_jacobi_wronskian (hJ r hr) (hV r hr)
      (hK r hr) u v)
    (C := 0) (fun _ _ ↦ by simp) hs ha ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh

/-- Jacobi fields vanishing initially have vanishing mutual Wronskian. -/
theorem jacobi_wronskian_eq_zero
    {J V K : ℝ → E →L[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hJ : ∀ r ∈ s, HasDerivWithinAt J (V r) s r)
    (hV : ∀ r ∈ s, HasDerivWithinAt V (-((K r).comp (J r))) s r)
    (hK : ∀ r ∈ s, LinearMap.IsSymmetric (K r).toLinearMap)
    (hs : Convex ℝ s) (ha : a ∈ s) (hzero : J a = 0) (ht : t ∈ s) (u v : E) :
    inner ℝ (J t u) (V t v) - inner ℝ (V t u) (J t v) = 0 := by
  simpa only [hzero, zero_apply, inner_zero_left, inner_zero_right, sub_self]
    using jacobi_wronskian_eq hJ hV hK hs ha ht u v

/-- Before singularity, a Jacobi operator with initially vanishing Wronskian has symmetric
logarithmic derivative. -/
theorem isSymmetric_jacobi_logDeriv
    {J V K : ℝ → E →L[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hJ : ∀ r ∈ s, HasDerivWithinAt J (V r) s r)
    (hV : ∀ r ∈ s, HasDerivWithinAt V (-((K r).comp (J r))) s r)
    (hK : ∀ r ∈ s, LinearMap.IsSymmetric (K r).toLinearMap)
    (hs : Convex ℝ s) (ha : a ∈ s)
    (hW : ∀ u v, inner ℝ (J a u) (V a v) - inner ℝ (V a u) (J a v) = 0)
    (ht : t ∈ s) (hinv : (J t).IsInvertible) :
    LinearMap.IsSymmetric ((V t).comp (J t).inverse).toLinearMap := by
  intro x y
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply]
  have hw := jacobi_wronskian_eq hJ hV hK hs ha ht
    ((J t).inverse x) ((J t).inverse y)
  rw [hW] at hw
  simpa only [hinv.self_apply_inverse] using (sub_eq_zero.mp hw).symm

end InnerProduct

end TauCeti
