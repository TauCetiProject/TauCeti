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
the Wronskian of two independent vector solutions is constant; initial vanishing makes
`V ∘ J⁻¹` symmetric. The Wronskian statements apply on arbitrary convex parameter sets,
including closed intervals, without finite dimensionality or completeness.

The Riccati identity holds over any nontrivially normed field. The Wronskian and symmetry
statements use a real inner product space. Applying them to geodesic variations
requires a parallel trivialization identifying the curvature and ordinary operator equations.
The native covariant Jacobi-field Wronskian is in
`TauCeti.Geometry.Manifold.Riemannian.Jacobi.Basic`.

## Main results

* `TauCeti.hasDerivWithinAt_jacobi_logDeriv`, `TauCeti.hasDerivAt_jacobi_logDeriv`: the
  operator Riccati equation, also within closed intervals.
* `TauCeti.hasDerivWithinAt_jacobi_wronskian`: the Wronskian has zero derivative.
* `TauCeti.jacobi_wronskian_eq`: conservation of the mutual Wronskian.
* `TauCeti.jacobi_wronskian_eq_zero`: initial vanishing on a convex set gives zero Wronskian.
* `TauCeti.isSymmetric_comp_inverse_of_inner_eq`: pointwise algebraic symmetry.
* `TauCeti.isSymmetric_jacobi_logDeriv`: symmetry from Jacobi equations and initial data.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Theorem 11.4.
* Public formalization references:
  [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions) and
  [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

namespace TauCeti

section Normed

open ContinuousLinearMap

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]

/-- The logarithmic derivative of an invertible Jacobi operator satisfies the Riccati
identity within a parameter set, including at its endpoints. -/
theorem hasDerivWithinAt_jacobi_logDeriv
    {J V : 𝕜 → F →L[𝕜] E} {K : E →L[𝕜] E} {s : Set 𝕜} {t : 𝕜}
    (hJ : HasDerivWithinAt J (V t) s t)
    (hV : HasDerivWithinAt V (-(K.comp (J t))) s t)
    (hinv : (J t).IsInvertible) :
    HasDerivWithinAt (fun r ↦ (V r).comp (J r).inverse)
      (-(((V t).comp (J t).inverse).comp ((V t).comp (J t).inverse)) - K) s t := by
  have hcancel := hinv.self_apply_inverse
  have hdi' := (hasFDerivAt_id (𝕜 := 𝕜) (J t)).clm_inverse_of_completeSpace hinv
  have hdi := hdi'.comp_hasDerivWithinAt t hJ
  convert! hV.clm_comp hdi using 1
  ext x
  simp [hcancel, ContinuousLinearMap.comp_assoc]
  abel

/-- The logarithmic derivative of an invertible Jacobi operator satisfies the Riccati
identity at an interior parameter value. -/
theorem hasDerivAt_jacobi_logDeriv
    {J V : 𝕜 → F →L[𝕜] E} {K : E →L[𝕜] E} {t : 𝕜}
    (hJ : HasDerivAt J (V t) t) (hV : HasDerivAt V (-(K.comp (J t))) t)
    (hinv : (J t).IsInvertible) :
    HasDerivAt (fun r ↦ (V r).comp (J r).inverse)
      (-(((V t).comp (J t).inverse).comp ((V t).comp (J t).inverse)) - K) t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_jacobi_logDeriv
    hJ.hasDerivWithinAt hV.hasDerivWithinAt hinv)

end Normed

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two vector solutions of a symmetric Jacobi equation have zero Wronskian derivative
within their parameter set. The coefficient need only be a linear map at this point. -/
theorem hasDerivWithinAt_jacobi_wronskian
    {X₁ V₁ X₂ V₂ : ℝ → E} {K : E →ₗ[ℝ] E} {s : Set ℝ} {t : ℝ}
    (hX₁ : HasDerivWithinAt X₁ (V₁ t) s t)
    (hV₁ : HasDerivWithinAt V₁ (-K (X₁ t)) s t)
    (hX₂ : HasDerivWithinAt X₂ (V₂ t) s t)
    (hV₂ : HasDerivWithinAt V₂ (-K (X₂ t)) s t)
    (hK : K.IsSymmetric) :
    HasDerivWithinAt (fun r ↦ inner ℝ (X₁ r) (V₂ r) - inner ℝ (V₁ r) (X₂ r)) 0 s t := by
  have hz : (inner ℝ (X₁ t) (-K (X₂ t)) + inner ℝ (V₁ t) (V₂ t)) -
      (inner ℝ (V₁ t) (V₂ t) + inner ℝ (-K (X₁ t)) (X₂ t)) = 0 := by
    rw [inner_neg_left, inner_neg_right, hK (X₁ t) (X₂ t)]
    ring
  exact hz ▸ HasDerivWithinAt.sub (hX₁.inner ℝ hV₂) (hV₁.inner ℝ hX₂)

/-- The Wronskian of two vector solutions of a symmetric Jacobi equation has zero derivative. -/
theorem hasDerivAt_jacobi_wronskian
    {X₁ V₁ X₂ V₂ : ℝ → E} {K : E →ₗ[ℝ] E} {t : ℝ}
    (hX₁ : HasDerivAt X₁ (V₁ t) t) (hV₁ : HasDerivAt V₁ (-K (X₁ t)) t)
    (hX₂ : HasDerivAt X₂ (V₂ t) t) (hV₂ : HasDerivAt V₂ (-K (X₂ t)) t)
    (hK : K.IsSymmetric) :
    HasDerivAt (fun r ↦ inner ℝ (X₁ r) (V₂ r) - inner ℝ (V₁ r) (X₂ r)) 0 t :=
  hasDerivWithinAt_univ.mp (hasDerivWithinAt_jacobi_wronskian
    hX₁.hasDerivWithinAt hV₁.hasDerivWithinAt hX₂.hasDerivWithinAt hV₂.hasDerivWithinAt hK)

/-- The Wronskian of two independent vector solutions is constant on a convex parameter set. -/
theorem jacobi_wronskian_eq
    {X₁ V₁ X₂ V₂ : ℝ → E} {K : ℝ → E →ₗ[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hX₁ : ∀ r ∈ s, HasDerivWithinAt X₁ (V₁ r) s r)
    (hV₁ : ∀ r ∈ s, HasDerivWithinAt V₁ (-(K r) (X₁ r)) s r)
    (hX₂ : ∀ r ∈ s, HasDerivWithinAt X₂ (V₂ r) s r)
    (hV₂ : ∀ r ∈ s, HasDerivWithinAt V₂ (-(K r) (X₂ r)) s r)
    (hK : ∀ r ∈ s, (K r).IsSymmetric)
    (hs : Convex ℝ s) (ha : a ∈ s) (ht : t ∈ s) :
    inner ℝ (X₁ t) (V₂ t) - inner ℝ (V₁ t) (X₂ t) =
      inner ℝ (X₁ a) (V₂ a) - inner ℝ (V₁ a) (X₂ a) := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun r hr ↦ hasDerivWithinAt_jacobi_wronskian
      (hX₁ r hr) (hV₁ r hr) (hX₂ r hr) (hV₂ r hr) (hK r hr))
    (C := 0) (fun _ _ ↦ by simp) hs ha ht
  simpa only [zero_mul, norm_le_zero_iff, sub_eq_zero] using hh

/-- Two initially vanishing Jacobi solutions have zero Wronskian on their convex parameter set. -/
theorem jacobi_wronskian_eq_zero
    {X₁ V₁ X₂ V₂ : ℝ → E} {K : ℝ → E →ₗ[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hX₁ : ∀ r ∈ s, HasDerivWithinAt X₁ (V₁ r) s r)
    (hV₁ : ∀ r ∈ s, HasDerivWithinAt V₁ (-(K r) (X₁ r)) s r)
    (hX₂ : ∀ r ∈ s, HasDerivWithinAt X₂ (V₂ r) s r)
    (hV₂ : ∀ r ∈ s, HasDerivWithinAt V₂ (-(K r) (X₂ r)) s r)
    (hK : ∀ r ∈ s, (K r).IsSymmetric)
    (hs : Convex ℝ s) (ha : a ∈ s) (hzero₁ : X₁ a = 0) (hzero₂ : X₂ a = 0)
    (ht : t ∈ s) : inner ℝ (X₁ t) (V₂ t) - inner ℝ (V₁ t) (X₂ t) = 0 := by
  simpa only [hzero₁, hzero₂, inner_zero_left, inner_zero_right, sub_self]
    using jacobi_wronskian_eq hX₁ hV₁ hX₂ hV₂ hK hs ha ht

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A vanishing mutual Wronskian makes `V ∘ J⁻¹` symmetric. This also holds for a singular
`J`, since the totalized inverse is then zero. The parameter space needs no inner product. -/
theorem isSymmetric_comp_inverse_of_inner_eq {J V : F →L[ℝ] E}
    (hW : ∀ u v, inner ℝ (J u) (V v) = inner ℝ (V u) (J v)) :
    LinearMap.IsSymmetric (V.comp J.inverse).toLinearMap := by
  by_cases hinv : J.IsInvertible
  · intro x y
    simpa only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
      hinv.self_apply_inverse] using (hW (J.inverse x) (J.inverse y)).symm
  · simp [ContinuousLinearMap.inverse_of_not_isInvertible hinv,
      LinearMap.IsSymmetric]

/-- A Jacobi operator with initially vanishing mutual Wronskian has symmetric logarithmic
derivative, using the totalized inverse also at singular parameters. -/
theorem isSymmetric_jacobi_logDeriv
    {J V : ℝ → F →L[ℝ] E} {K : ℝ → E →L[ℝ] E} {s : Set ℝ} {a t : ℝ}
    (hJ : ∀ r ∈ s, HasDerivWithinAt J (V r) s r)
    (hV : ∀ r ∈ s, HasDerivWithinAt V (-((K r).comp (J r))) s r)
    (hK : ∀ r ∈ s, LinearMap.IsSymmetric (K r).toLinearMap)
    (hs : Convex ℝ s) (ha : a ∈ s)
    (hW : ∀ u v, inner ℝ (J a u) (V a v) = inner ℝ (V a u) (J a v))
    (ht : t ∈ s) : LinearMap.IsSymmetric ((V t).comp (J t).inverse).toLinearMap := by
  apply isSymmetric_comp_inverse_of_inner_eq
  intro u v
  have hJu (r : ℝ) (hr : r ∈ s) (w : F) :
      HasDerivWithinAt (fun r ↦ J r w) (V r w) s r := by
    simpa using (hJ r hr).clm_apply (hasDerivWithinAt_const r s w)
  have hVu (r : ℝ) (hr : r ∈ s) (w : F) :
      HasDerivWithinAt (fun r ↦ V r w) (-(K r) (J r w)) s r := by
    simpa using (hV r hr).clm_apply (hasDerivWithinAt_const r s w)
  have hw := jacobi_wronskian_eq (K := fun r ↦ (K r).toLinearMap)
    (hJu · · u) (hVu · · u) (hJu · · v) (hVu · · v)
    hK hs ha ht
  rw [hW, sub_self] at hw
  exact sub_eq_zero.mp hw

end InnerProduct

end TauCeti
