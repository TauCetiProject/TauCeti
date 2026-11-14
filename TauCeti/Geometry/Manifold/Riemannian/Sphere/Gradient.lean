/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Gradients of restricted ambient functions and height functions on the round sphere

For a real-valued function `F : E → ℝ` differentiable at `p ∈ Sⁿ`, its restriction `F ∘ (↑)` to the
unit sphere differentiates along a tangent vector `v` as `⟪∇ F p, v⟫`, with `v` read in `E` through
the differential of the inclusion. Consequently, its round gradient read in `E` is the tangential
projection `∇ F p - ⟪∇ F p, p⟫ p` of the Euclidean gradient `∇ F p`, with squared norm
`‖∇ F p‖² - ⟪∇ F p, p⟫²`.

Specialising to the linear height function `p ↦ ⟪a, p⟫` (`a ∈ E`) recovers the formulas without
completeness hypotheses on `E`: its round gradient read in `E` is `a - ⟪a, p⟫ p`, of squared length
`‖a‖² - ⟪a, p⟫²`.

## Main results

* `TauCeti.mvfderiv_comp_coe_sphere`: the differential of `F ∘ (↑)` on `Sⁿ` pairs `∇ F p` with the
  pushforward tangent vector.
* `TauCeti.mvfderiv_coe_mgradient_comp_coe_sphere`: the round gradient of `F ∘ (↑)`, read in `E`,
  is `∇ F p - ⟪∇ F p, p⟫ p`.
* `TauCeti.norm_mgradient_comp_coe_sphere_sq`: its squared round norm is
  `‖∇ F p‖² - ⟪∇ F p, p⟫²`.
* `TauCeti.mvfderiv_inner_coe_sphere`, `TauCeti.mvfderiv_coe_mgradient_inner_coe_sphere`,
  `TauCeti.norm_mgradient_inner_coe_sphere_sq`: the height-function specialisations `p ↦ ⟪a, p⟫`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (gradients for an induced metric).
-/

public section

open Bundle InnerProductSpace Metric Module
open scoped ContDiff Gradient Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The differential of the restriction `F ∘ (↑)` of a differentiable ambient function `F : E → ℝ`
to the unit sphere sends a tangent vector `v` at `p` to `⟪∇ F p, v⟫`, with `v` read in `E`. -/
theorem mvfderiv_comp_coe_sphere [CompleteSpace E] {F : E → ℝ} {p : sphere (0 : E) 1}
    (hF : DifferentiableAt ℝ F p) (v : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p v =
      inner ℝ (∇ F p) (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v) := by
  rw [mvfderiv_comp_apply_of_differentiableAt hF
    ((contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero), inner_gradient_left]

/-- **The round gradient of a restricted ambient function.** Read in `E`, the round gradient at `p`
of `F ∘ (↑)` is the orthogonal projection `∇ F p - ⟪∇ F p, p⟫ p` of the Euclidean gradient onto the
tangent hyperplane `(ℝ ∙ p)ᗮ`. -/
theorem mvfderiv_coe_mgradient_comp_coe_sphere [CompleteSpace E] {F : E → ℝ}
    {p : sphere (0 : E) 1} (hF : DifferentiableAt ℝ F p) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p
        (Manifold.mgradient (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p) =
      ∇ F p - inner ℝ (∇ F p) (p : E) • (p : E) := by
  have hp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have ht : ∇ F p - inner ℝ (∇ F p) (p : E) • (p : E) ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, hp, real_inner_comm]
    ring
  let u : TangentSpace (𝓡 n) p := (sphereTangentEquiv p).symm ⟨_, ht⟩
  have hu : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p u =
      ∇ F p - inner ℝ (∇ F p) (p : E) • (p : E) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← coe_sphereTangentEquiv_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hgrad : Manifold.mgradient (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p = u := by
    refine (Manifold.eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [inner_tangentSpace_sphere, hu, mvfderiv_comp_coe_sphere hF, inner_sub_left,
      real_inner_smul_left, inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, sub_zero]
  rw [hgrad, hu]

/-- **Squared norm of the round gradient of a restricted ambient function.** At `p ∈ Sⁿ`,
`‖grad_{Sⁿ}(F|_{Sⁿ})(p)‖² = ‖∇ F p‖² - ⟪∇ F p, p⟫²`. -/
theorem norm_mgradient_comp_coe_sphere_sq [CompleteSpace E] {F : E → ℝ} {p : sphere (0 : E) 1}
    (hF : DifferentiableAt ℝ F p) :
    ‖Manifold.mgradient (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p‖ ^ 2 =
      ‖∇ F p‖ ^ 2 - inner ℝ (∇ F p) (p : E) ^ 2 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_mgradient_comp_coe_sphere hF, norm_sub_sq_real,
    norm_smul, norm_eq_of_mem_sphere p, real_inner_smul_right, Real.norm_eq_abs, mul_one, sq_abs]
  ring

/-- The differential of the height function `p ↦ ⟪a, p⟫` on the unit sphere sends a tangent vector
`v` to `⟪a, v⟫`, with `v` read in `E` through the differential of the inclusion. -/
theorem mvfderiv_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) (v : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p v =
      inner ℝ a (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v) := by
  have h : (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) =
      innerSL ℝ a ∘ ((↑) : sphere (0 : E) 1 → E) :=
    funext fun q ↦ (innerSL_apply_apply ℝ a (q : E)).symm
  rw [h, (innerSL ℝ a).mvfderiv_comp_apply
    ((contMDiff_coe_sphere (m := 1) p).mdifferentiableAt one_ne_zero), innerSL_apply_apply]

/-- **The round gradient of a height function.** Read in `E`, the gradient at `p` of the height
function `q ↦ ⟪a, q⟫` for the round metric is the tangential part `a - ⟪a, p⟫ p` of `a`. -/
theorem mvfderiv_coe_mgradient_inner_coe_sphere (a : E) (p : sphere (0 : E) 1) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p
        (Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p) =
      a - inner ℝ a (p : E) • (p : E) := by
  have hp : inner ℝ (p : E) (p : E) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have ht : a - inner ℝ a (p : E) • (p : E) ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right,
      real_inner_smul_right, hp, real_inner_comm]
    ring
  -- The tangent vector whose image in `E` is the tangential part of `a`.
  let u : TangentSpace (𝓡 n) p := (sphereTangentEquiv p).symm ⟨_, ht⟩
  have hu : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p u =
      a - inner ℝ a (p : E) • (p : E) := by
    rw [mvfderiv_apply_eq_mfderiv_apply, ← coe_sphereTangentEquiv_apply,
      LinearIsometryEquiv.apply_symm_apply]
  have hgrad : Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p = u := by
    refine (Manifold.eq_mgradient_iff.2 fun v ↦ ?_).symm
    rw [inner_tangentSpace_sphere, hu, mvfderiv_inner_coe_sphere, inner_sub_left,
      real_inner_smul_left, inner_coe_mvfderiv_subtypeVal_sphere, mul_zero, sub_zero]
  rw [hgrad, hu]

/-- **The length of the round gradient of a height function.** The squared length at `p` of the
round gradient of `q ↦ ⟪a, q⟫` is `‖a‖² - ⟪a, p⟫²`. -/
theorem norm_mgradient_inner_coe_sphere_sq (a : E) (p : sphere (0 : E) 1) :
    ‖Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p‖ ^ 2 =
      ‖a‖ ^ 2 - inner ℝ a (p : E) ^ 2 := by
  rw [norm_tangentSpace_sphere, mvfderiv_coe_mgradient_inner_coe_sphere, norm_sub_sq_real,
    norm_smul, norm_eq_of_mem_sphere p, real_inner_smul_right, Real.norm_eq_abs, mul_one, sq_abs]
  ring

end TauCeti
