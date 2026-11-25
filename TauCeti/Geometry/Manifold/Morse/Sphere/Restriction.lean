/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Morse.Hessian
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Critical points of functions restricted to the unit sphere

Let `F : E → ℝ` be a function on a real inner product space of dimension `n + 1`, and let
`f = F ∘ (↑)` be its restriction to the unit sphere `Sⁿ`. The tangent space of `Sⁿ` at `p`, read
in `E` through the differential `ι` of the inclusion, is the hyperplane `pᗮ`
(`range_mvfderiv_subtypeVal`). This file gives the method of Lagrange multipliers for `f`.

* **Critical points.** `p` is a critical point of `f` exactly when the derivative of `F` at `p`
  vanishes on `pᗮ` (`TauCeti.mem_criticalPoints_comp_coe_sphere_iff`). If that derivative is the
  inner product with a vector `g`, for instance the gradient of `F`, this says that `g` is a
  multiple of `p` (`TauCeti.mem_criticalPoints_comp_coe_sphere_iff_mem_span`); the factor is the
  Lagrange multiplier `μ = DF(p) p`.
* **The Hessian.** At a critical point `p` of `f`, with `F` twice continuously differentiable at
  `p`, the critical Hessian of `f` is the second derivative of `F` corrected by the Lagrange
  multiplier:
  `Hess f(p)(v, w) = D²F(p)(ι v, ι w) - μ ⟪ι v, ι w⟫`
  (`TauCeti.criticalHessian_comp_coe_sphere_apply`).

The Hessian formula is proved without computing the second derivative of a chart of the sphere.
The function `G = F - (μ / 2) (‖·‖² - 1)` agrees with `F` on the sphere, and its derivative at `p`
vanishes, because the derivative of `F` there is `μ ⟪p, ·⟫`. So `p` is a critical point of `G` on
`E`, and the second-order chain rule at a critical point (`TauCeti.criticalHessian_comp_apply`)
computes the critical Hessian of `G ∘ (↑) = f` from the second derivative of `G`, which is
`D²F(p) - μ ⟪·, ·⟫`.

These formulas give the nondegeneracy and the Morse index of the critical points of functions on
the sphere which are restrictions of explicit functions on `E`, such as quadratic forms or
polynomials in the coordinates.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  §6 (the Hessian of a function restricted to a submanifold at a critical point).
-/

public section

open Function Metric Module Set
open scoped ContDiff InnerProductSpace Manifold RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)] {F : E → ℝ} {p : sphere (0 : E) 1}

/-- **Critical points on the sphere.** A point `p` of the sphere is a critical point of the
restriction of `F` exactly when the derivative of `F` at `p` vanishes on the tangent hyperplane
`pᗮ`. -/
theorem mem_criticalPoints_comp_coe_sphere_iff (hF : DifferentiableAt ℝ F p) :
    p ∈ criticalPoints (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) ↔
      ∀ w ∈ (ℝ ∙ (p : E))ᗮ, fderiv ℝ F p w = 0 := by
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) p :=
    (contMDiff_coe_sphere (E := E) (m := 1) (n := n) p).mdifferentiableAt one_ne_zero
  -- The differential of `F ∘ (↑)` is `DF(p) ∘ ι`, and the range of `ι` is `pᗮ`.
  have hd : mvfderiv (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p =
      (fderiv ℝ F p).comp (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p) := by
    ext u
    exact mvfderiv_comp_apply_of_differentiableAt hF hcoe u
  rw [mem_criticalPoints, hd, ← range_mvfderiv_subtypeVal (n := n) p]
  constructor
  · rintro h _ ⟨u, rfl⟩
    exact congr($h u)
  · intro h
    ext u
    exact h _ ⟨u, rfl⟩

/-- **Lagrange multipliers on the sphere.** If the derivative of `F` at a point `p` of the sphere is
the inner product with `g`, then `p` is a critical point of the restriction of `F` exactly when `g`
is a multiple of `p`. -/
theorem mem_criticalPoints_comp_coe_sphere_iff_mem_span {g : E}
    (hF : HasFDerivAt F (innerSL ℝ g) (p : E)) :
    p ∈ criticalPoints (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) ↔ g ∈ ℝ ∙ (p : E) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  rw [mem_criticalPoints_comp_coe_sphere_iff hF.differentiableAt, hF.fderiv,
    ← Submodule.orthogonal_orthogonal (ℝ ∙ (p : E)), Submodule.mem_orthogonal']
  simp

/-- At a critical point `p` of the restriction of `F` to the sphere, the derivative of `F` is the
Lagrange multiplier `DF(p) p` times the inner product with `p`. -/
theorem fderiv_apply_eq_mul_inner_of_mem_criticalPoints_comp_coe_sphere
    (hF : DifferentiableAt ℝ F p)
    (hcrit : p ∈ criticalPoints (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E))) (w : E) :
    fderiv ℝ F p w = fderiv ℝ F p p * ⟪(p : E), w⟫ := by
  -- The component `w - ⟪p, w⟫ p` of `w` is tangent, so `F` has zero derivative along it.
  have hperp : w - ⟪(p : E), w⟫ • (p : E) ∈ (ℝ ∙ (p : E))ᗮ := by
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_sub_right, inner_smul_right,
      real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere]
    ring
  have h := (mem_criticalPoints_comp_coe_sphere_iff hF).1 hcrit _ hperp
  rw [map_sub, map_smul, smul_eq_mul, sub_eq_zero] at h
  rw [h, mul_comm]

/-- **The Hessian on the sphere.** At a critical point `p` of the restriction `f` of `F` to the
sphere, with `F` twice continuously differentiable at `p`, the critical Hessian of `f` is
`D²F(p)(ι v, ι w) - μ ⟪ι v, ι w⟫`, where `ι` is the differential of the inclusion and
`μ = DF(p) p` is the Lagrange multiplier. -/
theorem criticalHessian_comp_coe_sphere_apply (hF : ContDiffAt ℝ 2 F p)
    (hcrit : p ∈ criticalPoints (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)))
    (v w : TangentSpace (𝓡 n) p) :
    criticalHessian (𝓡 n) (F ∘ ((↑) : sphere (0 : E) 1 → E)) p v w =
      fderiv ℝ (fderiv ℝ F) p (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v)
          (mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w) -
        fderiv ℝ F p p * ⟪mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p v,
          mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w⟫ := by
  set μ := fderiv ℝ F p p
  have hF1 : DifferentiableAt ℝ F p := hF.differentiableAt (by norm_num)
  -- `G = F - (μ / 2) (‖·‖² - 1)` agrees with `F` on the sphere and is critical at `p` in `E`.
  set G : E → ℝ := fun x ↦ F x - μ / 2 * (‖x‖ ^ 2 - 1)
  have hGF : G ∘ ((↑) : sphere (0 : E) 1 → E) = F ∘ (↑) := by
    funext x
    simp [G, norm_eq_of_mem_sphere]
  have hGC : ContDiffAt ℝ 2 G p :=
    hF.sub (contDiffAt_const.mul (((contDiff_norm_sq ℝ).sub contDiff_const).contDiffAt))
  have hG0 : fderiv ℝ G p = 0 := by
    have hN : HasFDerivAt (fun x : E ↦ ‖x‖ ^ 2 - 1) (2 • innerSL ℝ (p : E)) p :=
      (hasStrictFDerivAt_norm_sq _).hasFDerivAt.sub_const 1
    have hGd : HasFDerivAt G (fderiv ℝ F p - (μ / 2) • 2 • innerSL ℝ (p : E)) p :=
      hF1.hasFDerivAt.sub (hN.const_mul (μ / 2))
    rw [hGd.fderiv]
    ext w
    simp only [sub_apply, smul_apply, smul_eq_mul,
      innerSL_apply_apply, zero_apply,
      fderiv_apply_eq_mul_inner_of_mem_criticalPoints_comp_coe_sphere hF1 hcrit w, μ]
    ring
  -- The second derivative of `G` at `p` is `D²F(p) - μ ⟪·, ·⟫`.
  have hN2 : DifferentiableAt ℝ (fderiv ℝ fun z : E ↦ ‖z‖ ^ 2) p :=
    ((contDiff_norm_sq ℝ (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiable
      one_ne_zero _
  have hD2 : ∀ a b, fderiv ℝ (fderiv ℝ G) p a b = fderiv ℝ (fderiv ℝ F) p a b - μ * ⟪a, b⟫ := by
    have hev : fderiv ℝ G =ᶠ[nhds (p : E)]
        fun x ↦ fderiv ℝ F x - (μ / 2) • fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2) x := by
      filter_upwards [(hF.eventually (by norm_num)).mono fun x hx ↦
        hx.differentiableAt (by norm_num)] with x hx
      have hN : HasFDerivAt (fun z : E ↦ ‖z‖ ^ 2 - 1) (fderiv ℝ (fun z : E ↦ ‖z‖ ^ 2) x) x :=
        ((contDiff_norm_sq ℝ (n := 1)).differentiable one_ne_zero x).hasFDerivAt.sub_const 1
      exact (hx.hasFDerivAt.sub (hN.const_mul (μ / 2))).fderiv
    intro a b
    rw [hev.fderiv_eq, fderiv_fun_sub ((hF.fderiv_right (m := 1) (by norm_num)).differentiableAt
      one_ne_zero) (hN2.fun_const_smul (μ / 2)), fderiv_fun_const_smul hN2]
    simp only [sub_apply, smul_apply, smul_eq_mul,
      fderiv_fderiv_norm_sq_apply]
    ring
  have key := criticalHessian_comp_apply (I := 𝓘(ℝ, E)) (I' := 𝓡 n)
    (φ := ((↑) : sphere (0 : E) 1 → E)) (f := G) rfl hGC.contMDiffAt
    (contMDiff_coe_sphere (E := E) (n := n) (m := 2) p)
    (mem_criticalPoints_iff_fderiv_eq_zero.2 hG0) v w
  rw [hGF, criticalHessian_modelSpace] at key
  rw [key, mvfderiv_apply_eq_mfderiv_apply, mvfderiv_apply_eq_mfderiv_apply]
  exact hD2 _ _

end TauCeti
