/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Gradient.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

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

These height gradients span every tangent space of the sphere; they are the vector fields from which
the curvature of the round sphere is computed, and the negative gradient flow of a height function
moves points along the meridians towards the south pole. Expanding in any finite orthonormal basis
of `E` expresses `(sphereTangentEquiv x).symm` as a linear combination of height gradients, giving
`C^m` regularity (for every `m : ℕ∞ω`, including `m = ω`) of orthogonal ambient lifts into the
tangent bundle.

## Main results

* `TauCeti.mvfderiv_comp_coe_sphere`: the differential of `F ∘ (↑)` on `Sⁿ` pairs `∇ F p` with the
  pushforward tangent vector.
* `TauCeti.mvfderiv_coe_mgradient_comp_coe_sphere`: the round gradient of `F ∘ (↑)`, read in `E`,
  is `∇ F p - ⟪∇ F p, p⟫ p`.
* `TauCeti.norm_mgradient_comp_coe_sphere_sq`: its squared round norm is
  `‖∇ F p‖² - ⟪∇ F p, p⟫²`.
* `TauCeti.mvfderiv_inner_coe_sphere`, `TauCeti.mvfderiv_coe_mgradient_inner_coe_sphere`,
  `TauCeti.norm_mgradient_inner_coe_sphere_sq`: the height-function specialisations `p ↦ ⟪a, p⟫`.
* `TauCeti.forall_mvfderiv_inner_coe_sphere_eq_zero_iff`: in positive dimension, the differential
  of the height function `p ↦ ⟪a, p⟫` vanishes identically only for `a = 0`.
* `TauCeti.sphereTangentEquiv_symm_eq_sum_mgradient`: `(sphereTangentEquiv x).symm w` expanded as a
  linear combination of round height gradients along any finite orthonormal basis of `E`.
* `TauCeti.contMDiff_sphereTangentEquiv_symm` and
  `TauCeti.contMDiff_section_sphereTangentEquiv_symm`: `C^m` regularity of lifting orthogonal
  ambient maps into `TangentBundle (𝓡 n) (sphere (0 : E) 1)`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (gradients for an induced metric).
-/

public section

open Bundle InnerProductSpace Metric Module
open scoped ContDiff Gradient InnerProductSpace Manifold

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
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  simpa only [Function.comp_def, coe_innerSL_apply, gradient_inner_const_left] using
    mvfderiv_coe_mgradient_comp_coe_sphere (n := n) (p := p) (innerSL ℝ a).differentiableAt

/-- **The length of the round gradient of a height function.** The squared length at `p` of the
round gradient of `q ↦ ⟪a, q⟫` is `‖a‖² - ⟪a, p⟫²`. -/
theorem norm_mgradient_inner_coe_sphere_sq (a : E) (p : sphere (0 : E) 1) :
    ‖Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) p‖ ^ 2 =
      ‖a‖ ^ 2 - inner ℝ a (p : E) ^ 2 := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : CompleteSpace E := FiniteDimensional.completeSpace ℝ E
  simpa only [Function.comp_def, coe_innerSL_apply, gradient_inner_const_left] using
    norm_mgradient_comp_coe_sphere_sq (n := n) (p := p) (innerSL ℝ a).differentiableAt

/-- In positive dimension, the differential of the height function `⟪a, ·⟫` vanishes everywhere on
the sphere only for `a = 0`: at a unit vector orthogonal to `a`, its round gradient has length
`‖a‖`. -/
theorem forall_mvfderiv_inner_coe_sphere_eq_zero_iff (hn : n ≠ 0) (a : E) :
    (∀ x, mvfderiv (𝓡 n) (fun q : sphere (0 : E) 1 ↦ inner ℝ a (q : E)) x = 0) ↔ a = 0 := by
  refine ⟨fun hd ↦ ?_, fun ha x ↦ ?_⟩
  · by_contra ha
    -- A unit vector `x` orthogonal to `a` exists since `dim E ≥ 2`.
    obtain ⟨e, he, horth⟩ := exists_norm_eq_one_forall_inner_eq_zero_of_card_lt_finrank (𝕜 := ℝ)
      ({a} : Finset E) (by simp [Fact.out (p := finrank ℝ E = n + 1)]; omega)
    let x : sphere (0 : E) 1 := ⟨e, by simpa using he⟩
    have hax : inner ℝ a (x : E) = 0 := horth a (by simp)
    have hx := norm_mgradient_inner_coe_sphere_sq (n := n) a x
    rw [Manifold.mgradient_eq_zero_iff.2 (hd x), norm_zero, hax] at hx
    exact ha (by simpa using hx.symm)
  · subst ha
    ext v
    rw [mvfderiv_inner_coe_sphere, inner_zero_left, zero_apply]

/-- Expanding `w ∈ (ℝ ∙ (x : E))ᗮ` in any finite orthonormal basis `b` of `E` expresses its
corresponding tangent vector `(sphereTangentEquiv x).symm w` as a linear combination of the round
gradients of the height functions `q ↦ ⟪b j, q⟫_ℝ`. -/
theorem sphereTangentEquiv_symm_eq_sum_mgradient {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) (x : sphere (0 : E) 1) (w : (ℝ ∙ (x : E))ᗮ) :
    (sphereTangentEquiv x).symm w =
      ∑ j : ι, ⟪b j, (w : E)⟫_ℝ •
        Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ ⟪b j, (q : E)⟫_ℝ) x := by
  apply injective_mvfderiv_subtypeVal_sphere x
  rw [mvfderiv_subtypeVal_sphere_eq_sphereTangentEquiv, LinearIsometryEquiv.apply_symm_apply,
    map_sum]
  have hwx : ⟪(w : E), (x : E)⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp w.property
  calc
    (w : E) = (∑ j : ι, ⟪b j, (w : E)⟫_ℝ • b j) -
        (∑ j : ι, ⟪(w : E), b j⟫_ℝ * ⟪b j, (x : E)⟫_ℝ) • (x : E) := by
      rw [b.sum_repr', b.sum_inner_mul_inner, hwx, zero_smul, sub_zero]
    _ = ∑ j : ι, (⟪b j, (w : E)⟫_ℝ • b j -
        (⟪b j, (w : E)⟫_ℝ * ⟪b j, (x : E)⟫_ℝ) • (x : E)) := by
      rw [Finset.sum_smul, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [real_inner_comm (w : E) (b j)]
    _ = ∑ j : ι, mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x
        (⟪b j, (w : E)⟫_ℝ •
          Manifold.mgradient (𝓡 n) (fun q : sphere (0 : E) 1 ↦ ⟪b j, (q : E)⟫_ℝ) x) := by
      refine Finset.sum_congr rfl fun j _ ↦ ?_
      rw [ContinuousLinearMap.map_smul, mvfderiv_coe_mgradient_inner_coe_sphere, smul_sub,
        smul_smul]

/-- Any `C^m` ambient map `u : M → E` orthogonal to a `C^m` base map `f : M → sphere (0 : E) 1`
lifts via `(sphereTangentEquiv (f ·)).symm` to a `C^m` map into the tangent bundle of the sphere,
for every `m : ℕ∞ω` (including `m = ω`). -/
theorem contMDiff_sphereTangentEquiv_symm {E' H' M : Type*}
    [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
    {J : ModelWithCorners ℝ E' H'} [TopologicalSpace M] [ChartedSpace H' M]
    {m : ℕ∞ω} {f : M → sphere (0 : E) 1} {u : M → E}
    (hf : ContMDiff J (𝓡 n) m f) (hu_diff : ContMDiff J 𝓘(ℝ, E) m u)
    (hu : ∀ z, u z ∈ (ℝ ∙ (f z : E))ᗮ) :
    ContMDiff J (𝓡 n).tangent m
      (fun z ↦ (⟨f z, (sphereTangentEquiv (f z)).symm ⟨u z, hu z⟩⟩ :
        TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have : IsManifold (𝓡 n) (ω + 1) (sphere (0 : E) 1) := by
    simpa only [show (ω : ℕ∞ω) + 1 = ω by simp] using
      (inferInstance : IsManifold (𝓡 n) ω (sphere (0 : E) 1))
  let b := stdOrthonormalBasis ℝ E
  have hgrad (j : Fin (finrank ℝ E)) :
      ContMDiff (𝓡 n) (𝓡 n).tangent m
        (fun q : sphere (0 : E) 1 ↦
          (⟨q, Manifold.mgradient (𝓡 n) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) q⟩ :
            TangentBundle (𝓡 n) (sphere (0 : E) 1))) := by
    have hh : ContMDiff (𝓡 n) 𝓘(ℝ) (ω + 1) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) :=
      ((innerSL ℝ (b j)).contDiff.contMDiff.comp
        (contMDiff_coe_sphere (E := E) (n := n) (m := ω))).of_le le_top
    exact (Manifold.contMDiff_mgradient (I := 𝓡 n) (n := ω) hh).of_le le_top
  have hsum := ContMDiff.sum_sectionAlong Finset.univ
    (fun j z ↦ ⟪b j, u z⟫_ℝ •
      Manifold.mgradient (𝓡 n) (fun r : sphere (0 : E) 1 ↦ ⟪b j, (r : E)⟫_ℝ) (f z)) hf
    fun j _ ↦ (((innerSL ℝ (b j)).contDiff.contMDiff.comp hu_diff).smul_totalSpace
      ((hgrad j).comp hf))
  exact hsum.congr fun z ↦
    congrArg (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) (f z))
      (sphereTangentEquiv_symm_eq_sum_mgradient (n := n) b (f z) ⟨u z, hu z⟩)

/-- A `C^m` ambient map `u : sphere (0 : E) 1 → E` satisfying `u x ∈ (ℝ ∙ (x : E))ᗮ` at every
point `x` defines a `C^m` tangent vector field on `sphere (0 : E) 1`. -/
theorem contMDiff_section_sphereTangentEquiv_symm {m : ℕ∞ω} {u : sphere (0 : E) 1 → E}
    (hu_diff : ContMDiff (𝓡 n) 𝓘(ℝ, E) m u)
    (hu : ∀ x : sphere (0 : E) 1, u x ∈ (ℝ ∙ (x : E))ᗮ) :
    ContMDiff (𝓡 n) (𝓡 n).tangent m
      (fun x : sphere (0 : E) 1 ↦
        (⟨x, (sphereTangentEquiv x).symm ⟨u x, hu x⟩⟩ :
          TangentBundle (𝓡 n) (sphere (0 : E) 1))) :=
  contMDiff_sphereTangentEquiv_symm contMDiff_id hu_diff hu

end TauCeti
