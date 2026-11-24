/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
public import TauCeti.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Cones over maps on the unit sphere

A map `f` defined on the unit sphere of a real normed space `E` extends to a positively homogeneous
map on all of `E`, its **cone** `TauCeti.sphereCone f`: a vector `x ≠ 0` goes to
`‖x‖ • f (‖x‖⁻¹ • x)`, the direction `‖x‖⁻¹ • x` being read off the polar coordinates
`homeomorphUnitSphereProd`, and the origin goes to the origin. On the ray through a unit vector `u`
it is `r • u ↦ r • f u` (`TauCeti.sphereCone_smul_coe`). It is continuous when `f` is continuous
and bounded (`TauCeti.continuous_sphereCone`), since near the origin it is bounded by a multiple of
the norm, and Lipschitz when `f` is Lipschitz and bounded (`LipschitzWith.sphereCone`).

When `f` maps the unit sphere of `E` to the unit sphere of `F`, the cone preserves norms, and taking
cones is compatible with composition (`TauCeti.sphereCone_sphereCone`). So a homeomorphism `σ`
between the unit spheres has as cone a norm-preserving, positively homogeneous homeomorphism
`Homeomorph.sphereCone σ : E ≃ₜ F`, whose inverse is the cone of `σ.symm`; this is the radial
extension used in the Alexander trick.

## Main definitions

* `TauCeti.sphereCone f`: the cone `x ↦ ‖x‖ • f (‖x‖⁻¹ • x)` over a map `f` on the unit sphere.
* `Homeomorph.sphereCone σ`: the cone over a homeomorphism of unit spheres, a homeomorphism of
  the ambient spaces.

## Main results

* `TauCeti.sphereCone_smul_coe`: the cone sends `r • u` to `r • f u` for `r ≥ 0`.
* `TauCeti.sphereCone_smul`: the cone is positively homogeneous.
* `TauCeti.continuous_sphereCone`: the cone over a continuous bounded map is continuous.
* `TauCeti.sphereCone_eq_norm_smul_sphereDirection`: the cone in terms of the direction map
  `TauCeti.sphereDirection`.
* `LipschitzWith.sphereCone`: the cone over an `L`-Lipschitz map bounded by `M` is
  `(M + 2L)`-Lipschitz.
* `TauCeti.norm_sphereCone`: the cone over a map into the unit sphere preserves norms.
* `TauCeti.sphereCone_sphereCone`, `Homeomorph.sphereCone_trans`: the cone over a composite is the
  composite of the cones.
* `Homeomorph.bijOn_sphereCone_closedBall`, `Homeomorph.tendsto_sphereCone_cobounded`: the cone
  over a homeomorphism of unit spheres maps each closed ball about the origin onto itself and tends
  to infinity at infinity.
-/

public section

noncomputable section

open Metric Set Filter Topology
open scoped NNReal

namespace TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **cone** over a map `f` on the unit sphere of `E`: the positively homogeneous extension
`x ↦ ‖x‖ • f (‖x‖⁻¹ • x)` of `f` to `E`, sending the origin to the origin. -/
def sphereCone (f : sphere (0 : E) 1 → F) (x : E) : F :=
  open scoped Classical in
  if hx : x = 0 then 0 else ‖x‖ • f (homeomorphUnitSphereProd E ⟨x, mem_compl_singleton_iff.2 hx⟩).1

variable {f : sphere (0 : E) 1 → F}

@[simp]
theorem sphereCone_zero (f : sphere (0 : E) 1 → F) : sphereCone f 0 = 0 := by
  simp [sphereCone]

theorem sphereCone_of_ne_zero {x : E} (hx : x ≠ 0) :
    sphereCone f x = ‖x‖ • f (homeomorphUnitSphereProd E ⟨x, mem_compl_singleton_iff.2 hx⟩).1 :=
  by simp [sphereCone, hx]

/-- On the ray through a unit vector `u`, the cone over `f` is `r • u ↦ r • f u`. -/
theorem sphereCone_smul_coe {r : ℝ} (hr : 0 ≤ r) (u : sphere (0 : E) 1) :
    sphereCone f (r • (u : E)) = r • f u := by
  rcases hr.eq_or_lt with rfl | hr
  · simp
  have hu : ‖(u : E)‖ = 1 := norm_eq_of_mem_sphere u
  have hne : r • (u : E) ≠ 0 := smul_ne_zero hr.ne' (norm_ne_zero_iff.1 (by simp [hu]))
  have hn : ‖r • (u : E)‖ = r := by rw [norm_smul, hu, mul_one, Real.norm_of_nonneg hr.le]
  rw [sphereCone_of_ne_zero hne, hn]
  congr 2
  ext
  rw [homeomorphUnitSphereProd_apply_fst_coe, hn, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

/-- The cone over `f` restricts to `f` on the unit sphere. -/
@[simp]
theorem sphereCone_coe (u : sphere (0 : E) 1) : sphereCone f u = f u := by
  simpa using sphereCone_smul_coe (f := f) zero_le_one u

/-- Every vector is a nonnegative multiple of a unit vector, unless the sphere is empty, in which
case it is zero. This is the case split by which statements about cones reduce to rays. -/
theorem eq_zero_or_exists_eq_smul_coe_sphere (x : E) :
    x = 0 ∨ ∃ r : ℝ, 0 < r ∧ ∃ u : sphere (0 : E) 1, x = r • (u : E) := by
  rcases eq_or_ne x 0 with hx | hx
  · exact .inl hx
  refine .inr ⟨‖x‖, norm_pos_iff.2 hx,
    ⟨‖x‖⁻¹ • x, mem_sphere_zero_iff_norm.2 (norm_smul_inv_norm (𝕜 := ℝ) hx)⟩, ?_⟩
  rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.2 hx), one_smul]

/-- The cone over `f` is positively homogeneous. -/
theorem sphereCone_smul {t : ℝ} (ht : 0 ≤ t) (x : E) :
    sphereCone f (t • x) = t • sphereCone f x := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  rw [smul_smul, sphereCone_smul_coe (mul_nonneg ht hr.le), sphereCone_smul_coe hr.le, smul_smul]

/-- The cone over the inclusion of the unit sphere is the identity. -/
@[simp]
theorem sphereCone_subtypeVal : sphereCone ((↑) : sphere (0 : E) 1 → E) = id := by
  funext x
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  simp [sphereCone_smul_coe hr.le]

/-- The cone over a map into the unit sphere preserves norms. -/
theorem norm_sphereCone (hf : ∀ u, ‖f u‖ = 1) (x : E) : ‖sphereCone f x‖ = ‖x‖ := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  rw [sphereCone_smul_coe hr.le, norm_smul, norm_smul, hf, norm_eq_of_mem_sphere u]

/-- The cone over a continuous map whose values are bounded in norm is continuous. -/
theorem continuous_sphereCone (hf : Continuous f) {c : ℝ} (hc : ∀ u, ‖f u‖ ≤ c) :
    Continuous (sphereCone f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, sphereCone_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ y : E, ‖sphereCone f y‖ ≤ c * ‖y‖ := fun y => by
      rcases eq_zero_or_exists_eq_smul_coe_sphere y with rfl | ⟨r, hr, u, rfl⟩
      · simp
      rw [sphereCone_smul_coe hr.le, norm_smul, norm_smul, norm_eq_of_mem_sphere u, mul_one,
        mul_comm]
      exact mul_le_mul_of_nonneg_right (hc u) (norm_nonneg _)
    have h0 : Tendsto (fun y : E => c * ‖y‖) (𝓝 0) (𝓝 0) :=
      (continuous_const.mul continuous_norm).tendsto' 0 0 (by simp)
    exact squeeze_zero (fun y => norm_nonneg _) hle h0
  · -- Away from the origin the cone is `(u, r) ↦ r • f u` in polar coordinates.
    have hcont : ContinuousOn (sphereCone f) {0}ᶜ := by
      rw [continuousOn_iff_continuous_domRestrict]
      have heq : ({0}ᶜ : Set E).domRestrict (sphereCone f) =
          (fun p => (p.2 : ℝ) • f p.1) ∘ homeomorphUnitSphereProd E := by
        funext y
        rw [domRestrict_apply, sphereCone_of_ne_zero y.property, Function.comp_apply,
          homeomorphUnitSphereProd_apply_snd_coe]
      rw [heq]
      exact ((continuous_subtypeVal.comp continuous_snd).smul (hf.comp continuous_fst)).comp
        (homeomorphUnitSphereProd E).continuous
    exact hcont.continuousAt (isOpen_compl_singleton.mem_nhds hx)

/-- The cone over `f` at `x` is `‖x‖ • f` of the direction of `x`, whatever direction `e` the
direction map assigns to the origin. -/
theorem sphereCone_eq_norm_smul_sphereDirection (e : sphere (0 : E) 1) (x : E) :
    sphereCone f x = ‖x‖ • f (sphereDirection e x) := by
  conv_lhs => rw [← norm_smul_sphereDirection e x]
  exact sphereCone_smul_coe (norm_nonneg x) _

/-- The cone over an `L`-Lipschitz map `g` on the unit sphere with `‖g‖ ≤ M` is
`(M + 2L)`-Lipschitz on the whole space. -/
theorem _root_.LipschitzWith.sphereCone {g : sphere (0 : E) 1 → F} {L M : ℝ≥0}
    (hg : LipschitzWith L g) (hM : ∀ u, ‖g u‖ ≤ M) : LipschitzWith (M + 2 * L) (sphereCone g) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rcases isEmpty_or_nonempty (sphere (0 : E) 1) with hE | ⟨⟨e⟩⟩
  · -- Without unit vectors every vector is zero.
    have h0 (z : E) : z = 0 :=
      (eq_zero_or_exists_eq_smul_coe_sphere z).resolve_right fun ⟨_, _, u, _⟩ ↦ hE.false u
    simp [h0 x, h0 y]
  have hxy : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  -- Inside this proof the bare name `sphereCone` refers to this theorem, hence the qualification.
  calc dist (TauCeti.sphereCone g x) (TauCeti.sphereCone g y)
      = ‖(‖x‖ - ‖y‖) • g (sphereDirection e x) +
          ‖y‖ • (g (sphereDirection e x) - g (sphereDirection e y))‖ := by
        rw [sphereCone_eq_norm_smul_sphereDirection e x,
          sphereCone_eq_norm_smul_sphereDirection e y, dist_eq_norm, sub_smul, smul_sub]
        congr 1
        abel
    _ ≤ |‖x‖ - ‖y‖| * M + ‖y‖ * (L * dist (sphereDirection e x) (sphereDirection e y)) := by
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_smul, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
        · rw [norm_smul, norm_norm, ← dist_eq_norm]
          exact mul_le_mul_of_nonneg_left (hg.dist_le_mul _ _) (norm_nonneg _)
    _ ≤ dist x y * M + L * (2 * dist x y) := by
        have h2 := norm_mul_dist_sphereDirection_le e x y
        rw [← dist_eq_norm] at h2
        rw [mul_left_comm]
        exact add_le_add (mul_le_mul_of_nonneg_right hxy M.coe_nonneg)
          (mul_le_mul_of_nonneg_left h2 L.coe_nonneg)
    _ = ((M + 2 * L : ℝ≥0) : ℝ) * dist x y := by
        push_cast
        ring

/-- **The cone over a composite is the composite of the cones**, when the inner map takes values in
the unit sphere. -/
theorem sphereCone_sphereCone (g : sphere (0 : F) 1 → G) (f : sphere (0 : E) 1 → sphere (0 : F) 1)
    (x : E) : sphereCone g (sphereCone ((↑) ∘ f) x) = sphereCone (g ∘ f) x := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  rw [sphereCone_smul_coe hr.le, sphereCone_smul_coe hr.le, Function.comp_apply,
    sphereCone_smul_coe hr.le, Function.comp_apply]

end TauCeti

namespace Homeomorph

open TauCeti

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- The **cone over a homeomorphism of unit spheres**: the positively homogeneous, norm-preserving
homeomorphism `x ↦ ‖x‖ • σ (‖x‖⁻¹ • x)` of the ambient spaces, sending the origin to the origin.
Its inverse is the cone over `σ.symm` (`Homeomorph.sphereCone_symm`). -/
def sphereCone (σ : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1) : E ≃ₜ F where
  toFun := TauCeti.sphereCone ((↑) ∘ σ)
  invFun := TauCeti.sphereCone ((↑) ∘ σ.symm)
  left_inv x := by
    rw [TauCeti.sphereCone_sphereCone]
    simp [Function.comp_def]
  right_inv x := by
    rw [TauCeti.sphereCone_sphereCone]
    simp [Function.comp_def]
  continuous_toFun := continuous_sphereCone (by fun_prop) fun u => (norm_eq_of_mem_sphere _).le
  continuous_invFun := continuous_sphereCone (by fun_prop) fun u => (norm_eq_of_mem_sphere _).le

variable (σ : sphere (0 : E) 1 ≃ₜ sphere (0 : F) 1)

theorem coe_sphereCone : ⇑σ.sphereCone = TauCeti.sphereCone ((↑) ∘ σ) :=
  (rfl)

@[simp]
theorem sphereCone_symm : σ.sphereCone.symm = σ.symm.sphereCone :=
  (rfl)

/-- The cone over the identity of the unit sphere is the identity. -/
@[simp]
theorem sphereCone_refl : (Homeomorph.refl (sphere (0 : E) 1)).sphereCone = Homeomorph.refl E := by
  ext x
  simp [coe_sphereCone]

/-- The cone over a composite of homeomorphisms of unit spheres is the composite of the cones. -/
theorem sphereCone_trans (τ : sphere (0 : F) 1 ≃ₜ sphere (0 : G) 1) :
    (σ.trans τ).sphereCone = σ.sphereCone.trans τ.sphereCone := by
  ext x
  simp only [coe_sphereCone, trans_apply, TauCeti.sphereCone_sphereCone]
  simp only [Function.comp_def, trans_apply]

@[simp]
theorem sphereCone_apply_zero : σ.sphereCone 0 = 0 :=
  TauCeti.sphereCone_zero _

/-- The cone over a homeomorphism of unit spheres restricts to it on the unit sphere. -/
@[simp]
theorem sphereCone_apply_coe (u : sphere (0 : E) 1) : σ.sphereCone u = σ u :=
  TauCeti.sphereCone_coe (f := Subtype.val ∘ σ) u

/-- The cone over a homeomorphism of unit spheres preserves norms. -/
@[simp]
theorem norm_sphereCone_apply (x : E) : ‖σ.sphereCone x‖ = ‖x‖ :=
  norm_sphereCone (fun u => norm_eq_of_mem_sphere (σ u)) x

/-- The cone over a homeomorphism of unit spheres maps each closed ball about the origin
bijectively onto itself. -/
theorem bijOn_sphereCone_closedBall (r : ℝ) :
    BijOn σ.sphereCone (closedBall 0 r) (closedBall 0 r) := by
  refine ⟨fun x hx => by simpa using hx, σ.sphereCone.injective.injOn, fun y hy => ?_⟩
  exact ⟨σ.sphereCone.symm y, by simpa using hy, σ.sphereCone.apply_symm_apply y⟩

/-- The cone over a homeomorphism of unit spheres tends to infinity at infinity. -/
theorem tendsto_sphereCone_cobounded :
    Tendsto σ.sphereCone (Bornology.cobounded E) (Bornology.cobounded F) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa using tendsto_norm_cobounded_atTop

end Homeomorph
