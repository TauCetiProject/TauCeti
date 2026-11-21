/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Normalize

/-!
# Radial projection to the unit sphere

This file proves that normalization is continuous away from the origin, in the form
`Filter.Tendsto.normalize`, and packages pointwise normalization of a continuous nowhere-zero
map as a continuous map to the unit sphere. It also defines the direction map
`sphereDirection e`, which sends a nonzero vector `x` to `‖x‖⁻¹ • x` and the origin to an assigned
point `e` of the unit sphere.

## Main results

* `Filter.Tendsto.normalize`: normalization preserves limits with a nonzero limit.
* `NormedSpace.isClosed_setOf_eq_zero_or_normalize_mem`: the cone `{0} ∪ {x ≠ 0 | x / ‖x‖ ∈ S}`
  over a closed set `S` of directions is closed.
* `TauCeti.norm_div_norm_smul_eq_of_inv_norm_smul_eq_normalize`: rescaling a vector with the
  direction of `w` by the ratio of the norms recovers `w`.
* `TauCeti.norm_div_norm_smul_le`, `Continuous.div_norm_smul`: rescaling `y` to length
  `τ ≤ ‖y‖` by `(τ / ‖y‖) • y` is bounded by `τ` and continuous, also where `y` vanishes.
* `TauCeti.continuousAt_sphereDirection`: the direction map is continuous away from the origin.
* `TauCeti.norm_mul_dist_sphereDirection_le`: `‖y‖ dist (x / ‖x‖, y / ‖y‖) ≤ 2 ‖x - y‖`.
* `LipschitzWith.norm_mul_comp_sphereDirection`: the positively homogeneous extension
  `x ↦ ‖x‖ g (x / ‖x‖)` of an `L`-Lipschitz function `g` on the sphere bounded by `M` is
  `(M + 2L)`-Lipschitz.

## Main definitions

* `TauCeti.normalizeToSphere`: radial projection of a continuous nowhere-zero map.
* `TauCeti.sphereDirection`: the direction of a vector, with an assigned value at the origin.
-/

public section

noncomputable section

open Filter Metric NormedSpace Set Topology
open scoped NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `f` tends to a nonzero vector `x`, then the normalization of `f` tends to the normalization
of `x`. -/
theorem _root_.Filter.Tendsto.normalize {α : Type*} {l : Filter α} {f : α → E} {x : E}
    (hf : Tendsto f l (𝓝 x)) (hx : x ≠ 0) :
    Tendsto (fun a => NormedSpace.normalize (f a)) l (𝓝 (NormedSpace.normalize x)) := by
  simp only [NormedSpace.normalize]
  exact (hf.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul hf

/-- The cone over a closed set `S` of directions, the set of vectors that are zero or whose
normalization lies in `S`, is closed. -/
theorem _root_.NormedSpace.isClosed_setOf_eq_zero_or_normalize_mem {S : Set E} (hS : IsClosed S) :
    IsClosed {x : E | x = 0 ∨ normalize x ∈ S} := by
  have : {x : E | x = 0 ∨ normalize x ∈ S}ᶜ = {x | x ≠ 0} ∩ normalize ⁻¹' Sᶜ := by
    ext x
    simp [not_or]
  rw [← isOpen_compl_iff, this]
  exact ContinuousOn.isOpen_inter_preimage
    (fun x hx ↦ ContinuousAt.continuousWithinAt (tendsto_id.normalize hx)) isOpen_ne
    hS.isOpen_compl

/-- Radial projection sends a continuous nowhere-zero map into a real normed space continuously
to its unit sphere. -/
noncomputable def normalizeToSphere {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) : C(Y, sphere (0 : E) 1) where
  toFun y := ⟨normalize (f y), mem_sphere_zero_iff_norm.mpr (norm_normalize (h0 y))⟩
  continuous_toFun :=
    (continuous_iff_continuousAt.2 fun y => (hf.tendsto y).normalize (h0 y)).subtype_mk _

/-- The underlying vector of `normalizeToSphere f hf h0 y` is the normalization of `f y`. -/
@[simp]
theorem coe_normalizeToSphere_apply {Y : Type*} [TopologicalSpace Y] (f : Y → E)
    (hf : Continuous f) (h0 : ∀ y, f y ≠ 0) (y : Y) :
    ((normalizeToSphere f hf h0 y : sphere (0 : E) 1) : E) = normalize (f y) :=
  (rfl)

/-- **Rescaling to a prescribed vector.** If `x` has the direction of `w` and the length of `a`,
that is `‖a‖⁻¹ • x = normalize w`, then stretching `x` by `‖w‖ / ‖a‖` gives `w`. -/
theorem norm_div_norm_smul_eq_of_inv_norm_smul_eq_normalize {a w x : E}
    (hx : ‖a‖⁻¹ • x = normalize w) : (‖w‖ / ‖a‖) • x = w := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [norm_zero, inv_zero, zero_smul, eq_comm, normalize_eq_zero_iff] at hx
    simp [hx]
  · rw [← smul_inv_smul₀ (norm_ne_zero_iff.2 ha) x, hx, smul_smul,
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 ha), norm_smul_normalize]

/-- The norm of `(τ / ‖y‖) • y` is at most `τ`, for `0 ≤ τ`. -/
theorem norm_div_norm_smul_le (y : E) {τ : ℝ} (hτ : 0 ≤ τ) : ‖(τ / ‖y‖) • y‖ ≤ τ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simpa using hτ
  · rw [norm_smul, Real.norm_of_nonneg (div_nonneg hτ (norm_nonneg _)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.2 hy)]

/-- The map `p ↦ (τ p / ‖y p‖) • y p` is continuous when `0 ≤ τ p ≤ ‖y p‖`, including where `y`
vanishes, since there its norm is at most `‖y p‖`. -/
theorem _root_.Continuous.div_norm_smul {X : Type*} [TopologicalSpace X] {τ : X → ℝ} {y : X → E}
    (hτ : Continuous τ) (hy : Continuous y) (h0 : ∀ p, 0 ≤ τ p) (hle : ∀ p, τ p ≤ ‖y p‖) :
    Continuous fun p ↦ (τ p / ‖y p‖) • y p := by
  refine continuous_iff_continuousAt.2 fun p ↦ ?_
  rcases eq_or_ne (y p) 0 with hp | hp
  · have hlim : Tendsto (fun q ↦ (τ q / ‖y q‖) • y q) (𝓝 p) (𝓝 0) :=
      squeeze_zero_norm (fun q ↦ (norm_div_norm_smul_le (y q) (h0 q)).trans (hle q))
        (by simpa [hp] using hy.norm.tendsto p)
    simpa [ContinuousAt, hp] using hlim
  · exact (hτ.continuousAt.div (continuous_norm.comp hy).continuousAt
      (norm_ne_zero_iff.2 hp)).smul hy.continuousAt

section Direction

open Classical in
/-- The direction of a vector on the unit sphere: `‖x‖⁻¹ • x` for a nonzero vector `x`, and the
assigned point `e` of the sphere at the origin. -/
def sphereDirection (e : sphere (0 : E) 1) (x : E) : sphere (0 : E) 1 :=
  ⟨if x = 0 then e else normalize x, by
    split_ifs with hx
    exacts [e.property, mem_sphere_zero_iff_norm.2 (norm_normalize hx)]⟩

variable (e : sphere (0 : E) 1) {x : E}

/-- The direction of the origin is the assigned point. -/
@[simp]
theorem sphereDirection_zero : sphereDirection e 0 = e := by
  simp [sphereDirection]

/-- The direction of a nonzero vector is its normalization. -/
theorem coe_sphereDirection_of_ne_zero (hx : x ≠ 0) :
    (sphereDirection e x : E) = normalize x := by
  simp [sphereDirection, hx]

/-- A vector is its norm times its direction. -/
@[simp]
theorem norm_smul_sphereDirection (x : E) : ‖x‖ • (sphereDirection e x : E) = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [coe_sphereDirection_of_ne_zero e hx, norm_smul_normalize]

/-- A positive multiple of a point of the sphere has that point as its direction. -/
@[simp]
theorem sphereDirection_smul_of_pos {r : ℝ} (hr : 0 < r) (u : sphere (0 : E) 1) :
    sphereDirection e (r • (u : E)) = u := by
  have hu : (u : E) ≠ 0 := ne_zero_of_mem_sphere one_ne_zero u
  ext1
  rw [coe_sphereDirection_of_ne_zero e (smul_ne_zero hr.ne' hu), normalize_smul_of_pos hr,
    normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere u)]

/-- A point of the sphere is its own direction. -/
@[simp]
theorem sphereDirection_coe (u : sphere (0 : E) 1) : sphereDirection e (u : E) = u := by
  simpa using sphereDirection_smul_of_pos e one_pos u

/-- The direction map is continuous away from the origin. -/
theorem continuousAt_sphereDirection (hx : x ≠ 0) : ContinuousAt (sphereDirection e) x := by
  rw [IsInducing.subtypeVal.continuousAt_iff, ContinuousAt, Function.comp_apply,
    coe_sphereDirection_of_ne_zero e hx]
  exact (tendsto_id.normalize hx).congr' <| Filter.mem_of_superset (isOpen_ne.mem_nhds hx)
    fun y hy ↦ (coe_sphereDirection_of_ne_zero e hy).symm

/-- Directions of two vectors are at distance at most `2 ‖x - y‖ / ‖y‖`, in the multiplied-out
form `‖y‖ dist (x / ‖x‖, y / ‖y‖) ≤ 2 ‖x - y‖`, which also holds when either vector vanishes. -/
theorem norm_mul_dist_sphereDirection_le (x y : E) :
    ‖y‖ * dist (sphereDirection e x) (sphereDirection e y) ≤ 2 * ‖x - y‖ := by
  set u : E := (sphereDirection e x : E)
  have hu : ‖u‖ = 1 := norm_eq_of_mem_sphere (sphereDirection e x)
  -- `‖y‖ • (u - v) = (‖y‖ - ‖x‖) • u + (x - y)`, using `‖x‖ • u = x` and `‖y‖ • v = y`.
  have hdecomp : ‖y‖ • (u - sphereDirection e y) = (‖y‖ - ‖x‖) • u + (x - y) := by
    rw [smul_sub, norm_smul_sphereDirection, sub_smul, norm_smul_sphereDirection]
    abel
  calc ‖y‖ * dist (sphereDirection e x) (sphereDirection e y)
      = ‖(‖y‖ - ‖x‖) • u + (x - y)‖ := by
        rw [Subtype.dist_eq, dist_eq_norm, ← hdecomp, norm_smul, norm_norm]
    _ ≤ |‖y‖ - ‖x‖| + ‖x - y‖ := by
        simpa [norm_smul, hu] using norm_add_le ((‖y‖ - ‖x‖) • u) (x - y)
    _ ≤ 2 * ‖x - y‖ := by
        linarith [abs_norm_sub_norm_le y x, norm_sub_rev y x]

end Direction

end TauCeti

open TauCeti in
/-- The positively homogeneous extension `x ↦ ‖x‖ g (x / ‖x‖)` of an `L`-Lipschitz function `g`
on the unit sphere with `|g| ≤ M` is `(M + 2L)`-Lipschitz on the whole space. The value assigned
to the direction of the origin is irrelevant, since the extension vanishes there. -/
theorem LipschitzWith.norm_mul_comp_sphereDirection {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {g : sphere (0 : E) 1 → ℝ} {L M : ℝ≥0}
    (hg : LipschitzWith L g) (hM : ∀ u, |g u| ≤ M) (e : sphere (0 : E) 1) :
    LipschitzWith (M + 2 * L) fun x ↦ ‖x‖ * g (sphereDirection e x) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  have hxy : |‖x‖ - ‖y‖| ≤ dist x y := by
    rw [dist_eq_norm]
    exact abs_norm_sub_norm_le x y
  calc dist (‖x‖ * g (sphereDirection e x)) (‖y‖ * g (sphereDirection e y))
      = |(‖x‖ - ‖y‖) * g (sphereDirection e x) +
          ‖y‖ * (g (sphereDirection e x) - g (sphereDirection e y))| := by
        rw [Real.dist_eq]
        congr 1
        ring
    _ ≤ |‖x‖ - ‖y‖| * M + ‖y‖ * (L * dist (sphereDirection e x) (sphereDirection e y)) := by
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (hM _) (abs_nonneg _)
        · rw [abs_mul, abs_norm, ← Real.dist_eq]
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

end
