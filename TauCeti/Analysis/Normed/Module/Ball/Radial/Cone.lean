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
# Cones and radial extensions over maps on the unit sphere

A map `f` defined on the unit sphere of a real normed space `E` extends radially to all of `E` in
two canonical ways:

* its **`0`-homogeneous radial extension** `TauCeti.sphereExtend f`, sending `x ≠ 0` to
  `f (‖x‖⁻¹ • x)` and `0` to `0`;
* its **cone** (`1`-homogeneous extension) `TauCeti.sphereCone f`, sending `x ≠ 0` to
  `‖x‖ • f (‖x‖⁻¹ • x)` (read off `homeomorphUnitSphereProd`) and `0` to `0`, so
  `sphereCone f x = ‖x‖ • sphereExtend f x` (`TauCeti.sphereCone_eq_norm_smul_sphereExtend`).

On the ray through a unit vector `u`, `sphereExtend f` is constant for `r > 0`
(`TauCeti.sphereExtend_smul_of_pos`) while `sphereCone f` is `r • u ↦ r • f u`
(`TauCeti.sphereCone_smul_coe`). The cone is continuous when `f` is continuous and bounded
(`TauCeti.continuous_sphereCone`), since near the origin it is bounded by a multiple of the norm,
and Lipschitz when `f` is Lipschitz and bounded (`LipschitzWith.sphereCone`).

When `f` maps the unit sphere of `E` to the unit sphere of `F`, the cone preserves norms, and taking
cones is compatible with composition (`TauCeti.sphereCone_sphereCone`). So a homeomorphism `σ`
between the unit spheres has as cone a norm-preserving, positively homogeneous homeomorphism
`Homeomorph.sphereCone σ : E ≃ₜ F`, whose inverse is the cone of `σ.symm`; this is the radial
extension used in the Alexander trick.

## Main definitions

* `TauCeti.sphereExtend f`: the `0`-homogeneous extension `x ↦ f (‖x‖⁻¹ • x)` (`0 ↦ 0`) of `f`.
* `TauCeti.sphereCone f`: the cone `x ↦ ‖x‖ • f (‖x‖⁻¹ • x)` over a map `f` on the unit sphere.
* `Homeomorph.sphereCone σ`: the cone over a homeomorphism of unit spheres, a homeomorphism of
  the ambient spaces.

## Main results

* `TauCeti.sphereExtend_coe`, `TauCeti.sphereExtend_smul_of_pos`,
  `TauCeti.continuousAt_sphereExtend`, `TauCeti.continuousOn_sphereExtend`,
  `TauCeti.sphereCone_eq_norm_smul_sphereExtend`: restriction, `0`-homogeneity, continuity away from
  the origin, and relation to `TauCeti.sphereCone`.
* `TauCeti.sphereCone_smul_coe`: the cone sends `r • u` to `r • f u` for `r ≥ 0`.
* `TauCeti.sphereCone_smul`: the cone is positively homogeneous.
* `TauCeti.continuous_sphereCone`: the cone over a continuous bounded map is continuous.
* `TauCeti.sphereCone_eq_norm_smul_sphereDirection`: the cone in terms of the direction map
  `TauCeti.sphereDirection`.
* `LipschitzWith.sphereCone`: the cone over an `L`-Lipschitz map bounded by `M` is
  `(M + 2L)`-Lipschitz.
* `TauCeti.lipschitzWith_sphereCone`: the cone over a bounded Lipschitz map is Lipschitz.
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

/-- If the values of `f` are bounded in norm by `c`, the cone over `f` grows at most like `c`
times the norm. -/
theorem norm_sphereCone_le {c : ℝ} (hc : ∀ u, ‖f u‖ ≤ c) (x : E) :
    ‖sphereCone f x‖ ≤ c * ‖x‖ := by
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, u, rfl⟩
  · simp
  rw [sphereCone_smul_coe hr.le, norm_smul, norm_smul, norm_eq_of_mem_sphere u, mul_one, mul_comm]
  exact mul_le_mul_of_nonneg_right (hc u) (norm_nonneg _)

/-- **The cone over a bounded Lipschitz map is Lipschitz.** If `‖f u‖ ≤ a` for every unit vector
`u` and `f` is `b`-Lipschitz for the distance the unit sphere inherits from `E`, then the cone over
`f` is `(a + 2 b)`-Lipschitz on `E`. -/
theorem lipschitzWith_sphereCone {a b : ℝ≥0} (ha : ∀ u, ‖f u‖ ≤ a) (hb : LipschitzWith b f) :
    LipschitzWith (a + 2 * b) (sphereCone f) := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat]
  have hab : (a : ℝ) ≤ a + 2 * b := le_add_of_nonneg_right (by positivity)
  -- If one of the points is the origin, the bound `‖sphereCone f z‖ ≤ a ‖z‖` suffices.
  rcases eq_zero_or_exists_eq_smul_coe_sphere y with rfl | ⟨s, hs, q, rfl⟩
  · rw [sphereCone_zero, sub_zero, sub_zero]
    exact (norm_sphereCone_le ha x).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  rcases eq_zero_or_exists_eq_smul_coe_sphere x with rfl | ⟨r, hr, p, rfl⟩
  · rw [sphereCone_zero, zero_sub, norm_neg, zero_sub, norm_neg]
    exact (norm_sphereCone_le ha _).trans (mul_le_mul_of_nonneg_right hab (norm_nonneg _))
  -- Otherwise write `r • f p - s • f q = (r - s) • f p + s • (f p - f q)`, and bound `|r - s|`
  -- and `s ‖p - q‖` by `d = ‖r • p - s • q‖` and `2 d`.
  rw [sphereCone_smul_coe hr.le, sphereCone_smul_coe hs.le]
  have hp : ‖(p : E)‖ = 1 := norm_eq_of_mem_sphere p
  have hq : ‖(q : E)‖ = 1 := norm_eq_of_mem_sphere q
  set d := ‖r • (p : E) - s • (q : E)‖
  have hrs : |r - s| ≤ d := by
    simpa only [norm_smul, hp, hq, mul_one, Real.norm_of_nonneg hr.le,
      Real.norm_of_nonneg hs.le] using abs_norm_sub_norm_le (r • (p : E)) (s • (q : E))
  have hpq : s * ‖(p : E) - q‖ ≤ 2 * d := by
    have h : s • ((p : E) - q) = (s - r) • (p : E) + (r • (p : E) - s • (q : E)) := by
      rw [smul_sub, sub_smul]
      abel
    have h' := norm_add_le ((s - r) • (p : E)) (r • (p : E) - s • (q : E))
    rw [← h, norm_smul, norm_smul, Real.norm_of_nonneg hs.le, hp, mul_one, Real.norm_eq_abs,
      abs_sub_comm] at h'
    linarith
  have hfpq : ‖f p - f q‖ ≤ b * ‖(p : E) - q‖ := by
    simpa only [dist_eq_norm, Subtype.dist_eq] using hb.dist_le_mul p q
  have h : r • f p - s • f q = (r - s) • f p + s • (f p - f q) := by
    rw [smul_sub, sub_smul]
    abel
  rw [h]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_of_nonneg hs.le]
  nlinarith [mul_le_mul hrs (ha p) (norm_nonneg _) (norm_nonneg _),
    mul_le_mul_of_nonneg_left hfpq hs.le, mul_le_mul_of_nonneg_left hpq b.property]

/-- The cone over a continuous map whose values are bounded in norm is continuous. -/
theorem continuous_sphereCone (hf : Continuous f) {c : ℝ} (hc : ∀ u, ‖f u‖ ≤ c) :
    Continuous (sphereCone f) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [ContinuousAt, sphereCone_zero, tendsto_zero_iff_norm_tendsto_zero]
    have hle : ∀ y : E, ‖sphereCone f y‖ ≤ c * ‖y‖ := norm_sphereCone_le hc
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

/-- The **`0`-homogeneous radial extension** of a map `f` on the unit sphere of `E`: sends `x ≠ 0`
to `f (‖x‖⁻¹ • x)` and `0` to `0`. -/
def sphereExtend {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) (x : E) : H :=
  open scoped Classical in
  if hx : x = 0 then 0
  else f ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩

theorem sphereExtend_def {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) (x : E) :
    sphereExtend f x =
      open scoped Classical in
      if hx : x = 0 then 0
      else f ⟨NormedSpace.normalize x,
        mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩ :=
  (rfl)

@[simp]
theorem sphereExtend_zero {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) :
    sphereExtend f 0 = 0 := by
  simp [sphereExtend]

theorem sphereExtend_of_ne_zero {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) {x : E}
    (hx : x ≠ 0) :
    sphereExtend f x =
      f ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩ := by
  simp [sphereExtend, hx]

/-- The `0`-homogeneous radial extension of `f` restricts to `f` on the unit sphere. -/
@[simp]
theorem sphereExtend_coe {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H)
    (p : sphere (0 : E) 1) :
    sphereExtend f (p : E) = f p := by
  rw [sphereExtend_of_ne_zero f (norm_ne_zero_iff.1 (by simp [norm_eq_of_mem_sphere p]))]
  congr 1
  exact Subtype.ext (NormedSpace.normalize_eq_self_of_norm_eq_one (norm_eq_of_mem_sphere p))

@[simp]
theorem sphereExtend_comp_coe {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) :
    sphereExtend f ∘ ((↑) : sphere (0 : E) 1 → E) = f :=
  funext (sphereExtend_coe f)

/-- The `0`-homogeneous radial extension is constant along open rays (`r > 0`). -/
theorem sphereExtend_smul_of_pos {H : Type*} [Zero H] (f : sphere (0 : E) 1 → H) {r : ℝ}
    (hr : 0 < r) (x : E) :
    sphereExtend f (r • x) = sphereExtend f x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sphereExtend_of_ne_zero f (smul_ne_zero hr.ne' hx), sphereExtend_of_ne_zero f hx]
    congr 1
    exact Subtype.ext (NormedSpace.normalize_smul_of_pos hr x)

@[simp]
theorem sphereExtend_zero_fun {H : Type*} [Zero H] :
    sphereExtend (0 : sphere (0 : E) 1 → H) = 0 := by
  ext x
  by_cases hx : x = 0 <;> simp [sphereExtend, hx]

@[simp]
theorem sphereExtend_add {H : Type*} [AddZeroClass H] (f₁ f₂ : sphere (0 : E) 1 → H) :
    sphereExtend (f₁ + f₂) = sphereExtend f₁ + sphereExtend f₂ := by
  ext x
  by_cases hx : x = 0 <;> simp [sphereExtend, hx]

@[simp]
theorem sphereExtend_const_smul {R H : Type*} [Zero H] [SMulZeroClass R H] (c : R)
    (f : sphere (0 : E) 1 → H) :
    sphereExtend (c • f) = c • sphereExtend f := by
  ext x
  by_cases hx : x = 0 <;> simp [sphereExtend, hx]

/-- Away from the origin, `sphereExtend f` is continuous at `x` whenever `f` is continuous at
`‖x‖⁻¹ • x`. -/
theorem continuousAt_sphereExtend {H : Type*} [TopologicalSpace H] [Zero H]
    {f : sphere (0 : E) 1 → H} {x : E} (hx : x ≠ 0)
    (hf : ContinuousAt f
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩) :
    ContinuousAt (sphereExtend f) x := by
  have heq : (({0}ᶜ : Set E).domRestrict (sphereExtend f)) =
      (f ∘ Prod.fst) ∘ homeomorphUnitSphereProd E := by
    funext y
    rw [domRestrict_apply, sphereExtend_of_ne_zero f y.property, Function.comp_apply,
      Function.comp_apply]
    congr 1
    ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, NormedSpace.normalize]
  have hx_eq : (homeomorphUnitSphereProd E ⟨x, mem_compl_singleton_iff.2 hx⟩).1 =
      ⟨NormedSpace.normalize x, mem_sphere_zero_iff_norm.2 (NormedSpace.norm_normalize hx)⟩ := by
    ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, NormedSpace.normalize]
  have hcont : ContinuousAt (({0}ᶜ : Set E).domRestrict (sphereExtend f))
      ⟨x, mem_compl_singleton_iff.2 hx⟩ := by
    rw [heq]
    exact ((hx_eq ▸ hf).comp continuous_fst.continuousAt).comp
      (homeomorphUnitSphereProd E).continuous.continuousAt
  exact (continuousWithinAt_iff_continuousAt_domRestrict _ _).2 hcont
    |>.continuousAt (isOpen_compl_singleton.mem_nhds hx)

/-- The `0`-homogeneous radial extension of a continuous map on the unit sphere is continuous
away from the origin. -/
theorem continuousOn_sphereExtend {H : Type*} [TopologicalSpace H] [Zero H]
    {f : sphere (0 : E) 1 → H} (hf : Continuous f) :
    ContinuousOn (sphereExtend f) {0}ᶜ :=
  fun _ hx ↦ (continuousAt_sphereExtend hx hf.continuousAt).continuousWithinAt

/-- The cone over `f` is `‖x‖` times its `0`-homogeneous radial extension `sphereExtend f`. -/
theorem sphereCone_eq_norm_smul_sphereExtend (f : sphere (0 : E) 1 → F) (x : E) :
    sphereCone f x = ‖x‖ • sphereExtend f x := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [sphereCone_of_ne_zero hx, sphereExtend_of_ne_zero f hx]
    congr 2
    ext
    simp only [homeomorphUnitSphereProd_apply_fst_coe, NormedSpace.normalize]

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
