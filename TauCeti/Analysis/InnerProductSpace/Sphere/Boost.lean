/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Conformal boosts of a unit sphere

Fix a unit vector `v` of a real inner product space `E`. For `a : ℝ`, the **boost** of the unit
sphere toward `v` is the map

`sphereBoost v a x = (cosh a + sinh a ⟪x, v⟫)⁻¹ • (x + (sinh a + (cosh a - 1) ⟪x, v⟫) • v)`.

It is the action on the unit sphere, viewed as the projectivized future light cone
`{(1, x) | ‖x‖ = 1}` of `ℝ × E`, of the Lorentz boost of rapidity `a` in the plane spanned by the
time direction and `v`. Through stereographic projection from `-v` it is the dilation by `e⁻ᵃ`, so
it is a Möbius transformation of the sphere fixing `v` and `-v`. For `a > 0` every point other
than `-v` moves toward `v`: the height `⟪x, v⟫ = tanh σ` becomes `tanh (σ + a)`
(`TauCeti.inner_sphereBoost`).

The boosts preserve the unit sphere (`TauCeti.norm_sphereBoost`), form a one-parameter group on it
(`TauCeti.sphereBoost_sphereBoost`, `TauCeti.sphereBoost_zero`) and commute with linear
isometries (`LinearIsometry.sphereBoost_map`). In particular a boost toward `ι i`, for a
linear isometry `ι : ℂ →ₗᵢ[ℝ] E`, preserves the great circle `ι` of the unit circle and acts on it
by the boost of the unit circle toward `i`. Boosting far enough carries a compact set of the
sphere avoiding `-v` into the open hemisphere around `v`
(`IsCompact.eventually_forall_inner_sphereBoost_pos`).

## Main definitions

* `TauCeti.sphereBoost v a`: the boost of rapidity `a` toward `v`.

## Main results

* `TauCeti.norm_sphereBoost`: boosts preserve the unit sphere.
* `TauCeti.sphereBoost_sphereBoost`: on the unit sphere, rapidities add under composition.
* `TauCeti.inner_sphereBoost`: the height formula `tanh σ ↦ tanh (σ + a)`.
* `LinearIsometry.sphereBoost_map`: boosts commute with linear isometries.
* `IsCompact.eventually_forall_inner_sphereBoost_pos`: large boosts carry a compact set
  avoiding `-v` into the open hemisphere around `v`.

## References

* J. G. Ratcliffe, *Foundations of Hyperbolic Manifolds*, Graduate Texts in Mathematics 149,
  3rd ed., Springer (2019), Sections 4.1 and 4.5 (Lorentz transformations and their action on
  the sphere at infinity as Möbius transformations).
-/

public section

noncomputable section

open Real
open scoped RealInnerProductSpace

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The **boost** of rapidity `a` toward the vector `v`:
`x ↦ (cosh a + sinh a ⟪x, v⟫)⁻¹ • (x + (sinh a + (cosh a - 1) ⟪x, v⟫) • v)`. For a unit vector
`v` it maps the unit sphere to itself, fixing `±v`, and moves every other point of the sphere
along the great circle through `v` toward `v` when `0 < a`. -/
def sphereBoost (v : E) (a : ℝ) (x : E) : E :=
  (cosh a + sinh a * ⟪x, v⟫)⁻¹ • (x + (sinh a + (cosh a - 1) * ⟪x, v⟫) • v)

theorem sphereBoost_def (v : E) (a : ℝ) (x : E) :
    sphereBoost v a x =
      (cosh a + sinh a * ⟪x, v⟫)⁻¹ • (x + (sinh a + (cosh a - 1) * ⟪x, v⟫) • v) :=
  (rfl)

/-- The boost of rapidity zero is the identity. -/
@[simp]
theorem sphereBoost_zero (v : E) : sphereBoost v 0 = id := by
  funext x
  simp [sphereBoost_def]

/-- The denominator of a boost is positive on the unit sphere. -/
theorem cosh_add_sinh_mul_inner_pos {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (a : ℝ) :
    0 < cosh a + sinh a * ⟪x, v⟫ := by
  -- `2 (cosh a + sinh a s) = eᵃ (1 + s) + e⁻ᵃ (1 - s)` is a positive combination for `|s| ≤ 1`.
  have h2 : 2 * (cosh a + sinh a * ⟪x, v⟫) =
      exp a * (1 + ⟪x, v⟫) + exp (-a) * (1 - ⟪x, v⟫) := by
    rw [← cosh_add_sinh a, ← cosh_sub_sinh a]
    ring
  have hs₁ := neg_one_le_real_inner_of_norm_eq_one hx hv
  have h₁ := mul_nonneg (exp_pos a).le (by linarith : 0 ≤ 1 + ⟪x, v⟫)
  have h₂ := mul_nonneg (exp_pos (-a)).le
    (by linarith [real_inner_le_one_of_norm_eq_one hx hv] : 0 ≤ 1 - ⟪x, v⟫)
  rcases eq_or_lt_of_le hs₁ with hs | hs
  · nlinarith [exp_pos (-a)]
  · nlinarith [mul_pos (exp_pos a) (by linarith : 0 < 1 + ⟪x, v⟫)]

/-- **The height formula.** Boosting a point of height `s = tanh σ` by `a` gives the height
`(sinh a + cosh a s) / (cosh a + sinh a s) = tanh (σ + a)`. -/
theorem inner_sphereBoost {v : E} (hv : ‖v‖ = 1) (a : ℝ) (x : E) :
    ⟪sphereBoost v a x, v⟫ = (sinh a + cosh a * ⟪x, v⟫) / (cosh a + sinh a * ⟪x, v⟫) := by
  rw [sphereBoost_def, real_inner_smul_left, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, hv, div_eq_inv_mul]
  ring

/-- **Boosts preserve the unit sphere.** -/
@[simp]
theorem norm_sphereBoost {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (a : ℝ) :
    ‖sphereBoost v a x‖ = 1 := by
  have hD := cosh_add_sinh_mul_inner_pos hv hx a
  -- `‖x + c v‖² = 1 + 2 c ⟪x, v⟫ + c²` is the square of the denominator since
  -- `cosh² a - sinh² a = 1`: the boost preserves the Lorentz form.
  have hN : ‖x + (sinh a + (cosh a - 1) * ⟪x, v⟫) • v‖ = cosh a + sinh a * ⟪x, v⟫ := by
    rw [← sq_eq_sq₀ (norm_nonneg _) hD.le, norm_add_sq_real, norm_smul, real_inner_smul_right, hx,
      hv, Real.norm_eq_abs, mul_one, sq_abs]
    linear_combination (⟪x, v⟫ ^ 2 - 1) * cosh_sq a
  rw [sphereBoost_def, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hD, hN,
    inv_mul_cancel₀ hD.ne']

/-- **Rapidities add.** On the unit sphere, boosting by `b` and then by `a` toward the same unit
vector is boosting by `a + b`. -/
theorem sphereBoost_sphereBoost {v x : E} (hv : ‖v‖ = 1) (hx : ‖x‖ = 1) (a b : ℝ) :
    sphereBoost v a (sphereBoost v b x) = sphereBoost v (a + b) x := by
  have hD := cosh_add_sinh_mul_inner_pos hv hx b
  rw [sphereBoost_def v a, inner_sphereBoost hv b x, sphereBoost_def v b, sphereBoost_def v (a + b)]
  generalize ⟪x, v⟫ = s at hD ⊢
  set D := cosh b + sinh b * s
  -- Both sides are combinations of `x` and `v`; compare the coefficients.
  have hden : (cosh a + sinh a * ((sinh b + cosh b * s) / D))⁻¹ * D⁻¹ =
      (cosh (a + b) + sinh (a + b) * s)⁻¹ := by
    rw [← mul_inv, cosh_add, sinh_add]
    congr 1
    field_simp
    ring
  have hnum : D⁻¹ * (sinh b + (cosh b - 1) * s) +
      (sinh a + (cosh a - 1) * ((sinh b + cosh b * s) / D)) =
        D⁻¹ * (sinh (a + b) + (cosh (a + b) - 1) * s) := by
    rw [cosh_add, sinh_add]
    field_simp
    ring
  calc (cosh a + sinh a * ((sinh b + cosh b * s) / D))⁻¹ •
        (D⁻¹ • (x + (sinh b + (cosh b - 1) * s) • v) +
          (sinh a + (cosh a - 1) * ((sinh b + cosh b * s) / D)) • v)
      = ((cosh a + sinh a * ((sinh b + cosh b * s) / D))⁻¹ * D⁻¹) • x +
          ((cosh a + sinh a * ((sinh b + cosh b * s) / D))⁻¹ *
            (D⁻¹ * (sinh b + (cosh b - 1) * s) +
              (sinh a + (cosh a - 1) * ((sinh b + cosh b * s) / D)))) • v := by module
    _ = (cosh (a + b) + sinh (a + b) * s)⁻¹ •
          (x + (sinh (a + b) + (cosh (a + b) - 1) * s) • v) := by
        rw [hnum, ← mul_assoc (cosh a + sinh a * ((sinh b + cosh b * s) / D))⁻¹ D⁻¹, hden,
          smul_add, smul_smul]

/-- The boost toward `v` fixes `v`. -/
@[simp]
theorem sphereBoost_self {v : E} (hv : ‖v‖ = 1) (a : ℝ) : sphereBoost v a v = v := by
  have h : cosh a + sinh a ≠ 0 := by rw [cosh_add_sinh]; positivity
  simp only [sphereBoost_def, real_inner_self_eq_norm_sq, hv, one_pow, mul_one]
  match_scalars
  field_simp
  ring

/-- The boost toward `v` fixes `-v`. -/
@[simp]
theorem sphereBoost_neg_self {v : E} (hv : ‖v‖ = 1) (a : ℝ) : sphereBoost v a (-v) = -v := by
  have h : cosh a - sinh a ≠ 0 := by rw [cosh_sub_sinh]; positivity
  simp only [sphereBoost_def, inner_neg_left, real_inner_self_eq_norm_sq, hv, one_pow, mul_neg,
    mul_one, ← sub_eq_add_neg]
  match_scalars
  field_simp
  ring

/-- **Boosts commute with linear isometries.** -/
theorem _root_.LinearIsometry.sphereBoost_map (ι : F →ₗᵢ[ℝ] E) (w : F) (a : ℝ) (x : F) :
    sphereBoost (ι w) a (ι x) = ι (sphereBoost w a x) := by
  simp only [sphereBoost_def, ι.inner_map_map, map_smul, map_add]

/-- **Boosts attract toward `v`.** A compact subset of the unit sphere avoiding `-v` is carried
into the open hemisphere `⟪x, v⟫ > 0` by every boost toward `v` of large enough rapidity. -/
theorem _root_.IsCompact.eventually_forall_inner_sphereBoost_pos {C : Set E} (hC : IsCompact C)
    {v : E} (hv : ‖v‖ = 1) (hC₁ : ∀ x ∈ C, ‖x‖ = 1) (hCv : -v ∉ C) :
    ∀ᶠ a in Filter.atTop, ∀ x ∈ C, 0 < ⟪sphereBoost v a x, v⟫ := by
  -- On `C` the height is bounded below by some `-1 + ε` with `ε > 0`.
  obtain ⟨b, hb, hbC⟩ := hC.exists_forall_le' (a := -1) (f := fun x => ⟪x, v⟫)
    (continuous_id.inner continuous_const).continuousOn fun x hx =>
      (neg_one_le_real_inner_of_norm_eq_one (hC₁ x hx) hv).lt_of_ne fun h =>
        hCv (((inner_eq_neg_one_iff_of_norm_eq_one (hC₁ x hx) hv).1 h.symm) ▸ hx)
  have hε : 0 < b + 1 := by linarith
  filter_upwards [Filter.eventually_gt_atTop (-log (b + 1))] with a ha x hx
  rw [inner_sphereBoost hv]
  refine div_pos ?_ (cosh_add_sinh_mul_inner_pos hv (hC₁ x hx) a)
  -- `sinh a + cosh a s ≥ (b + 1) cosh a - e⁻ᵃ > 0`, as `cosh a ≥ 1` and `e⁻ᵃ < b + 1`.
  have hexp : exp (-a) < b + 1 := by
    calc exp (-a) < exp (log (b + 1)) := exp_lt_exp.2 (by linarith)
      _ = b + 1 := exp_log hε
  have hcs := cosh_sub_sinh a
  nlinarith [mul_le_mul_of_nonneg_left (hbC x hx) (cosh_pos a).le, one_le_cosh a]

end TauCeti
