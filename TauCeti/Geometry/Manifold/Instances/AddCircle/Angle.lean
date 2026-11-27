/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Geometry.Manifold.Instances.AddCircle
public import TauCeti.Geometry.Manifold.IsManifold.Pi
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Topology.Circle.AddCircle

/-!
# The cosine and sine of the angles of a torus

On the torus `(ℝ / 2πℤ)^ι = ∀ _ : ι, AddCircle (2π)`, modelled on
`ModelWithCorners.pi fun _ ↦ 𝓘(ℝ)` with tangent spaces `ι → ℝ`, each coordinate `xᵢ` is an angle
modulo `2π`. Its cosine and sine, the real and imaginary parts of `xᵢ` on the unit circle
(`AddCircle.toCircle`), are the smooth functions `TauCeti.torusAngleCos ι i` and
`TauCeti.torusAngleSin ι i`. At the class of a real vector `t` they are `cos tᵢ` and `sin tᵢ`, and
their differentials are `-sin xᵢ dxᵢ` and `cos xᵢ dxᵢ`. They are the coefficients of the
trigonometric differential forms of the torus, such as the exact form `cos θ dθ ∧ dφ = d (sin θ dφ)`
of the two-torus.

## Main definitions

* `TauCeti.torusAngleCos ι i`, `TauCeti.torusAngleSin ι i`: the smooth functions `x ↦ cos xᵢ` and
  `x ↦ sin xᵢ`.

## Main results

* `TauCeti.torusAngleCos_coe`, `TauCeti.torusAngleSin_coe`: their values at the class of a real
  vector.
* `TauCeti.mvfderiv_torusAngleCos`, `TauCeti.mvfderiv_torusAngleSin`: their differentials.
* `TauCeti.abs_torusAngleCos_le_one`, `TauCeti.abs_torusAngleSin_le_one`: both lie in `[-1, 1]`.
-/

public section

open Filter AddCircle
open scoped ContDiff Manifold Real Topology

namespace TauCeti

/-- The period `2π` is positive. -/
local instance torusAngleTwoPiPos : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

section Angle

variable {ι : Type*} [Fintype ι]

/-- On the circle `ℝ / 2πℤ`, the real part of the class of `s` on the unit circle is `cos s`. -/
private theorem re_toCircle_coe_two_pi (s : ℝ) :
    (toCircle (s : AddCircle (2 * π)) : ℂ).re = Real.cos s := by
  rw [re_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul]

/-- On the circle `ℝ / 2πℤ`, the imaginary part of the class of `s` on the unit circle is
`sin s`. -/
private theorem im_toCircle_coe_two_pi (s : ℝ) :
    (toCircle (s : AddCircle (2 * π)) : ℂ).im = Real.sin s := by
  rw [im_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul]

/-- In the preferred chart at `x`, a function `f` of the torus `(ℝ / 2πℤ)^ι` whose value at the
class of every real vector `t` is `h tᵢ` is read as `y ↦ h yᵢ`. -/
private theorem comp_extChartAt_symm_eventuallyEq {f : (∀ _ : ι, AddCircle (2 * π)) → ℝ}
    {h : ℝ → ℝ} {i : ι} (hf : ∀ t : ι → ℝ, f (fun j ↦ (t j : AddCircle (2 * π))) = h (t i))
    (x : ∀ _ : ι, AddCircle (2 * π)) :
    f ∘ (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm
      =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x)] fun y ↦ h (y i) := by
  filter_upwards [extChartAt_target_mem_nhds (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x]
    with y hy
  rw [Function.comp_apply, extChartAt_pi_symm_apply x hy, hf]

/-- A function `f` of the torus `(ℝ / 2πℤ)^ι` whose value at the class of every real vector `t` is
`h tᵢ` takes the value `h` at the `i`-th coordinate of the chart point of `x`. -/
private theorem apply_eq_extChartAt {f : (∀ _ : ι, AddCircle (2 * π)) → ℝ} {h : ℝ → ℝ} {i : ι}
    (hf : ∀ t : ι → ℝ, f (fun j ↦ (t j : AddCircle (2 * π))) = h (t i))
    (x : ∀ _ : ι, AddCircle (2 * π)) :
    f x = h (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) := by
  have := (comp_extChartAt_symm_eventuallyEq hf x).self_of_nhds
  rwa [Function.comp_apply, extChartAt_to_inv] at this

variable (ι) in
/-- The cosine `x ↦ cos xᵢ` of the `i`-th angle of the torus `(ℝ / 2πℤ)^ι`, as a smooth
function. -/
noncomputable def torusAngleCos (i : ι) :
    C^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ), ∀ _ : ι, AddCircle (2 * π); ℝ⟯ :=
  ⟨fun x ↦ (toCircle (x i) : ℂ).re, fun x ↦
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
      ContDiffAt.congr_of_eventuallyEq (by fun_prop)
        (comp_extChartAt_symm_eventuallyEq (h := Real.cos)
          (fun t ↦ re_toCircle_coe_two_pi (t i)) x)⟩

variable (ι) in
/-- The sine `x ↦ sin xᵢ` of the `i`-th angle of the torus `(ℝ / 2πℤ)^ι`, as a smooth function. -/
noncomputable def torusAngleSin (i : ι) :
    C^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ), ∀ _ : ι, AddCircle (2 * π); ℝ⟯ :=
  ⟨fun x ↦ (toCircle (x i) : ℂ).im, fun x ↦
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
      ContDiffAt.congr_of_eventuallyEq (by fun_prop)
        (comp_extChartAt_symm_eventuallyEq (h := Real.sin)
          (fun t ↦ im_toCircle_coe_two_pi (t i)) x)⟩

/-- The cosine of the `i`-th angle is the real part of the `i`-th coordinate on the unit circle. -/
theorem torusAngleCos_apply (i : ι) (x : ∀ _ : ι, AddCircle (2 * π)) :
    torusAngleCos ι i x = (toCircle (x i) : ℂ).re :=
  (rfl)

/-- The sine of the `i`-th angle is the imaginary part of the `i`-th coordinate on the unit
circle. -/
theorem torusAngleSin_apply (i : ι) (x : ∀ _ : ι, AddCircle (2 * π)) :
    torusAngleSin ι i x = (toCircle (x i) : ℂ).im :=
  (rfl)

/-- The cosine of the `i`-th angle at the class of a real vector `t` is `cos tᵢ`. -/
@[simp]
theorem torusAngleCos_coe (i : ι) (t : ι → ℝ) :
    torusAngleCos ι i (fun j ↦ (t j : AddCircle (2 * π))) = Real.cos (t i) := by
  rw [torusAngleCos_apply, re_toCircle_coe_two_pi]

/-- The sine of the `i`-th angle at the class of a real vector `t` is `sin tᵢ`. -/
@[simp]
theorem torusAngleSin_coe (i : ι) (t : ι → ℝ) :
    torusAngleSin ι i (fun j ↦ (t j : AddCircle (2 * π))) = Real.sin (t i) := by
  rw [torusAngleSin_apply, im_toCircle_coe_two_pi]

omit [Fintype ι] in
/-- The covector `c • proj i` of `ι → ℝ` sends `w` to `c * wᵢ`. -/
private theorem smul_proj_apply (c : ℝ) (i : ι) (w : ι → ℝ) :
    (c • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i) w = c * w i := by
  rw [smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]

/-- A function `f` of the torus `(ℝ / 2πℤ)^ι` whose value at the class of every real vector `t` is
`h tᵢ`, for `h` with derivative `h'`, has differential `g x dxᵢ`, where `g` is the function whose
value at the class of `t` is `h' tᵢ`. -/
private theorem mvfderiv_apply_of_coe {f g : (∀ _ : ι, AddCircle (2 * π)) → ℝ} {h h' : ℝ → ℝ}
    {i : ι} (hf : ∀ t : ι → ℝ, f (fun j ↦ (t j : AddCircle (2 * π))) = h (t i))
    (hg : ∀ t : ι → ℝ, g (fun j ↦ (t j : AddCircle (2 * π))) = h' (t i))
    (hh : ∀ s, HasDerivAt h (h' s) s) (x : ∀ _ : ι, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) f x v = g x * v i := by
  have hd : HasFDerivAt (fun y : ι → ℝ ↦ h (y i))
      (h' (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) •
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι ↦ ℝ) i)
      (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x) :=
    (hh _).comp_hasFDerivAt _ (hasFDerivAt_apply i _)
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm, (comp_extChartAt_symm_eventuallyEq hf x).fderiv_eq,
    hd.fderiv, ← apply_eq_extChartAt hg x]
  -- The tangent vector `v` is a vector of `ι → ℝ`.
  exact smul_proj_apply _ i v

/-- The cosine of the `i`-th angle has differential `-sin xᵢ dxᵢ`. -/
theorem mvfderiv_torusAngleCos (i : ι) (x : ∀ _ : ι, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusAngleCos ι i) x v =
      -torusAngleSin ι i x * v i :=
  mvfderiv_apply_of_coe (torusAngleCos_coe i) (g := fun x ↦ -torusAngleSin ι i x)
    (fun t ↦ by rw [torusAngleSin_coe]) Real.hasDerivAt_cos x v

/-- The sine of the `i`-th angle has differential `cos xᵢ dxᵢ`. -/
theorem mvfderiv_torusAngleSin (i : ι) (x : ∀ _ : ι, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusAngleSin ι i) x v =
      torusAngleCos ι i x * v i :=
  mvfderiv_apply_of_coe (torusAngleSin_coe i) (torusAngleCos_coe i) Real.hasDerivAt_sin x v

/-- The cosine of an angle of the torus lies in `[-1, 1]`. -/
theorem abs_torusAngleCos_le_one (i : ι) (x : ∀ _ : ι, AddCircle (2 * π)) :
    |torusAngleCos ι i x| ≤ 1 := by
  rw [torusAngleCos_apply]
  exact (Complex.abs_re_le_norm _).trans (by simp)

/-- The sine of an angle of the torus lies in `[-1, 1]`. -/
theorem abs_torusAngleSin_le_one (i : ι) (x : ∀ _ : ι, AddCircle (2 * π)) :
    |torusAngleSin ι i x| ≤ 1 := by
  rw [torusAngleSin_apply]
  exact (Complex.abs_im_le_norm _).trans (by simp)

end Angle

end TauCeti
