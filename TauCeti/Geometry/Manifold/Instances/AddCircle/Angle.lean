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
local instance : Fact (0 < 2 * π) := ⟨Real.two_pi_pos⟩

section Angle

variable {ι : Type*} [Fintype ι]

/-- In the preferred chart at `x`, a function of the `i`-th angle of the torus `(ℝ / 2πℤ)^ι` given
by `g ∘ toCircle` is read as `y ↦ g (exp (i yᵢ))`. -/
private theorem comp_extChartAt_symm_eventuallyEq (g : Circle → ℝ) (i : ι)
    (x : ∀ _ : ι, AddCircle (2 * π)) :
    (fun z : ∀ _ : ι, AddCircle (2 * π) ↦ g (toCircle (z i))) ∘
        (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x).symm
      =ᶠ[𝓝 (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x)]
      fun y ↦ g (toCircle (y i : AddCircle (2 * π))) := by
  filter_upwards [extChartAt_target_mem_nhds (I := ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x]
    with y hy
  rw [Function.comp_apply, extChartAt_pi_symm_apply x hy]

variable (ι) in
/-- The cosine `x ↦ cos xᵢ` of the `i`-th angle of the torus `(ℝ / 2πℤ)^ι`, as a smooth
function. -/
noncomputable def torusAngleCos (i : ι) :
    C^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ), ∀ _ : ι, AddCircle (2 * π); ℝ⟯ :=
  ⟨fun x ↦ (toCircle (x i) : ℂ).re, fun x ↦
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
      ContDiffAt.congr_of_eventuallyEq
        (by simp only [re_toCircle_coe]; fun_prop)
        (comp_extChartAt_symm_eventuallyEq (fun z ↦ (z : ℂ).re) i x)⟩

variable (ι) in
/-- The sine `x ↦ sin xᵢ` of the `i`-th angle of the torus `(ℝ / 2πℤ)^ι`, as a smooth function. -/
noncomputable def torusAngleSin (i : ι) :
    C^∞⟮ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ), ∀ _ : ι, AddCircle (2 * π); ℝ⟯ :=
  ⟨fun x ↦ (toCircle (x i) : ℂ).im, fun x ↦
    contMDiffAt_iff_contDiffAt_comp_extChartAt_symm.2 <|
      ContDiffAt.congr_of_eventuallyEq
        (by simp only [im_toCircle_coe]; fun_prop)
        (comp_extChartAt_symm_eventuallyEq (fun z ↦ (z : ℂ).im) i x)⟩

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
  rw [torusAngleCos_apply, re_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul]

/-- The sine of the `i`-th angle at the class of a real vector `t` is `sin tᵢ`. -/
@[simp]
theorem torusAngleSin_coe (i : ι) (t : ι → ℝ) :
    torusAngleSin ι i (fun j ↦ (t j : AddCircle (2 * π))) = Real.sin (t i) := by
  rw [torusAngleSin_apply, im_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul]

/-- Read in the preferred chart at `x`, the `i`-th angle of `x` is the `i`-th coordinate of its
chart point, so its cosine and sine are those of that coordinate. -/
private theorem torusAngleCos_torusAngleSin_eq_extChartAt (i : ι)
    (x : ∀ _ : ι, AddCircle (2 * π)) :
    torusAngleCos ι i x = Real.cos (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) ∧
      torusAngleSin ι i x =
        Real.sin (extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x i) := by
  have hx : x = fun j ↦ ((extChartAt (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x x j : ℝ) :
      AddCircle (2 * π)) := by
    rw [← extChartAt_pi_symm_apply x (mem_extChartAt_target x),
      (extChartAt _ x).left_inv (mem_extChartAt_source x)]
  constructor
  · conv_lhs => rw [hx]
    exact torusAngleCos_coe i _
  · conv_lhs => rw [hx]
    exact torusAngleSin_coe i _

/-- The cosine of the `i`-th angle has differential `-sin xᵢ dxᵢ`. -/
theorem mvfderiv_torusAngleCos (i : ι) (x : ∀ _ : ι, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusAngleCos ι i) x v =
      -torusAngleSin ι i x * v i := by
  have heq := comp_extChartAt_symm_eventuallyEq (fun z ↦ (z : ℂ).re) i x
  simp only [re_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul] at heq
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm]
  -- `erw`: the coercion of the bundled smooth map unfolds to the function read by `heq`.
  erw [heq.fderiv_eq, (hasFDerivAt_apply i _).cos.fderiv]
  rw [(torusAngleCos_torusAngleSin_eq_extChartAt i x).2]
  -- The derivative `(-sin yᵢ) • proj i` evaluates to `-sin yᵢ * vᵢ` by definition.
  rfl

/-- The sine of the `i`-th angle has differential `cos xᵢ dxᵢ`. -/
theorem mvfderiv_torusAngleSin (i : ι) (x : ∀ _ : ι, AddCircle (2 * π))
    (v : TangentSpace (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) x) :
    mvfderiv (ModelWithCorners.pi fun _ : ι ↦ 𝓘(ℝ)) (torusAngleSin ι i) x v =
      torusAngleCos ι i x * v i := by
  have heq := comp_extChartAt_symm_eventuallyEq (fun z ↦ (z : ℂ).im) i x
  simp only [im_toCircle_coe, div_self Real.two_pi_pos.ne', one_mul] at heq
  rw [mvfderiv_eq_fderiv_comp_extChartAt_symm]
  -- `erw`: the coercion of the bundled smooth map unfolds to the function read by `heq`.
  erw [heq.fderiv_eq, (hasFDerivAt_apply i _).sin.fderiv]
  rw [(torusAngleCos_torusAngleSin_eq_extChartAt i x).1]
  -- The derivative `cos yᵢ • proj i` evaluates to `cos yᵢ * vᵢ` by definition.
  rfl

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
