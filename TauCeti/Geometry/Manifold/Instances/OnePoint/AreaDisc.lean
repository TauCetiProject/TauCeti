/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.Geometry.Manifold.DifferentialForm.MapCoeff
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Symplectic.Complex.Line
import TauCeti.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph
import TauCeti.Geometry.Manifold.LocalDiffeomorph.MFDeriv

/-!
# The sphere of area `a` minus a point is the disc of area `a`

For `a > 0`, scaling the Fubini–Study form `ω_FS` of the Riemann sphere `OnePoint ℂ`, which has
total area one, gives the sphere `S²(a)` of area `a` with the symplectic form `a • ω_FS`. This file
shows that `S²(a)` minus the point `∞` is symplectomorphic to the open disc of area `a` in `ℂ`,
the disc of radius `√(a / π)`, with its standard area form `dx ∧ dy`
(`TauCeti.stdComplexSymplecticForm`).

The symplectomorphism is the partial diffeomorphism `OnePoint.areaDiscChart a`, defined on the
complement of `∞`. In the affine coordinate it is the radial map

`z ↦ √(a / π) z / √(1 + |z|²)`  (`OnePoint.areaDiscChart_coe`),

which is Mathlib's diffeomorphism `OpenPartialHomeomorph.univBall 0 √(a / π)` of `ℂ` onto the open
disc. Its inverse is `y ↦ y / √(a / π - |y|²)` (`OnePoint.areaDiscChart_symm_apply`). It is a
Darboux chart: it pulls `dx ∧ dy` back to `a • ω_FS`
(`OnePoint.eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart`). Equivalently, its inverse
embeds the open disc of area `a` symplectically into `S²(a)`, with image the complement of `∞`
(`OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm`).

The computation is in the affine coordinate. Write `t = |z|²` and `r = √(a / π)`. The derivative
of the radial map is `v ↦ α v - β ⟪z, v⟫ z` with `α = r / √(1 + t)` and `β = r / √(1 + t)³`, and
such a map scales the area form by `α (α - β t) = r² / (1 + t)²`. Since `r² = a / π`, this is
`a ρ(z)`, where `ρ(z) = 1 / (π (1 + t)²)` is the density of `ω_FS`.

The disc of radius `R` sits in the sphere `S²(a)` whenever `π R² ≤ a`. This is the
two-dimensional factor of the symplectic embedding of a ball of radius `R` in the cylinder
`{z ∈ ℂⁿ | |z₀| < R}` into the product `S²(a) × T²ⁿ⁻²`, through which Gromov's nonsqueezing
theorem is proved by counting holomorphic spheres.

## Main declarations

* `OnePoint.areaDiscChart`: the partial diffeomorphism of `OnePoint ℂ` minus `∞` onto the disc of
  area `a`.
* `OnePoint.eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart`: it pulls the standard area form
  back to `a • ω_FS`.
* `OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm`: its inverse embeds the open
  disc of area `a` symplectically into the sphere of area `a`.
* `OnePoint.volume_areaDiscChart_target`: the disc it maps onto has area `a`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. **82** (1985),
  307–347, §0.3.A (the nonsqueezing theorem).
-/

public section

open Set Metric ComplexConjugate TauCeti
open scoped Manifold InnerProductSpace TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

/-- **The disc chart of the sphere of area `a`.** The partial diffeomorphism of the Riemann sphere
minus `∞` onto `ℂ` given in the affine coordinate by Mathlib's radial map
`OpenPartialHomeomorph.univBall 0 √(a / π)`. For `a > 0` it is `z ↦ √(a / π) z / √(1 + |z|²)`
(`OnePoint.areaDiscChart_coe`), its target is the open disc of radius `√(a / π)`, which has area
`a` (`OnePoint.volume_areaDiscChart_target`), and it carries `a • ω_FS` to the standard area form
(`OnePoint.eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart`). For `a ≤ 0` it is the affine
chart. -/
-- The smoothness exponent `((⊤ : ℕ∞) : WithTop ℕ∞)` is the value of the notation `∞` of
-- `ContDiff`; inside the namespace `OnePoint` the symbol `∞` denotes the point at infinity.
def areaDiscChart (a : ℝ) :
    PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ ((⊤ : ℕ∞) : WithTop ℕ∞) where
  toPartialEquiv :=
    (affineChart.trans (OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi))).toPartialEquiv
  open_source := (affineChart.trans _).open_source
  open_target := (affineChart.trans _).open_target
  contMDiffOn_toFun := by
    have h : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (affineChart : OnePoint ℂ → ℂ)
        {(∞ : OnePoint ℂ)}ᶜ := by
      simpa [chartAt_coe] using
        contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))
          (x := ((0 : ℂ) : OnePoint ℂ))
    refine (OpenPartialHomeomorph.contDiff_univBall.contMDiff.comp_contMDiffOn h).mono ?_
    rw [OpenPartialHomeomorph.trans_source, affineChart_source]
    exact inter_subset_left
  contMDiffOn_invFun := by
    have hs : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi)).symm
        (OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi)).target := by
      by_cases hr : 0 < √(a / Real.pi)
      · rw [OpenPartialHomeomorph.univBall_target _ hr]
        exact OpenPartialHomeomorph.contDiffOn_univBall_symm.contMDiffOn
      · -- For a nonpositive radius, `univBall` is the translation by the center `0`.
        rw [OpenPartialHomeomorph.univBall, dite_eq_right hr]
        exact (contMDiff_id.contMDiffOn (s := univ)).congr fun y _ ↦ by simp
    have hsub : (affineChart.trans
        (OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi))).target ⊆
          (OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi)).target := by
      rw [OpenPartialHomeomorph.trans_target]
      exact inter_subset_left
    refine (contMDiff_coe_real.comp_contMDiffOn (hs.mono hsub)).congr fun y _ ↦ ?_
    simp [affineChart_symm_apply]

/-- The disc chart is the radial map `OpenPartialHomeomorph.univBall 0 √(a / π)` read in the
affine coordinate. -/
theorem areaDiscChart_apply (a : ℝ) (x : OnePoint ℂ) :
    areaDiscChart a x = OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi) (affineChart x) :=
  (rfl)

/-- The inverse of the disc chart is the inverse of the radial map, followed by the inclusion of
`ℂ` in the Riemann sphere. -/
theorem areaDiscChart_symm_apply_eq_coe (a : ℝ) (y : ℂ) :
    (areaDiscChart a).symm y =
      ((OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi)).symm y : OnePoint ℂ) :=
  affineChart_symm_apply _

/-- The disc chart is defined on the complement of `∞`. -/
@[simp]
theorem areaDiscChart_source (a : ℝ) : (areaDiscChart a).source = {(∞ : OnePoint ℂ)}ᶜ := by
  simp [areaDiscChart]

private theorem sqrt_div_pi_pos {a : ℝ} (ha : 0 < a) : 0 < √(a / Real.pi) :=
  Real.sqrt_pos.2 (div_pos ha Real.pi_pos)

/-- For `a > 0`, the disc chart maps onto the open disc of radius `√(a / π)`. -/
theorem areaDiscChart_target {a : ℝ} (ha : 0 < a) :
    (areaDiscChart a).target = ball 0 √(a / Real.pi) := by
  simp [areaDiscChart, OpenPartialHomeomorph.univBall_target _ (sqrt_div_pi_pos ha)]

/-- For `a > 0`, a point lies in the target of the disc chart exactly when its norm is less than
`√(a / π)`. -/
theorem mem_areaDiscChart_target {a : ℝ} (ha : 0 < a) {y : ℂ} :
    y ∈ (areaDiscChart a).target ↔ ‖y‖ < √(a / Real.pi) := by
  rw [areaDiscChart_target ha, mem_ball_zero_iff]

/-- **The disc of the disc chart has area `a`.** -/
theorem volume_areaDiscChart_target {a : ℝ} (ha : 0 < a) :
    MeasureTheory.volume (areaDiscChart a).target = ENNReal.ofReal a := by
  rw [areaDiscChart_target ha, Complex.volume_ball, ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  simp [Real.sq_sqrt (div_pos ha Real.pi_pos).le, Real.pi_ne_zero]

/-- The disc chart in the affine coordinate: `z ↦ √(a / π) z / √(1 + |z|²)`. -/
theorem areaDiscChart_coe {a : ℝ} (ha : 0 < a) (z : ℂ) :
    areaDiscChart a z = (√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • z := by
  rw [areaDiscChart_apply, affineChart_coe,
    OpenPartialHomeomorph.univBall_apply (sqrt_div_pi_pos ha), vadd_eq_add, add_zero]

/-- The inverse of the disc chart: `y ↦ y / √(a / π - |y|²)`, a point of the affine part of the
sphere when `|y| < √(a / π)`. -/
theorem areaDiscChart_symm_apply {a : ℝ} (ha : 0 < a) (y : ℂ) :
    (areaDiscChart a).symm y = (((√(a / Real.pi - ‖y‖ ^ 2))⁻¹ • y : ℂ) : OnePoint ℂ) := by
  rw [areaDiscChart_symm_apply_eq_coe,
    OpenPartialHomeomorph.univBall_symm_apply (sqrt_div_pi_pos ha), vsub_eq_sub, sub_zero,
    dist_zero_right,
    Real.sq_sqrt (div_pos ha Real.pi_pos).le]

/-- **The derivative of the disc chart** at a finite point `z`:
`v ↦ α v - β ⟪z, v⟫ z` with `α = √(a / π) / √(1 + |z|²)` and `β = √(a / π) / √(1 + |z|²)³`. -/
theorem mvfderiv_areaDiscChart_coe {a : ℝ} (ha : 0 < a) (z v : ℂ) :
    mvfderiv 𝓘(ℝ, ℂ) (areaDiscChart a) (z : OnePoint ℂ) v =
      (√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • v -
        (√(a / Real.pi) / √(1 + ‖z‖ ^ 2) ^ 3 * ⟪z, v⟫_ℝ) • z := by
  have hd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (areaDiscChart a) (z : OnePoint ℂ) :=
    (areaDiscChart a).mdifferentiableAt (by simp) (by simp)
  have hf := OpenPartialHomeomorph.hasFDerivAt_univBall (sqrt_div_pi_pos ha) 0 z
  have hw : writtenInExtChartAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (z : OnePoint ℂ) (areaDiscChart a) =
      OpenPartialHomeomorph.univBall (0 : ℂ) √(a / Real.pi) := by
    funext w
    simp [writtenInExtChartAt, chartAt_coe, areaDiscChart_apply]
  refine (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans ?_
  rw [hd.mfderiv, hw]
  simp only [modelWithCornersSelf_coe, range_id, fderivWithin_univ, extChartAt_coe, chartAt_coe,
    Function.comp_apply, id_eq, affineChart_coe, hf.fderiv]
  -- The tangent spaces of `OnePoint ℂ` and of `ℂ` are `ℂ` itself, and the casts are identities.
  exact (by simp only [sub_apply, smul_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul] :
    ((√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • ContinuousLinearMap.id ℝ ℂ -
      (√(a / Real.pi) / √(1 + ‖z‖ ^ 2) ^ 3) • (innerSL ℝ z).smulRight z) v =
      (√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • v -
        (√(a / Real.pi) / √(1 + ‖z‖ ^ 2) ^ 3 * ⟪z, v⟫_ℝ) • z)

/-- The pointwise identity behind `eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart`, in the
affine coordinate `z`: `a ρ(z) Im (conj v * w)` is the area of the images of `v` and `w` under the
derivative of the disc chart. -/
private theorem smul_fubiniStudyDensity_mul_eq {a : ℝ} (ha : 0 < a) (z v w : ℂ) :
    a • (fubiniStudyDensity z * (conj v * w).im) =
      stdComplexSymplecticForm
        ((√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • v -
          (√(a / Real.pi) / √(1 + ‖z‖ ^ 2) ^ 3 * ⟪z, v⟫_ℝ) • z)
        ((√(a / Real.pi) / √(1 + ‖z‖ ^ 2)) • w -
          (√(a / Real.pi) / √(1 + ‖z‖ ^ 2) ^ 3 * ⟪z, w⟫_ℝ) • z) := by
  rw [stdComplexSymplecticForm_smul_sub_smul, stdComplexSymplecticForm_apply,
    fubiniStudyDensity_def, smul_eq_mul, Complex.mul_im, Complex.conj_re, Complex.conj_im]
  set s := √(1 + ‖z‖ ^ 2)
  set r := √(a / Real.pi)
  have hS : s ^ 2 = 1 + ‖z‖ ^ 2 := Real.sq_sqrt (by positivity)
  have hr : r ^ 2 = a / Real.pi := Real.sq_sqrt (div_pos ha Real.pi_pos).le
  have hS0 : s ≠ 0 := (Real.sqrt_pos.2 (by positivity)).ne'
  -- The scaling factor `α (α - β |z|²)` is `r² (s² - |z|²) / s⁴`, and `s² - |z|² = 1`.
  have hcoef : r / s * (r / s - r / s ^ 3 * ‖z‖ ^ 2) = a * (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹ :=
    calc r / s * (r / s - r / s ^ 3 * ‖z‖ ^ 2) = r ^ 2 * (s ^ 2 - ‖z‖ ^ 2) / (s ^ 2) ^ 2 := by
          field_simp
      _ = a * (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹ := by
          rw [hS, hr, add_sub_cancel_right, mul_one, div_div, div_eq_mul_inv]
  rw [hcoef]
  ring

/-- **The disc chart is a Darboux chart for `a • ω_FS`.** For `a > 0`, the standard area form
`dx ∧ dy` of `ℂ` pulls back along the disc chart to the Fubini–Study form scaled to total area
`a`: at every point `x ≠ ∞`, `a ω_FS(v, w) = dx ∧ dy (dφ v, dφ w)`. So the sphere of area `a`
minus a point is symplectomorphic to the open disc of area `a`. -/
theorem eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart {a : ℝ} (ha : 0 < a) :
    ∀ x ∈ (areaDiscChart a).source, ∀ v w : TangentSpace 𝓘(ℝ, ℂ) x,
      (a • fubiniStudyForm).eval₂ x v w =
        stdComplexSymplecticForm (mvfderiv 𝓘(ℝ, ℂ) (areaDiscChart a) x v)
          (mvfderiv 𝓘(ℝ, ℂ) (areaDiscChart a) x w) := by
  intro x hx v w
  obtain ⟨z, rfl⟩ := ne_infty_iff_exists.1 (by simpa using hx)
  -- Tangent vectors at finite points of `OnePoint ℂ` are complex numbers.
  rw [SmoothForm.eval₂_smul, eval₂_fubiniStudyForm_coe z v w, mvfderiv_areaDiscChart_coe ha z v,
    mvfderiv_areaDiscChart_coe ha z w]
  exact smul_fubiniStudyDensity_mul_eq ha z v w

/-- **The disc of area `a` embeds symplectically into the sphere of area `a`.** For `a > 0` and
`|y| < √(a / π)`, the inverse of the disc chart pulls `a • ω_FS` back to the standard area form at
`y`. Its image is the sphere minus `∞`. -/
theorem eval₂_smul_fubiniStudyForm_mfderiv_areaDiscChart_symm {a : ℝ} (ha : 0 < a) {y : ℂ}
    (hy : ‖y‖ < √(a / Real.pi)) (v w : TangentSpace 𝓘(ℝ, ℂ) y) :
    (a • fubiniStudyForm).eval₂ ((areaDiscChart a).symm y)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (areaDiscChart a).symm y v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (areaDiscChart a).symm y w) =
      stdComplexSymplecticForm v w := by
  have hy' : y ∈ (areaDiscChart a).target := (mem_areaDiscChart_target ha).2 hy
  have hinv (u : TangentSpace 𝓘(ℝ, ℂ) y) :
      mvfderiv 𝓘(ℝ, ℂ) (areaDiscChart a) ((areaDiscChart a).symm y)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (areaDiscChart a).symm y u) = u :=
    (mvfderiv_apply_eq_mfderiv_apply _ _ _).trans
      ((areaDiscChart a).mfderiv_apply_mfderiv_symm_apply (by simp) hy' u)
  exact (eval₂_smul_fubiniStudyForm_eq_mvfderiv_areaDiscChart ha _
    ((areaDiscChart a).map_target hy') _ _).trans
    (congrArg₂ (fun v' w' : ℂ ↦ stdComplexSymplecticForm v' w') (hinv v) (hinv w))

end OnePoint
