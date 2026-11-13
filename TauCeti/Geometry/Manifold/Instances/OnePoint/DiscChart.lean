/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.LocalDiffeomorph
public import TauCeti.Geometry.Manifold.Instances.OnePoint.FubiniStudy
public import TauCeti.Geometry.Symplectic.Complex.Radial
import TauCeti.Analysis.InnerProductSpace.Radial
import TauCeti.Analysis.Normed.Module.Ball.Homeomorph

/-!
# The sphere of area `π r²` minus a point is the open disc of radius `r`

The Riemann sphere `OnePoint ℂ` with the Fubini–Study form `ω_FS` (`OnePoint.fubiniStudyForm`) has
total area one, so `a • ω_FS` is the area form of the sphere `S²(a)` of area `a`. This file shows
that `S²(π r²)` with the point `∞` removed is symplectomorphic to the open disc of radius `r` in `ℂ`
with its standard area form `dx ∧ dy` (`TauCeti.stdComplexSymplecticForm`), for every `r > 0`. The
symplectomorphism is a global chart of the punctured sphere, in the sense of Darboux charts: the
smooth partial diffeomorphism `OnePoint.discChart r` from `OnePoint ℂ` to `ℂ`, with source the
complement of `∞`, which for `r > 0` has target the open disc of radius `r` and reads a finite
point `z` as

`z ↦ r z / √(1 + |z|²)`,

Mathlib's radial diffeomorphism `OpenPartialHomeomorph.univBall 0 r` of `ℂ` onto the disc. Its
derivative pulls the standard area form back to `π r² ω_FS`
(`OnePoint.eval₂_smul_fubiniStudyForm_eq_mvfderiv_discChart`). Its inverse,
`z ↦ z / √(r² - |z|²)` on the disc, is therefore a symplectic embedding of the disc of radius `r`
into `S²(π r²)` (`OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_discChart_symm`) whose image misses
only `∞`.

Both computations are instances of the area scaling of radial maps
(`TauCeti.stdComplexSymplecticForm_fderiv_smul_self`): the map `x ↦ g(|x|²) x` scales the area form
by `g(s) (g(s) + 2 s g'(s))` at `|x|² = s`. For `g(s) = r / √(1 + s)` this factor is
`r² / (1 + s)²`, which is `π r²` times the Fubini–Study density `1 / (π (1 + s)²)`.

A disc of radius `R < r`, and so any bounded subset of `ℂ`, thus embeds symplectically into a sphere
of area `π r²`. This is the normalization by which the first factor of a cylinder
`{|z₁| < R} ⊆ ℂⁿ` is compactified to a sphere of area slightly larger than `π R²`, as in Gromov's
proof of the nonsqueezing theorem.

## Main declarations

* `OnePoint.discChart r`: for `r > 0`, the chart `z ↦ r z / √(1 + |z|²)` of the sphere minus `∞`
  onto the open disc of radius `r`.
* `OnePoint.mvfderiv_discChart_coe` and `OnePoint.mfderiv_discChart_symm`: the derivatives of the
  chart and of its inverse, read in the affine coordinate.
* `OnePoint.eval₂_smul_fubiniStudyForm_eq_mvfderiv_discChart`: for `r > 0`, it pulls the standard
  area form of `ℂ` back to `π r² ω_FS`.
* `OnePoint.eval₂_smul_fubiniStudyForm_mfderiv_discChart_symm`: for `r > 0`, its inverse pulls
  `π r² ω_FS` back to the standard area form, so it is a symplectic embedding of the disc into
  `S²(π r²)`.

## References

* M. Gromov, *Pseudo holomorphic curves in symplectic manifolds*, Invent. Math. 82 (1985),
  307–347, §0.3.A (the nonsqueezing theorem).
-/

public section

open Set Metric OpenPartialHomeomorph TauCeti
open scoped Manifold ComplexConjugate TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

variable {r : ℝ}

/-- **The disc chart of the Riemann sphere.** The smooth partial diffeomorphism of `OnePoint ℂ`
onto the open disc of radius `r` in `ℂ`, defined off `∞`, which reads a finite point `z` as
`r z / √(1 + |z|²)` (Mathlib's `OpenPartialHomeomorph.univBall 0 r`). For `r ≤ 0` it is the affine
chart. -/
def discChart (r : ℝ) : PartialDiffeomorph 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (OnePoint ℂ) ℂ (⊤ : ℕ∞) where
  toFun x := univBall (0 : ℂ) r (affineChart x)
  invFun z := (univBall (0 : ℂ) r).symm z
  source := {∞}ᶜ
  target := (univBall (0 : ℂ) r).target
  map_source' _ _ := (univBall (0 : ℂ) r).map_source (by simp)
  map_target' _ _ := coe_ne_infty _
  left_inv' x hx := by
    induction x using OnePoint.rec with
    | infty => exact absurd rfl hx
    | coe z => rw [affineChart_coe, (univBall (0 : ℂ) r).left_inv (by simp)]
  right_inv' z hz := by rw [affineChart_coe, (univBall (0 : ℂ) r).right_inv hz]
  open_source := isClosed_infty.isOpen_compl
  open_target := (univBall (0 : ℂ) r).open_target
  contMDiffOn_toFun := by
    -- The affine chart is the chart of the sphere at every finite point.
    have hchart : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) affineChart {(∞ : OnePoint ℂ)}ᶜ := by
      simpa only [chartAt_coe (𝕜 := ℂ), affineChart_source] using
        contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := ((0 : ℂ) : OnePoint ℂ))
    exact (contDiff_univBall (c := (0 : ℂ)) (r := r)).contMDiff.comp_contMDiffOn hchart
  contMDiffOn_invFun := by
    -- The inclusion of `ℂ` is holomorphic, hence smooth for the underlying real structure.
    have hcoe : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) ((↑) : ℂ → OnePoint ℂ) := by
      simpa using ((contMDiff_coe (𝕜 := ℂ)).restrictScalars ℝ).of_le le_top
    exact hcoe.comp_contMDiffOn (contDiffOn_univBall_symm_target (0 : ℂ) r).contMDiffOn

@[simp]
theorem discChart_source : (discChart r).source = {(∞ : OnePoint ℂ)}ᶜ :=
  (rfl)

@[simp]
theorem discChart_target (hr : 0 < r) : (discChart r).target = ball 0 r :=
  univBall_target (0 : ℂ) hr

/-- The disc chart reads a finite point `z` as `univBall 0 r z`, which is `r z / √(1 + |z|²)` for
`r > 0` (`OpenPartialHomeomorph.univBall_apply_of_pos`) and `z` for `r ≤ 0`. -/
@[simp]
theorem discChart_coe (z : ℂ) : discChart r z = univBall (0 : ℂ) r z :=
  congrArg (univBall (0 : ℂ) r) (affineChart_coe z)

/-- The inverse of the disc chart is the inverse of `univBall 0 r`, followed by the inclusion of
`ℂ` in the sphere. -/
@[simp]
theorem discChart_symm_apply (z : ℂ) :
    (discChart r).toPartialEquiv.symm z = ((univBall (0 : ℂ) r).symm z : ℂ) :=
  (rfl)

/-- At a finite point `z`, the derivative of the disc chart is the derivative of
`univBall 0 r` at `z`. -/
theorem mvfderiv_discChart_coe (z : ℂ) (v : TangentSpace 𝓘(ℝ, ℂ) (z : OnePoint ℂ)) :
    mvfderiv 𝓘(ℝ, ℂ) (discChart r) (z : OnePoint ℂ) v = fderiv ℝ (univBall (0 : ℂ) r) z v := by
  -- The disc chart is `univBall 0 r` after the extended chart at `z`, which is the affine chart.
  have heq : (discChart r : OnePoint ℂ → ℂ) =
      univBall (0 : ℂ) r ∘ extChartAt 𝓘(ℝ, ℂ) (z : OnePoint ℂ) := by
    funext x
    simp [discChart, chartAt_coe]
  rw [heq, mvfderiv_comp_apply_of_differentiableAt
    (contDiff_univBall (n := 1)).differentiable_one.differentiableAt
    (mdifferentiableAt_extChartAt (mem_chart_source ℂ _)),
    mvfderiv_apply_of_eventuallyEq_extChartAt Filter.EventuallyEq.rfl]
  simp

/-- At a point `z` of the target of the disc chart, the derivative of its inverse is the derivative
of the inverse of `univBall 0 r` at `z`. -/
theorem mfderiv_discChart_symm {z : ℂ} (hz : z ∈ (discChart r).target) (v : ℂ) :
    mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discChart r).symm z v = fderiv ℝ (univBall (0 : ℂ) r).symm z v := by
  have hmd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discChart r).symm z :=
    (discChart r).symm.mdifferentiableAt (by simp) hz
  rw [hmd.mfderiv]
  simp only [writtenInExtChartAt, PartialDiffeomorph.symm_toPartialEquiv, discChart_symm_apply,
    chartAt_coe, affineChart_coe,
    Function.comp_def, fderivWithin_univ, mfld_simps]
  -- Both tangent identifications `tangentSpaceCastModel` are the identity of `ℂ`.
  rfl

/-- The area identity behind `eval₂_smul_fubiniStudyForm_eq_mvfderiv_discChart`, in the affine
coordinate: `univBall 0 r` scales the standard area form by `r² / (1 + |z|²)²`, which is `π r²`
times the Fubini–Study density. -/
private theorem mul_fubiniStudyDensity_mul_eq_fderiv_univBall (hr : 0 < r) (z v w : ℂ) :
    Real.pi * r ^ 2 * (fubiniStudyDensity z * ((starRingEnd ℂ) v * w).im) =
      stdComplexSymplecticForm (fderiv ℝ (univBall (0 : ℂ) r) z v)
        (fderiv ℝ (univBall (0 : ℂ) r) z w) := by
  have h1 : 0 < 1 + ‖z‖ ^ 2 := by positivity
  -- `univBall 0 r` is the radial map `x ↦ g(|x|²) x` with `g(s) = r / √(1 + s)`.
  have hφ : ⇑(univBall (0 : ℂ) r) = fun x : ℂ ↦ (r * (Real.sqrt (1 + ‖x‖ ^ 2))⁻¹) • x :=
    funext fun x ↦ by rw [univBall_apply_of_pos _ hr, vadd_eq_add, add_zero]
  have hg : HasDerivAt (fun t : ℝ ↦ r * (Real.sqrt (1 + t))⁻¹)
      (-(r / (2 * (1 + ‖z‖ ^ 2) * Real.sqrt (1 + ‖z‖ ^ 2)))) (‖z‖ ^ 2) := by
    have hsq := ((hasDerivAt_id (‖z‖ ^ 2)).const_add 1).sqrt h1.ne'
    refine ((hsq.inv (Real.sqrt_pos.2 h1).ne').const_mul r).congr_deriv ?_
    simp only [id_eq]
    rw [Real.sq_sqrt h1.le]
    field_simp
  rw [hφ, stdComplexSymplecticForm_fderiv_smul_self hg,
    stdComplexSymplecticForm_apply_eq_im_conj_mul, fubiniStudyDensity_def]
  -- The area factor `g(s) (g(s) + 2 s g'(s))` is `r² / (1 + s)²`.
  have hq : Real.sqrt (1 + ‖z‖ ^ 2) ^ 2 = 1 + ‖z‖ ^ 2 := Real.sq_sqrt h1.le
  have hq0 : Real.sqrt (1 + ‖z‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  field_simp
  rw [hq]
  ring

/-- The area identity behind `eval₂_smul_fubiniStudyForm_mfderiv_discChart_symm`, in the affine
coordinate: the inverse of `univBall 0 r` scales the standard area form by `r² / (r² - |z|²)²`,
the reciprocal of `π r²` times the Fubini–Study density at the image point. -/
private theorem mul_fubiniStudyDensity_fderiv_univBall_symm (hr : 0 < r) {z : ℂ}
    (hz : z ∈ ball 0 r) (v w : ℂ) :
    Real.pi * r ^ 2 * (fubiniStudyDensity ((univBall (0 : ℂ) r).symm z) *
        ((starRingEnd ℂ) (fderiv ℝ (univBall (0 : ℂ) r).symm z v) *
          fderiv ℝ (univBall (0 : ℂ) r).symm z w).im) =
      stdComplexSymplecticForm v w := by
  have hs : ‖z‖ ^ 2 < r ^ 2 := pow_lt_pow_left₀ (mem_ball_zero_iff.1 hz) (norm_nonneg z) two_ne_zero
  have h1 : 0 < r ^ 2 - ‖z‖ ^ 2 := by linarith
  -- The inverse of `univBall 0 r` is the radial map `x ↦ g(|x|²) x` with `g(s) = 1 / √(r² - s)`.
  have hψ : ⇑(univBall (0 : ℂ) r).symm = fun x : ℂ ↦ (Real.sqrt (r ^ 2 - ‖x‖ ^ 2))⁻¹ • x :=
    funext fun x ↦ by rw [univBall_symm_apply_of_pos _ hr, dist_zero_right, vsub_eq_sub, sub_zero]
  have hg : HasDerivAt (fun t : ℝ ↦ (Real.sqrt (r ^ 2 - t))⁻¹)
      ((2 * (r ^ 2 - ‖z‖ ^ 2) * Real.sqrt (r ^ 2 - ‖z‖ ^ 2))⁻¹) (‖z‖ ^ 2) := by
    have hsq := ((hasDerivAt_id (‖z‖ ^ 2)).const_sub (r ^ 2)).sqrt h1.ne'
    refine (hsq.inv (Real.sqrt_pos.2 h1).ne').congr_deriv ?_
    simp only [id_eq]
    rw [Real.sq_sqrt h1.le]
    field_simp
  rw [← stdComplexSymplecticForm_apply_eq_im_conj_mul, hψ,
    stdComplexSymplecticForm_fderiv_smul_self hg,
    fubiniStudyDensity_def, norm_smul, norm_inv, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  -- With `q = √(r² - s)`, `1 + |ψ z|² = r² / q²` and the area factor is `r² / q⁴`.
  have hq : Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ^ 2 = r ^ 2 - ‖z‖ ^ 2 := Real.sq_sqrt h1.le
  have hq0 : Real.sqrt (r ^ 2 - ‖z‖ ^ 2) ≠ 0 := (Real.sqrt_pos.2 h1).ne'
  field_simp
  rw [hq]
  ring

/-- **The disc chart is symplectic.** At every finite point `x` of the sphere, the derivative of
the disc chart `z ↦ r z / √(1 + |z|²)` pulls the standard area form of `ℂ` back to `π r²` times
the Fubini–Study form. So the sphere of area `π r²` minus `∞` is symplectomorphic to the open disc
of radius `r`. -/
theorem eval₂_smul_fubiniStudyForm_eq_mvfderiv_discChart (hr : 0 < r) {x : OnePoint ℂ}
    (hx : x ∈ (discChart r).source) (v w : TangentSpace 𝓘(ℝ, ℂ) x) :
    SmoothBundleForm.eval₂ ((Real.pi * r ^ 2) • fubiniStudyForm) x v w =
      stdComplexSymplecticForm (mvfderiv 𝓘(ℝ, ℂ) (discChart r) x v)
        (mvfderiv 𝓘(ℝ, ℂ) (discChart r) x w) := by
  induction x using OnePoint.rec with
  | infty => simp at hx
  | coe z =>
    rw [mvfderiv_discChart_coe, mvfderiv_discChart_coe, SmoothForm.eval₂_smul, smul_eq_mul]
    exact (congrArg (Real.pi * r ^ 2 * ·) (eval₂_fubiniStudyForm_coe z v w)).trans
      (mul_fubiniStudyDensity_mul_eq_fderiv_univBall hr z v w)

/-- **The disc of radius `r` embeds symplectically into the sphere of area `π r²`.** At a point
`z` of the open disc of radius `r`, the derivative of the inverse of the disc chart,
`z ↦ z / √(r² - |z|²)` followed by the inclusion of `ℂ` in the sphere, pulls `π r²` times the
Fubini–Study form back to the standard area form of `ℂ`. -/
theorem eval₂_smul_fubiniStudyForm_mfderiv_discChart_symm (hr : 0 < r) {z : ℂ} (hz : z ∈ ball 0 r)
    (v w : ℂ) :
    SmoothBundleForm.eval₂ ((Real.pi * r ^ 2) • fubiniStudyForm) ((discChart r).symm z)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discChart r).symm z v)
        (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (discChart r).symm z w) =
      stdComplexSymplecticForm v w := by
  have hz' : z ∈ (discChart r).target := by rwa [discChart_target hr]
  rw [mfderiv_discChart_symm hz', mfderiv_discChart_symm hz']
  -- The inverse of the disc chart sends `z` to the finite point `(univBall 0 r).symm z`.
  exact (SmoothForm.eval₂_smul _ _ _ _ _).trans <|
    (congrArg (Real.pi * r ^ 2 * ·)
      (eval₂_fubiniStudyForm_coe ((univBall (0 : ℂ) r).symm z) _ _)).trans
      (mul_fubiniStudyDensity_fderiv_univBall_symm hr hz v w)

end OnePoint
