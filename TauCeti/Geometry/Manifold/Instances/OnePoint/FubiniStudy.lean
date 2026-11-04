/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Constructions.HaarToSphere
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# The Fubini–Study form of the Riemann sphere

The Riemann sphere `OnePoint ℂ`, regarded as a real surface through its holomorphic charts, carries
the **Fubini–Study form** `ω_FS = (i / 2π) ∂ ∂bar log (1 + |z|²)`. In the affine coordinate
`z = x + iy` it reads

`ω_FS = ρ(z) dx ∧ dy`, with density `ρ(z) = 1 / (π (1 + |z|²)²)`
(`OnePoint.fubiniStudyDensity`).

The density satisfies `ρ(z⁻¹) = |z|⁴ ρ(z)`, which is exactly the transformation law of a two-form
under the chart transition `z ↦ z⁻¹`, whose derivative is multiplication by `-z⁻²`. So in the
inverted coordinate `w = 1 / z` the form reads `ρ(w) du ∧ dv` again, and the two coordinate
expressions glue to a smooth two-form `OnePoint.fubiniStudyForm` on the whole sphere, including
the point `∞`. On a tangent space, identified with `ℂ` through the preferred chart, it is

`ω_FS(v, w) = ρ(c) Im (conj v * w)`,

where `c` is the coordinate of the base point (`OnePoint.eval₂_fubiniStudyForm`); in an arbitrary
chart of the atlas it has the same expression in that chart's coordinate
(`OnePoint.eval₂_fubiniStudyForm_tangentCoordChange`).

Since `ρ > 0` the form vanishes nowhere, so it is a symplectic form on the sphere
(`OnePoint.isSymplectic_fubiniStudyForm`). It is compatible with the complex structure of the
sphere, multiplication by `i` on each tangent space
(`OnePoint.compatible_fubiniStudyForm`); the associated Riemannian metric
`g_FS(v, w) = ω_FS(v, i w)` is `ρ(c) Re (conj v * w)`
(`OnePoint.eval₂_fubiniStudyForm_I_mul`). The form is normalized to total area one: the density
integrates to `1` over the affine chart
(`OnePoint.integral_fubiniStudyDensity`), which is the whole sphere except the point `∞`. The area
`π` of the unit disc and the polar integral `∫₀^∞ 2r / (1 + r²)² dr = 1` give this value. The
comparison with the integral of the form over the oriented sphere is not carried out here.

This is the area form with which symplectic and holomorphic-curve arguments on the sphere are
normalized; other areas are obtained by scaling it.

## Main declarations

* `OnePoint.fubiniStudyDensity`: the density `1 / (π (1 + |z|²)²)` in the affine coordinate.
* `OnePoint.fubiniStudyDensity_inv`: its transformation law under `z ↦ z⁻¹`.
* `OnePoint.integral_fubiniStudyDensity`: it integrates to `1` over `ℂ`.
* `OnePoint.fubiniStudyForm`: the Fubini–Study form, a smooth real two-form on `OnePoint ℂ`.
* `OnePoint.eval₂_fubiniStudyForm` and `OnePoint.eval₂_fubiniStudyForm_tangentCoordChange`: its
  values in the preferred chart and in every chart of the atlas.
* `OnePoint.isSymplectic_fubiniStudyForm`: it is symplectic.
* `OnePoint.compatible_fubiniStudyForm`: it is compatible with the complex structure.

## References

* P. Griffiths and J. Harris, *Principles of Algebraic Geometry*, Wiley, 1978, Chapter 0,
  Section 2 (the Fubini–Study metric `(i / 2π) ∂ ∂bar log ‖Z‖²` on projective space).
* D. Huybrechts, *Complex Geometry: An Introduction*, Universitext, Springer, 2005, Section 3.1
  (the Fubini–Study form).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS Colloquium
  Publications 52, 2012, Section 2.2 (compatible pairs).
-/

public section

open Set Filter Function MeasureTheory ComplexConjugate TauCeti
open scoped Manifold Topology TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

attribute [local instance] Complex.finrank_real_complex_fact

/-! ### The density -/

/-- The density `ρ(z) = 1 / (π (1 + |z|²)²)` of the Fubini–Study form in the affine coordinate
of the Riemann sphere. -/
def fubiniStudyDensity (z : ℂ) : ℝ :=
  (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹

theorem fubiniStudyDensity_def (z : ℂ) :
    fubiniStudyDensity z = (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹ :=
  (rfl)

/-- The density at the origin is `1 / π`. -/
@[simp]
theorem fubiniStudyDensity_zero : fubiniStudyDensity 0 = Real.pi⁻¹ := by
  simp [fubiniStudyDensity]

/-- The Fubini–Study density is positive. -/
theorem fubiniStudyDensity_pos (z : ℂ) : 0 < fubiniStudyDensity z := by
  unfold fubiniStudyDensity
  positivity

/-- The Fubini–Study density is smooth, indeed real-analytic. -/
theorem contDiff_fubiniStudyDensity {n : WithTop ℕ∞} : ContDiff ℝ n fubiniStudyDensity :=
  (contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℝ)).pow 2)).inv fun z ↦ by positivity

/-- **The transformation law of the density under `z ↦ z⁻¹`.** The density at `z⁻¹` is `|z|⁴`
times the density at `z`, the factor `|z|⁴` being the Jacobian of `z ↦ z⁻¹`. This is what makes
the coordinate expressions of the Fubini–Study form in the two charts of the sphere agree. -/
theorem fubiniStudyDensity_inv {z : ℂ} (hz : z ≠ 0) :
    fubiniStudyDensity z⁻¹ = ‖z‖ ^ 4 * fubiniStudyDensity z := by
  have hz' : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  simp only [fubiniStudyDensity, norm_inv]
  field_simp
  ring

/-- The radial profile of the density integrates against `r dr` to `1 / (2π)`, through the
primitive `r ↦ -1 / (2π (1 + r²))`. -/
private theorem integral_Ioi_mul_fubiniStudyDensity :
    ∫ r in Ioi (0 : ℝ), r * (Real.pi * (1 + r ^ 2) ^ 2)⁻¹ = (2 * Real.pi)⁻¹ := by
  have hderiv (r : ℝ) : HasDerivAt (fun r : ℝ ↦ -(2 * Real.pi * (1 + r ^ 2))⁻¹)
      (r * (Real.pi * (1 + r ^ 2) ^ 2)⁻¹) r := by
    have h := (((hasDerivAt_pow 2 r).const_add 1).const_mul (2 * Real.pi)).inv
      (by positivity)
    convert h.neg using 1
    field_simp
    ring
  have hlim : Tendsto (fun r : ℝ ↦ -(2 * Real.pi * (1 + r ^ 2))⁻¹) atTop (𝓝 0) := by
    have h : Tendsto (fun r : ℝ ↦ 2 * Real.pi * (1 + r ^ 2)) atTop atTop :=
      Tendsto.const_mul_atTop (by positivity)
        (tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero))
    simpa using h.inv_tendsto_atTop.neg
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (fun r _ ↦ hderiv r)
    (fun r hr ↦ by have : 0 < r := hr; positivity) hlim]
  simp

/-- **The Fubini–Study density has total integral one.** Integrating in polar coordinates, the
density integrates to `2 · π · 1 / (2π) = 1` over `ℂ`, the affine chart of the sphere, which misses
only the point `∞`. This is the normalization of the Fubini–Study form to total area one. -/
theorem integral_fubiniStudyDensity : ∫ z : ℂ, fubiniStudyDensity z = 1 := by
  have h := integral_fun_norm_addHaar (volume : Measure ℂ)
    (fun r : ℝ ↦ (Real.pi * (1 + r ^ 2) ^ 2)⁻¹)
  simp only [Complex.finrank_real_complex, Measure.real, Complex.volume_ball] at h
  rw [show (fun z : ℂ ↦ fubiniStudyDensity z) =
      fun z ↦ (Real.pi * (1 + ‖z‖ ^ 2) ^ 2)⁻¹ from rfl, h]
  simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul, integral_Ioi_mul_fubiniStudyDensity]
  simp only [ENNReal.ofReal_one, one_pow, one_mul, ENNReal.coe_toReal, NNReal.coe_real_pi]
  field_simp
  norm_num

/-! ### Tangent coordinate changes of the Riemann sphere -/

/-- On the Riemann sphere regarded as a real surface, the tangent coordinate change from the chart
at `∞` to the chart at a nonzero finite point `z` is multiplication by `-z²`, the derivative of
the chart transition `w ↦ w⁻¹` at `w = z⁻¹`. -/
theorem tangentCoordChange_infty_coe {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    tangentCoordChange 𝓘(ℝ, ℂ) (∞ : OnePoint ℂ) (z : OnePoint ℂ) (z : OnePoint ℂ) v =
      -z ^ 2 * v := by
  have h : HasFDerivAt (fun w : ℂ ↦ w⁻¹)
      ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) (-(z⁻¹ ^ 2)⁻¹)).restrictScalars ℝ) z⁻¹ :=
    (hasDerivAt_inv (inv_ne_zero hz)).hasFDerivAt.restrictScalars ℝ
  simp [affineChart_comp_invChart_symm, h.fderiv, mul_comm]

/-! ### The Fubini–Study form -/

/-- The underlying rough form of the Fubini–Study form: at a point with coordinate `c` in its
preferred chart, `ρ(c) dx ∧ dy`. -/
private def fubiniStudyRough : RoughForm 𝓘(ℝ, ℂ) (OnePoint ℂ) ℝ 2 :=
  fun x ↦ fubiniStudyDensity (chartAt ℂ x x) • Complex.orientation.volumeFormL

private theorem fubiniStudyRough_apply (x : OnePoint ℂ) (u : Fin 2 → ℂ) :
    fubiniStudyRough x u = fubiniStudyDensity (chartAt ℂ x x) * (conj (u 0) * u 1).im :=
  -- The value at `x` is `ρ • vol` on the tangent space at `x`, which is `ℂ`.
  congrArg (fubiniStudyDensity (chartAt ℂ x x) * ·) (Complex.orientation_volumeFormL_apply u)

/-- **Chart independence of the coordinate expression.** In every chart of the atlas, the rough
Fubini–Study form reads `ρ dx ∧ dy` in that chart's coordinate. -/
private theorem fubiniStudyRough_tangentCoordChange {x y : OnePoint ℂ}
    (hy : y ∈ (chartAt ℂ x).source) (u : Fin 2 → ℂ) :
    fubiniStudyRough y (fun i ↦ tangentCoordChange 𝓘(ℝ, ℂ) x y y (u i)) =
      fubiniStudyDensity (chartAt ℂ x y) * (conj (u 0) * u 1).im := by
  refine (fubiniStudyRough_apply y _).trans ?_
  induction x using OnePoint.rec with
  | coe z₀ =>
    induction y using OnePoint.rec with
    | infty => simp at hy
    | coe z =>
      -- Both points use the affine chart, so the coordinate change is the identity.
      simp [Function.comp_def]
  | infty =>
    induction y using OnePoint.rec with
    | infty =>
      rw [tangentCoordChange_self (by simp), tangentCoordChange_self (by simp)]
    | coe z =>
      have hz : z ≠ 0 := by rintro rfl; simp at hy
      -- Multiplying both vectors by `c` scales their area `Im (conj v * w)` by `|c|²`.
      have hscale (v w c : ℂ) : (conj (c * v) * (c * w)).im = ‖c‖ ^ 2 * (conj v * w).im := by
        rw [map_mul, show conj c * conj v * (c * w) = (conj c * c) * (conj v * w) by ring,
          Complex.conj_mul', ← Complex.ofReal_pow, Complex.im_ofReal_mul]
      rw [tangentCoordChange_infty_coe hz, tangentCoordChange_infty_coe hz, hscale,
        chartAt_infty, invChart_coe, fubiniStudyDensity_inv hz]
      simp only [chartAt_coe, affineChart_coe, norm_neg, norm_pow]
      ring

/-- The rough Fubini–Study form is smooth: in the tangent trivialization at any point it is the
smooth function `ρ` of the chart coordinate times a constant. -/
private theorem isSmoothForm_fubiniStudyRough {n : WithTop ℕ∞} :
    IsSmoothForm 𝓘(ℝ, ℂ) n fubiniStudyRough := by
  rw [isSmoothForm_iff_forall_contMDiffAt_trivializationAt_apply]
  intro x u
  have hsmooth : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) n
      (fun y ↦ fubiniStudyDensity (extChartAt 𝓘(ℝ, ℂ) x y) * (conj (u 0) * u 1).im) x :=
    (contDiff_fubiniStudyDensity.mul contDiff_const).comp_contMDiffAt contMDiffAt_extChartAt
  refine hsmooth.congr_of_eventuallyEq ?_
  filter_upwards [(chartAt ℂ x).open_source.mem_nhds (mem_chart_source ℂ x)] with y hy
  rw [TangentBundle.symmL_trivializationAt_eq_core hy]
  exact (fubiniStudyRough_tangentCoordChange hy u).trans (by simp)

/-- **The Fubini–Study form** of the Riemann sphere, the smooth real two-form
`ω_FS = (i / 2π) ∂ ∂bar log (1 + |z|²)`, which reads `ρ(z) dx ∧ dy` with
`ρ(z) = 1 / (π (1 + |z|²)²)` in the affine coordinate `z = x + iy`, and in the same way in the
inverted coordinate. -/
def fubiniStudyForm : SmoothTwoForm 𝓘(ℝ, ℂ) (OnePoint ℂ) :=
  ⟨fubiniStudyRough, isSmoothForm_fubiniStudyRough.mem_smoothBundleForms⟩

/-- **The Fubini–Study form on a tangent space.** Identifying the tangent space at `x` with `ℂ`
through the preferred chart, in which `x` has coordinate `c`, the Fubini–Study form is
`ω_FS(v, w) = ρ(c) Im (conj v * w)`. -/
theorem eval₂_fubiniStudyForm (x : OnePoint ℂ) (v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm x v w =
      fubiniStudyDensity (chartAt ℂ x x) * (conj v * w).im :=
  (SmoothBundleForm.eval₂_apply _ _ _ _).trans (fubiniStudyRough_apply x ![v, w])

/-- The Fubini–Study form at a finite point `z`, in the affine coordinate:
`ω_FS(v, w) = Im (conj v * w) / (π (1 + |z|²)²)`. -/
@[simp]
theorem eval₂_fubiniStudyForm_coe (z v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm (z : OnePoint ℂ) v w =
      fubiniStudyDensity z * (conj v * w).im := by
  simp [eval₂_fubiniStudyForm]

/-- The Fubini–Study form at `∞`, in the inverted coordinate: `ω_FS(v, w) = Im (conj v * w) / π`. -/
@[simp]
theorem eval₂_fubiniStudyForm_infty (v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm (∞ : OnePoint ℂ) v w =
      Real.pi⁻¹ * (conj v * w).im := by
  simp [eval₂_fubiniStudyForm]

/-- **The Fubini–Study form in every chart.** For `y` in the source of the preferred chart at
`x`, the Fubini–Study form at `y`, evaluated on the tangent vectors with coordinates `v` and `w` in
the chart at `x`, is `ρ(c) Im (conj v * w)`, where `c` is the coordinate of `y` in that chart. -/
theorem eval₂_fubiniStudyForm_tangentCoordChange {x y : OnePoint ℂ}
    (hy : y ∈ (chartAt ℂ x).source) (v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm y (tangentCoordChange 𝓘(ℝ, ℂ) x y y v)
        (tangentCoordChange 𝓘(ℝ, ℂ) x y y w) =
      fubiniStudyDensity (chartAt ℂ x y) * (conj v * w).im :=
  (SmoothBundleForm.eval₂_apply _ _ _ _).trans <|
    (congrArg (fubiniStudyRough y) (by funext i; fin_cases i <;> rfl)).trans
      (fubiniStudyRough_tangentCoordChange hy ![v, w])

/-- **The Fubini–Study metric.** The Riemannian metric `g_FS(v, w) = ω_FS(v, i w)` associated with
the Fubini–Study form and the complex structure is `ρ(c) Re (conj v * w)`, where `c` is the
coordinate of the base point. -/
theorem eval₂_fubiniStudyForm_I_mul (x : OnePoint ℂ) (v w : ℂ) :
    SmoothBundleForm.eval₂ fubiniStudyForm x v (Complex.I * w) =
      fubiniStudyDensity (chartAt ℂ x x) * (conj v * w).re := by
  rw [eval₂_fubiniStudyForm, mul_left_comm]
  simp

/-- The Fubini–Study form vanishes at no point. -/
theorem fubiniStudyForm_apply_ne_zero (x : OnePoint ℂ) : fubiniStudyForm.1 x ≠ 0 := by
  intro h
  have h1 : fubiniStudyForm.1 x (![1, Complex.I] : Fin 2 → ℂ) =
      fubiniStudyDensity (chartAt ℂ x x) :=
    (fubiniStudyRough_apply x _).trans (by simp)
  rw [h] at h1
  exact (fubiniStudyDensity_pos _).ne' h1.symm

/-- **The Fubini–Study form is symplectic**: it is a nowhere-vanishing two-form on a surface. -/
theorem isSymplectic_fubiniStudyForm : fubiniStudyForm.IsSymplectic :=
  (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two
    Complex.finrank_real_complex).2 fubiniStudyForm_apply_ne_zero

/-- **The Fubini–Study form is compatible with the complex structure** of the Riemann sphere: it
is invariant under multiplication by `i`, and `ω_FS(v, i v) = ρ |v|² > 0` for `v ≠ 0`. -/
theorem compatible_fubiniStudyForm :
    fubiniStudyForm.Compatible (SmoothAlmostComplexStructure.ofComplexManifold ℂ (OnePoint ℂ)) := by
  -- Each tangent space is `ℂ`, on which the complex structure is multiplication by `I`.
  refine ⟨SmoothTwoForm.invariant_iff.2 fun x (v w : ℂ) ↦ ?_,
    SmoothTwoForm.tames_iff.2 fun x (v : ℂ) hv ↦ ?_⟩
  · -- The complex structure is `v ↦ I • v` on the tangent space `ℂ`, and `conj I * I = 1`.
    have h (v w : ℂ) : SmoothBundleForm.eval₂ fubiniStudyForm x (Complex.I • v) (Complex.I • w) =
        SmoothBundleForm.eval₂ fubiniStudyForm x v w := by
      simp only [eval₂_fubiniStudyForm, smul_eq_mul, map_mul, Complex.conj_I]
      ring_nf
      simp
    exact (congrArg₂ (SmoothBundleForm.eval₂ fubiniStudyForm x)
      (SmoothAlmostComplexStructure.ofComplexManifold_apply x v)
      (SmoothAlmostComplexStructure.ofComplexManifold_apply x w)).trans (h v w)
  · -- On the tangent space `ℂ`, `ω_FS(v, I v) = ρ Re (conj v * v) = ρ |v|²`.
    have h (v : ℂ) (hv : v ≠ 0) :
        0 < SmoothBundleForm.eval₂ fubiniStudyForm x v (Complex.I • v) := by
      rw [smul_eq_mul, eval₂_fubiniStudyForm_I_mul, Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re]
      exact mul_pos (fubiniStudyDensity_pos _) (pow_pos (norm_pos_iff.2 hv) 2)
    exact (congrArg (SmoothBundleForm.eval₂ fubiniStudyForm x v)
      (SmoothAlmostComplexStructure.ofComplexManifold_apply x v)).trans_gt (h v hv)

end OnePoint
