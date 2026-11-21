/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Distribution.TemperateGrowth
public import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Topology.Circle.Metric

/-!
# Derivatives, growth and Lipschitz bounds of the Fourier phases

On a real inner-product space, the phases `ζ ↦ 𝐞 ⟪ζ, x⟫` and `y ↦ 𝐞 (-⟪y, ζ⟫)` of the inverse and
direct Fourier integrals have directional derivatives `2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫` and
`-2πi ⟪v, ζ⟫ 𝐞 (-⟪y, ζ⟫)` in the direction `v`. These are Mathlib's derivatives
`Real.hasFDerivAt_fourierChar_neg_bilinear_right` and
`Real.hasFDerivAt_fourierChar_neg_bilinear_left` of the Fourier character composed with a
bilinear map, specialized to the inner product and evaluated in a direction, which is the form
used to integrate by parts against the phase.

The plane wave `x ↦ 𝐞 ⟪x, η⟫ = exp(2πi ⟪x, η⟫)` of frequency `η` is smooth, and jointly continuous
in the frequency and the position; its derivatives of order `k` are bounded by `(2π ‖η‖) ^ k`
(`Real.norm_iteratedFDeriv_fourierChar_inner_le`, stated with the Fourier atoms in
`TauCeti.Analysis.PositiveDefinite.FourierAtom`).

The Fourier character `𝐞 t = Circle.exp (2πt)` is `2π`-Lipschitz, since `Circle.exp` is
`1`-Lipschitz (`TauCeti.lipschitzWith_one_circleExp`). Hence the phase `z ↦ 𝐞 ⟪ζ, z⟫` changes by
at most `2π ‖ζ‖ ‖z - z'‖`, which is how increments of oscillatory integrals in the spatial variable
are bounded by a first frequency moment.

The plane wave `x ↦ 𝐞 ⟪x, ξ⟫` is a function of temperate growth, and since it has modulus one
it lies in `L^∞` of any measure, with norm one when the measure is nonzero.

## Main results

* `Real.hasLineDerivAt_fourierChar_inner`: the directional derivative of `ζ ↦ 𝐞 ⟪ζ, x⟫`.
* `Real.hasLineDerivAt_fourierChar_neg_inner`: the directional derivative of
  `y ↦ 𝐞 (-⟪y, ζ⟫)`.
* `Real.continuous_fourierChar_inner`, `Real.contDiff_fourierChar_inner`: the plane waves are
  jointly continuous and smooth in the position.
* `Real.norm_fourierChar_sub_fourierChar_le`: `‖𝐞 t - 𝐞 t'‖ ≤ 2π |t - t'|`.
* `Real.norm_fourierChar_smul_sub_fourierChar_smul_le`:
  `‖𝐞 ⟪ζ, z⟫ • v - 𝐞 ⟪ζ, z'⟫ • v‖ ≤ 2π ‖ζ‖ ‖z - z'‖ ‖v‖`.
* `Real.hasTemperateGrowth_fourierChar_inner`: the plane wave `x ↦ 𝐞 ⟪x, ξ⟫` has temperate growth.
* `Real.memLp_top_fourierChar_inner`, `Real.norm_toLp_fourierChar_inner`: the plane wave lies in
  `L^∞` of any measure, with norm one when the measure is nonzero.
* `ContDiff.fourierChar`: `y ↦ 𝐞 (Φ y)` is `C^n` when the phase `Φ` is.
* `HasFDerivAt.fourierChar`: the derivative of `y ↦ 𝐞 (Φ y)` is `2πi 𝐞 (Φ y) DΦ(y)`.
-/

public section

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace ENNReal

namespace Real

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The line derivative in the direction `v` of the phase `ζ ↦ 𝐞 ⟪ζ, x⟫` is
`2πi ⟪v, x⟫ 𝐞 ⟪ζ, x⟫`. This is Mathlib's derivative of `ζ ↦ 𝐞 (-L x ζ)` with `L = -innerSL ℝ`. -/
theorem hasLineDerivAt_fourierChar_inner (x v ζ : E) :
    HasLineDerivAt ℝ (fun ζ ↦ (𝐞 ⟪ζ, x⟫ : ℂ)) ((2 * π * Complex.I * ⟪v, x⟫) * 𝐞 ⟪ζ, x⟫) ζ v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_right (-innerSL ℝ) x ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm x]
  ring

/-- The line derivative in the direction `v` of the phase `y ↦ 𝐞 (-⟪y, ζ⟫)` is
`-2πi ⟪v, ζ⟫ 𝐞 (-⟪y, ζ⟫)`. This is Mathlib's derivative of `y ↦ 𝐞 (-L y ζ)` with
`L = innerSL ℝ`. -/
theorem hasLineDerivAt_fourierChar_neg_inner (ζ v y : E) :
    HasLineDerivAt ℝ (fun y ↦ (𝐞 (-⟪y, ζ⟫) : ℂ))
      ((-2 * π * Complex.I * ⟪v, ζ⟫) * 𝐞 (-⟪y, ζ⟫)) y v := by
  convert (hasFDerivAt_fourierChar_neg_bilinear_left (innerSL ℝ) y ζ).hasLineDerivAt v
    using 1 <;> simp [innerSL_apply_apply ℝ, real_inner_comm ζ]
  ring

/-- The plane waves `𝐞 ⟪η, x⟫` depend continuously on the frequency and the position jointly. -/
theorem continuous_fourierChar_inner :
    Continuous fun p : E × E ↦ (𝐞 ⟪p.1, p.2⟫ : ℂ) :=
  continuous_subtypeVal.comp (continuous_fourierChar.comp continuous_inner)

/-- The Fourier character is `2π`-Lipschitz: `‖𝐞 t - 𝐞 t'‖ ≤ 2π |t - t'|`, since
`𝐞 t = Circle.exp (2πt)` and `Circle.exp` is `1`-Lipschitz. -/
theorem norm_fourierChar_sub_fourierChar_le (t t' : ℝ) :
    ‖(𝐞 t : ℂ) - 𝐞 t'‖ ≤ 2 * π * |t - t'| := by
  have h := TauCeti.lipschitzWith_one_circleExp.dist_le_mul (2 * π * t) (2 * π * t')
  rw [← fourierChar_apply', ← fourierChar_apply'] at h
  calc ‖(𝐞 t : ℂ) - 𝐞 t'‖ = dist (𝐞 t) (𝐞 t') := (Circle.dist_eq_norm_coe_sub _ _).symm
    _ ≤ 2 * π * |t - t'| := by
        simpa [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos two_pi_pos] using h

/-- The phase `z ↦ 𝐞 ⟪ζ, z⟫` acting on a vector `v` is `2π ‖ζ‖ ‖v‖`-Lipschitz:
`‖𝐞 ⟪ζ, z⟫ • v - 𝐞 ⟪ζ, z'⟫ • v‖ ≤ 2π ‖ζ‖ ‖z - z'‖ ‖v‖`. -/
theorem norm_fourierChar_smul_sub_fourierChar_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℂ F] (ζ z z' : E) (v : F) :
    ‖𝐞 ⟪ζ, z⟫ • v - 𝐞 ⟪ζ, z'⟫ • v‖ ≤ 2 * π * ‖ζ‖ * ‖z - z'‖ * ‖v‖ := by
  rw [Circle.smul_def, Circle.smul_def, ← sub_smul, norm_smul]
  gcongr
  calc ‖(𝐞 ⟪ζ, z⟫ : ℂ) - 𝐞 ⟪ζ, z'⟫‖ ≤ 2 * π * |⟪ζ, z⟫ - ⟪ζ, z'⟫| :=
        norm_fourierChar_sub_fourierChar_le _ _
    _ ≤ 2 * π * (‖ζ‖ * ‖z - z'‖) := by
        rw [← inner_sub_right]
        gcongr
        exact abs_real_inner_le_norm _ _
    _ = 2 * π * ‖ζ‖ * ‖z - z'‖ := by ring

/-- The plane wave `x ↦ 𝐞 ⟪x, ξ⟫` has temperate growth. -/
theorem hasTemperateGrowth_fourierChar_inner (ξ : E) :
    (fun x : E ↦ (𝐞 ⟪x, ξ⟫ : ℂ)).HasTemperateGrowth := by
  have h : (fun x : E ↦ (𝐞 ⟪x, ξ⟫ : ℂ)) =
      fun x ↦ Complex.exp (((2 * π * ⟪x, ξ⟫ : ℝ) : ℂ) * Complex.I) := by
    funext x
    rw [fourierChar_apply]
  rw [h]
  exact Complex.hasTemperateGrowth_exp_mul_I.comp (by fun_prop)

variable [MeasurableSpace E] [OpensMeasurableSpace E] {μ : Measure E}

/-- The plane wave `x ↦ 𝐞 ⟪x, ξ⟫` is essentially bounded. -/
theorem memLp_top_fourierChar_inner (ξ : E) : MemLp (fun x : E ↦ (𝐞 ⟪x, ξ⟫ : ℂ)) ∞ μ :=
  memLp_top_of_bound (by fun_prop : Continuous fun x : E ↦ (𝐞 ⟪x, ξ⟫ : ℂ)).aestronglyMeasurable 1
    (ae_of_all _ fun x ↦ by simp)

/-- The plane wave `x ↦ 𝐞 ⟪x, ξ⟫` has norm one in `L^∞` of any nonzero measure. -/
theorem norm_toLp_fourierChar_inner [NeZero μ] (ξ : E) :
    ‖(memLp_top_fourierChar_inner (μ := μ) ξ).toLp _‖ = 1 := by
  rw [Lp.norm_toLp, eLpNorm_congr_norm_ae (memLp_top_fourierChar_inner ξ).aestronglyMeasurable
    aestronglyMeasurable_const (g := fun _ : E ↦ (1 : ℂ)) (ae_of_all _ fun x ↦ by simp),
    eLpNorm_const _ ENNReal.top_ne_zero (NeZero.ne μ)]
  simp

end Real

/-- The Fourier character composed with a `C^n` real phase is `C^n`. -/
@[fun_prop]
theorem ContDiff.fourierChar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : WithTop ℕ∞} {Φ : F → ℝ} (hΦ : ContDiff ℝ n Φ) : ContDiff ℝ n fun y ↦ (𝐞 (Φ y) : ℂ) := by
  simp_rw [Real.fourierChar_apply]
  exact ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hΦ)).mul contDiff_const).cexp

/-- The plane wave `x ↦ 𝐞 ⟪x, η⟫` is smooth. -/
theorem Real.contDiff_fourierChar_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (η : E) {n : WithTop ℕ∞} : ContDiff ℝ n fun x : E ↦ (𝐞 ⟪x, η⟫ : ℂ) :=
  (contDiff_inner.comp (contDiff_id.prodMk contDiff_const)).fourierChar

/-- The derivative of the Fourier character composed with a real phase `Φ` is
`2πi 𝐞 (Φ y) DΦ(y)`. -/
theorem HasFDerivAt.fourierChar {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Φ : F → ℝ} {Φ' : F →L[ℝ] ℝ} {y : F} (hΦ : HasFDerivAt Φ Φ' y) :
    HasFDerivAt (fun z ↦ (𝐞 (Φ z) : ℂ)) (Φ'.smulRight (2 * Real.pi * Complex.I * 𝐞 (Φ y))) y := by
  refine ((Real.hasDerivAt_fourierChar (Φ y)).hasFDerivAt.comp y hΦ).congr_fderiv ?_
  ext w
  simp [mul_comm]
