/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Energy
public import TauCeti.Analysis.PDE.Vortex.GaugeFixed
public import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Covariant translations of a plane vortex

Translating a plane vortex `x = (a, α)` along a real tangent vector `v` gives a curve of
vortices, and its velocity `∂_v x` solves the linearized equation. In general it does not
satisfy the gauge-fixing condition `d₀* = 0`, so it is not in the kernel of the gauge-fixed
operator `L_x = d₀* ⊕ d₁`. Adding the infinitesimal gauge transformation by the connection
component `a(v)` corrects this. The result is the **covariant translation**

  `y_v = (ι_v F_a, ∇_v α)`,

with `∇ = d + a`. It is the variation `∂_v x + d₀ (b(v))`, where `a = i b`
(`TauCeti.Vortex.covariantTranslation_eq_fderiv_add_gaugeDirection`).

At every point where the vortex equation holds nearby, `L_x y_v = 0`
(`TauCeti.Vortex.gaugeFixedOperator_covariantTranslation_of_equation_eq_zero`). The rows of
`d₁` vanish because `d₁ (∂_v x)` is the derivative of the equation along `v` and `d₁ d₀ = 0`.
The gauge-fixing row `d₀* y_v = v₁ ∂₂ κ - v₂ ∂₁ κ + Im (conj φ ∇_v φ)`, with `φ = α / 2` and
`F_a = i κ ds ∧ dt`, vanishes by the curvature equation `κ = (|α|² - 1) / 8` and holomorphy
`∇₂ φ = i ∇₁ φ`.

For a vortex with unit-modulus end, `y_v` is square integrable, since `|y_v|²` is bounded by
`|v|²` times the energy density (`TauCeti.Vortex.memLp_covariantTranslation`). The map
`v ↦ y_v` is real-linear. It is injective once the section has a zero
(`TauCeti.Vortex.covariantTranslation_injective`): if `∇_v α` vanished identically, `|α|`
would be constant along the lines in direction `v`, and could not tend to one from a zero.
Therefore the `L²` kernel of `L_x` at such a vortex contains the two-dimensional real space of
covariant translations. Geometrically they move all zeros of the vortex by the same vector.
Identifying them with tangent vectors to the divisor space `Sym^m ℂ` needs the smooth family of
vortices, which is not constructed here. The remaining kernel directions, the Fredholm property
of `L_x` and its index are not treated here either.

## Main declarations

* `TauCeti.Vortex.covariantTranslation x v`: the variation `(ι_v F_a, ∇_v α)`.
* `TauCeti.Vortex.sectionValue_covariantTranslation`: its section part is `∇_v α`.
* `TauCeti.Vortex.gaugeAdjoint_covariantTranslation_of_equation_eq_zero` and
  `TauCeti.Vortex.linearizedEquation_covariantTranslation_of_equation_eq_zero`: `d₀* y_v = 0`
  and `d₁ y_v = 0` at a vortex.
* `TauCeti.Vortex.gaugeFixedOperator_covariantTranslation_of_equation_eq_zero`: `L_x y_v = 0`.
* `TauCeti.Vortex.memLp_covariantTranslation`: `y_v ∈ L²`.
* `TauCeti.Vortex.covariantTranslation_injective`: `v ↦ y_v` is injective when the section
  has a zero and unit modulus at infinity.

## References

* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III.
* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277--292.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open Complex Filter MeasureTheory Topology

variable {x : ℂ → EuclideanSpace ℝ (Fin 4)} {z : ℂ}

/-- The **covariant translation** `(ι_v F_a, ∇_v α)` of the field `x` along a real tangent
vector `v`, as a variation in the coordinates of `linearizedEquation`. With `F_a = i κ ds ∧ dt`,
its connection part is `ι_v F_a = i κ (-v₂ ds + v₁ dt)`, and its section part is the covariant
derivative `∇_v α = ∂_v α + i b(v) α`, where `a = i b` (`sectionValue_covariantTranslation`). -/
def covariantTranslation (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v z : ℂ) :
    EuclideanSpace ℝ (Fin 4) :=
  !₂[-v.im * curvature x z, v.re * curvature x z,
    fderiv ℝ (fun w ↦ x w 2) z v - (x z 0 * v.re + x z 1 * v.im) * x z 3,
    fderiv ℝ (fun w ↦ x w 3) z v + (x z 0 * v.re + x z 1 * v.im) * x z 2]

/-- The first connection component of the covariant translation. -/
@[simp]
theorem covariantTranslation_apply_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v z : ℂ) :
    covariantTranslation x v z 0 = -v.im * curvature x z := by
  rfl

/-- The second connection component of the covariant translation. -/
@[simp]
theorem covariantTranslation_apply_one (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v z : ℂ) :
    covariantTranslation x v z 1 = v.re * curvature x z := by
  rfl

/-- The real section component of the covariant translation. -/
@[simp]
theorem covariantTranslation_apply_two (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v z : ℂ) :
    covariantTranslation x v z 2 =
      fderiv ℝ (fun w ↦ x w 2) z v - (x z 0 * v.re + x z 1 * v.im) * x z 3 := by
  rfl

/-- The imaginary section component of the covariant translation. -/
@[simp]
theorem covariantTranslation_apply_three (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v z : ℂ) :
    covariantTranslation x v z 3 =
      fderiv ℝ (fun w ↦ x w 3) z v + (x z 0 * v.re + x z 1 * v.im) * x z 2 := by
  rfl

/-- The covariant translation along the zero vector vanishes. -/
@[simp]
theorem covariantTranslation_zero (x : ℂ → EuclideanSpace ℝ (Fin 4)) :
    covariantTranslation x 0 = 0 := by
  ext z i
  fin_cases i <;> simp

/-- The covariant translation is additive in the tangent vector. -/
theorem covariantTranslation_add (x : ℂ → EuclideanSpace ℝ (Fin 4)) (v w : ℂ) :
    covariantTranslation x (v + w) = covariantTranslation x v + covariantTranslation x w := by
  ext z i
  fin_cases i <;> simp <;> ring

/-- The covariant translation is homogeneous for real scalars. -/
theorem covariantTranslation_smul (x : ℂ → EuclideanSpace ℝ (Fin 4)) (c : ℝ) (v : ℂ) :
    covariantTranslation x (c • v) = c • covariantTranslation x v := by
  ext z i
  fin_cases i <;> simp [-Complex.real_smul, map_smul, Complex.smul_re, Complex.smul_im] <;> ring

/-- The section part of the covariant translation along `v` is the covariant derivative
`∇_v α`. -/
theorem sectionValue_covariantTranslation (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (v : ℂ) :
    sectionValue (covariantTranslation x v) z = covariantDerivative x z v := by
  have hsfun := funext (sectionValue_apply x)
  have hcastp := (ofRealCLM.hasFDerivAt.comp z hp.hasFDerivAt).fderiv
  have hcastq := (ofRealCLM.hasFDerivAt.comp z hq.hasFDerivAt).fderiv
  simp only [Function.comp_def, ofRealCLM_apply] at hcastp hcastq
  rw [covariantDerivative_apply, hsfun]
  simp (disch := fun_prop) only [sectionValue_apply, covariantTranslation_apply_two,
    covariantTranslation_apply_three, fderiv_const_mul, fderiv_fun_add, fderiv_fun_mul,
    hcastp, hcastq, fderiv_const_apply]
  apply Complex.ext <;> simp <;> ring

/-- The covariant translation is the translation velocity `∂_v x` corrected by the
infinitesimal gauge transformation by the connection component `b(v) = b₁ v₁ + b₂ v₂`. -/
theorem covariantTranslation_eq_fderiv_add_gaugeDirection (hx : DifferentiableAt ℝ x z)
    (v : ℂ) :
    covariantTranslation x v z =
      fderiv ℝ x z v + gaugeDirection x (fun w ↦ x w 0 * v.re + x w 1 * v.im) z := by
  have hxi (i : Fin 4) : DifferentiableAt ℝ (fun w ↦ x w i) z :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).differentiableAt).comp z hx
  have hdi (i : Fin 4) (u : ℂ) : fderiv ℝ x z u i = fderiv ℝ (fun w ↦ x w i) z u := by
    have h := ((EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp z hx.hasFDerivAt).fderiv
    exact (congrArg (fun L : ℂ →L[ℝ] ℝ ↦ L u) h).symm
  have hlin (i : Fin 4) : fderiv ℝ (fun w ↦ x w i) z v =
      v.re * fderiv ℝ (fun w ↦ x w i) z 1 + v.im * fderiv ℝ (fun w ↦ x w i) z I := by
    simpa using LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ (fun w ↦ x w i) z : ℂ →ₗ[ℝ] ℝ) v
  ext i
  fin_cases i
  · simp (disch := fun_prop) [hdi, curvature_apply, fderiv_fun_add, fderiv_mul_const, hlin 0]
    ring
  · simp (disch := fun_prop) [hdi, curvature_apply, fderiv_fun_add, fderiv_mul_const, hlin 1]
    ring
  · simp [hdi]
    ring
  · simp [hdi]

/-- At a point where the vortex equation holds nearby, the curvature coefficient agrees near
the point with `|φ|² / 2 - 1 / 8`, where `φ = p + i q`. -/
private theorem curvature_eventuallyEq (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) :
    curvature x =ᶠ[𝓝 z] fun w ↦ (2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹) :=
  hsol.mono fun w hw ↦ by
    rw [curvature_apply, curvature_eq_of_equation_eq_zero hw]
    ring

/-- **The gauge-fixing row.** At a point where the vortex equation holds nearby, the covariant
translations satisfy the pointwise gauge-fixing condition `d₀* y_v = 0` there. -/
theorem gaugeAdjoint_covariantTranslation_of_equation_eq_zero
    (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z) (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z)
    (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (v : ℂ) :
    gaugeAdjoint x (covariantTranslation x v) z = 0 := by
  have hκ := curvature_eventuallyEq hsol
  have h0 : (fun w ↦ covariantTranslation x v w 0) =ᶠ[𝓝 z]
      fun w ↦ -v.im * ((2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹)) :=
    hκ.mono fun w hw ↦ by simp [hw]
  have h1 : (fun w ↦ covariantTranslation x v w 1) =ᶠ[𝓝 z]
      fun w ↦ v.re * ((2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹)) :=
    hκ.mono fun w hw ↦ by simp [hw]
  have he1 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 1) hsol.self_of_nhds
  have he2 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 2) hsol.self_of_nhds
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply] at he1 he2
  have hlin (i : Fin 4) : fderiv ℝ (fun w ↦ x w i) z v =
      v.re * fderiv ℝ (fun w ↦ x w i) z 1 + v.im * fderiv ℝ (fun w ↦ x w i) z I := by
    simpa using LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ (fun w ↦ x w i) z : ℂ →ₗ[ℝ] ℝ) v
  rw [gaugeAdjoint_def, h0.fderiv_eq, h1.fderiv_eq]
  simp (disch := fun_prop) only [fderiv_const_mul, fderiv_sub_const,
    fderiv_fun_add, fderiv_fun_pow, covariantTranslation_apply_two,
    covariantTranslation_apply_three, hlin 2, hlin 3]
  simp
  linear_combination (v.re * x z 2 - v.im * x z 3) * he2 +
    (-(v.re * x z 3) - v.im * x z 2) * he1

/-- **The linearized equation.** At a point where the vortex equation holds nearby, the
covariant translations solve the linearized vortex equation: `d₁ y_v = 0`. -/
theorem linearizedEquation_covariantTranslation_of_equation_eq_zero
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (v : ℂ) :
    linearizedEquation x (covariantTranslation x v) z = 0 := by
  have hp' := hp.differentiableAt (by norm_num)
  have hq' := hq.differentiableAt (by norm_num)
  have hdp := (hp.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hdq := (hq.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsp := hp.isSymmSndFDerivAt (by norm_num)
  have hsq := hq.isSymmSndFDerivAt (by norm_num)
  have hκ := curvature_eventuallyEq hsol
  have h0 : (fun w ↦ covariantTranslation x v w 0) =ᶠ[𝓝 z]
      fun w ↦ -v.im * ((2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹)) :=
    hκ.mono fun w hw ↦ by simp [hw]
  have h1 : (fun w ↦ covariantTranslation x v w 1) =ᶠ[𝓝 z]
      fun w ↦ v.re * ((2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹)) :=
    hκ.mono fun w hw ↦ by simp [hw]
  -- Differentiate the two holomorphicity rows of the equation along `v`.
  have hrow (i : Fin 3) : fderiv ℝ (fun w ↦ equation x w i) z v = 0 := by
    have he : (fun w ↦ equation x w i) =ᶠ[𝓝 z] fun _ ↦ 0 :=
      hsol.mono fun w hw ↦ by simp [hw]
    rw [he.fderiv_eq]
    simp
  have hr1 := hrow 1
  have hr2 := hrow 2
  simp (disch := fun_prop) only [equation_apply_one, equation_apply_two,
    fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
    fderiv_clm_apply hdp (differentiableAt_const _),
    fderiv_clm_apply hdq (differentiableAt_const _),
    add_apply, sub_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
    ContinuousLinearMap.comp_zero, zero_add,
    ContinuousLinearMap.flip_apply] at hr1 hr2
  have he1 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 1) hsol.self_of_nhds
  have he2 := congrArg (fun e : EuclideanSpace ℝ (Fin 3) ↦ e 2) hsol.self_of_nhds
  simp only [equation_apply_one, equation_apply_two, PiLp.zero_apply] at he1 he2
  have hlin (i : Fin 4) : fderiv ℝ (fun w ↦ x w i) z v =
      v.re * fderiv ℝ (fun w ↦ x w i) z 1 + v.im * fderiv ℝ (fun w ↦ x w i) z I := by
    simpa using LinearMap.apply_eq_re_smul_one_add_im_smul_I
      (fderiv ℝ (fun w ↦ x w i) z : ℂ →ₗ[ℝ] ℝ) v
  have r0 : linearizedEquation x (covariantTranslation x v) z 0 = 0 := by
    simp only [linearizedEquation_apply_zero]
    rw [h0.fderiv_eq, h1.fderiv_eq]
    simp (disch := fun_prop) only [fderiv_const_mul, fderiv_sub_const,
      fderiv_fun_add, fderiv_fun_pow, covariantTranslation_apply_two,
      covariantTranslation_apply_three, hlin 2, hlin 3]
    simp
    ring
  have r1 : linearizedEquation x (covariantTranslation x v) z 1 = 0 := by
    simp (disch := fun_prop) only [linearizedEquation_apply_one, covariantTranslation_apply_zero,
      covariantTranslation_apply_one, covariantTranslation_apply_two,
      covariantTranslation_apply_three, fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
      fderiv_clm_apply hdp (differentiableAt_const _),
      fderiv_clm_apply hdq (differentiableAt_const _),
      add_apply, sub_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_apply, zero_add,
      ContinuousLinearMap.flip_apply, hsp.eq _ v, hsq.eq _ v, curvature_apply]
    simp only [hlin 0, hlin 1] at hr1 hr2 ⊢
    simp
    linear_combination hr1 - (x z 0 * v.re + x z 1 * v.im) * he2
  have r2 : linearizedEquation x (covariantTranslation x v) z 2 = 0 := by
    simp (disch := fun_prop) only [linearizedEquation_apply_two, covariantTranslation_apply_zero,
      covariantTranslation_apply_one, covariantTranslation_apply_two,
      covariantTranslation_apply_three, fderiv_fun_sub, fderiv_fun_add, fderiv_fun_mul,
      fderiv_clm_apply hdp (differentiableAt_const _),
      fderiv_clm_apply hdq (differentiableAt_const _),
      add_apply, sub_apply, smul_apply, smul_eq_mul, fderiv_const_apply,
      ContinuousLinearMap.comp_zero, zero_apply, zero_add,
      ContinuousLinearMap.flip_apply, hsp.eq _ v, hsq.eq _ v, curvature_apply]
    simp only [hlin 0, hlin 1] at hr1 hr2 ⊢
    simp
    linear_combination hr2 + (x z 0 * v.re + x z 1 * v.im) * he1
  ext i
  fin_cases i
  exacts [r0, r1, r2]

/-- **Covariant translations are in the kernel of the gauge-fixed operator.** At a point where
the vortex equation holds nearby, `L_x y_v = 0` for every real tangent vector `v`. -/
theorem gaugeFixedOperator_covariantTranslation_of_equation_eq_zero
    (hb₁ : DifferentiableAt ℝ (fun w ↦ x w 0) z) (hb₂ : DifferentiableAt ℝ (fun w ↦ x w 1) z)
    (hp : ContDiffAt ℝ 2 (fun w ↦ x w 2) z) (hq : ContDiffAt ℝ 2 (fun w ↦ x w 3) z)
    (hsol : ∀ᶠ w in 𝓝 z, equation x w = 0) (v : ℂ) :
    gaugeFixedOperator x (covariantTranslation x v) z = 0 := by
  have h₀ := gaugeAdjoint_covariantTranslation_of_equation_eq_zero
    (hp.differentiableAt (by norm_num)) (hq.differentiableAt (by norm_num)) hsol v
  have h := linearizedEquation_covariantTranslation_of_equation_eq_zero hb₁ hb₂ hp hq hsol v
  ext i
  fin_cases i
  · simpa using h₀
  · simpa using congrArg (· 0) h
  · simpa using congrArg (· 1) h
  · simpa using congrArg (· 2) h

/-- The pointwise size of a covariant translation is controlled by the energy density:
`|y_v|² ≤ |v|² (|F_a|² + |d_a α|² + (1 - |α|²)²)`. -/
theorem norm_covariantTranslation_sq_le (hp : DifferentiableAt ℝ (fun w ↦ x w 2) z)
    (hq : DifferentiableAt ℝ (fun w ↦ x w 3) z) (v : ℂ) :
    ‖covariantTranslation x v z‖ ^ 2 ≤ ‖v‖ ^ 2 * energyDensity x z := by
  have hs := sectionValue_covariantTranslation hp hq v
  have hsec : covariantTranslation x v z 2 ^ 2 + covariantTranslation x v z 3 ^ 2 =
      ‖covariantDerivative x z v‖ ^ 2 / 4 := by
    rw [← hs, sq_norm_sectionValue]
    ring
  have hcd := covariantDerivative_eq_re_mul_add_im_mul x z v
  have htri : ‖covariantDerivative x z v‖ ≤
      |v.re| * ‖covariantDerivative x z 1‖ + |v.im| * ‖covariantDerivative x z I‖ := by
    rw [hcd]
    refine (norm_add_le _ _).trans ?_
    simp
  have hv : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hcs : ‖covariantDerivative x z v‖ ^ 2 ≤
      ‖v‖ ^ 2 * (‖covariantDerivative x z 1‖ ^ 2 + ‖covariantDerivative x z I‖ ^ 2) := by
    rw [hv]
    have h0 : 0 ≤ ‖covariantDerivative x z v‖ := norm_nonneg _
    nlinarith [sq_nonneg (|v.re| * ‖covariantDerivative x z I‖ -
      |v.im| * ‖covariantDerivative x z 1‖), sq_abs v.re, sq_abs v.im,
      mul_nonneg (abs_nonneg v.re) (norm_nonneg (covariantDerivative x z 1)),
      mul_nonneg (abs_nonneg v.im) (norm_nonneg (covariantDerivative x z I))]
  rw [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_four, energyDensity_apply]
  simp only [covariantTranslation_apply_zero, covariantTranslation_apply_one]
  nlinarith [sq_nonneg (1 - ‖sectionValue x z‖ ^ 2), sq_nonneg v.re, sq_nonneg v.im,
    sq_nonneg (curvature x z), sq_nonneg ‖v‖]

section Integrability

variable (μ : Measure ℂ) [μ.IsAddHaarMeasure]

/-- The covariant translations of a classical vortex with unit-modulus section at infinity are
square integrable. No decay of the connection or of the derivatives is assumed. -/
theorem memLp_covariantTranslation
    (hb₁ : Differentiable ℝ (fun w ↦ x w 0)) (hb₂ : Differentiable ℝ (fun w ↦ x w 1))
    (hp : ContDiff ℝ 2 (fun w ↦ x w 2)) (hq : ContDiff ℝ 2 (fun w ↦ x w 3))
    (hsol : ∀ z, equation x z = 0)
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) (v : ℂ) :
    MemLp (covariantTranslation x v) 2 μ := by
  have hκ : curvature x = fun w ↦ 2⁻¹ * (x w 2 ^ 2 + x w 3 ^ 2) - 8⁻¹ :=
    funext fun w ↦ (curvature_eventuallyEq (Eventually.of_forall hsol) (z := w)).self_of_nhds
  have hpc := hp.continuous
  have hqc := hq.continuous
  have hcκ : Continuous (curvature x) := by
    rw [hκ]
    exact (continuous_const.mul ((hpc.pow 2).add (hqc.pow 2))).sub continuous_const
  have hdp := (hp.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := v))
  have hdq := (hq.continuous_fderiv (by norm_num)).clm_apply (continuous_const (y := v))
  have hb : Continuous fun w ↦ x w 0 * v.re + x w 1 * v.im :=
    (hb₁.continuous.mul continuous_const).add (hb₂.continuous.mul continuous_const)
  have h₀ : Continuous fun z ↦ covariantTranslation x v z 0 := by
    simp only [covariantTranslation_apply_zero]
    exact continuous_const.mul hcκ
  have h₁ : Continuous fun z ↦ covariantTranslation x v z 1 := by
    simp only [covariantTranslation_apply_one]
    exact continuous_const.mul hcκ
  have h₂ : Continuous fun z ↦ covariantTranslation x v z 2 := by
    simp only [covariantTranslation_apply_two]
    exact hdp.sub (hb.mul hqc)
  have h₃ : Continuous fun z ↦ covariantTranslation x v z 3 := by
    simp only [covariantTranslation_apply_three]
    exact hdq.add (hb.mul hpc)
  have hcont : Continuous (covariantTranslation x v) := by
    refine (PiLp.continuous_toLp 2 _).comp (continuous_pi fun i ↦ ?_)
    fin_cases i
    exacts [h₀, h₁, h₂, h₃]
  have hI : Integrable (fun z ↦ ‖v‖ ^ 2 * energyDensity x z) μ :=
    (integrable_energyDensity μ hb₁ hb₂ hp hq hsol hlim).const_mul _
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  refine hI.mono' (hcont.norm.pow 2).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact norm_covariantTranslation_sq_le (hp.differentiable (by norm_num) z)
    (hq.differentiable (by norm_num) z) v

end Integrability

/-- **The covariant translations are independent.** If the section of `x` has a zero and unit
modulus at infinity, then a covariant translation vanishes identically only along `v = 0`. -/
theorem covariantTranslation_eq_zero_iff (hp : Differentiable ℝ (fun w ↦ x w 2))
    (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {z₀ : ℂ}
    (hz₀ : sectionValue x z₀ = 0) {v : ℂ} :
    covariantTranslation x v = 0 ↔ v = 0 := by
  refine ⟨fun hy ↦ ?_, fun hv ↦ hv ▸ covariantTranslation_zero x⟩
  by_contra hv
  -- Along the line `t ↦ z₀ + t v` the modulus `|α|²` has derivative `2 Re (conj α ∇_v α) = 0`.
  set g : ℝ → ℝ := fun t ↦ 4 * (x (z₀ + t • v) 2 ^ 2 + x (z₀ + t • v) 3 ^ 2) with hg
  have hderiv (t : ℝ) : HasDerivAt g 0 t := by
    have hl : HasDerivAt (fun t : ℝ ↦ z₀ + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add z₀
    have hp' : HasDerivAt (fun s : ℝ ↦ x (z₀ + s • v) 2)
        (fderiv ℝ (fun w ↦ x w 2) (z₀ + t • v) v) t := by
      simpa [Function.comp_def] using
        (hp (z₀ + t • v)).hasFDerivAt.comp_hasDerivAt t hl
    have hq' : HasDerivAt (fun s : ℝ ↦ x (z₀ + s • v) 3)
        (fderiv ℝ (fun w ↦ x w 3) (z₀ + t • v) v) t := by
      simpa [Function.comp_def] using
        (hq (z₀ + t • v)).hasFDerivAt.comp_hasDerivAt t hl
    have h2 := congrArg (fun y : ℂ → EuclideanSpace ℝ (Fin 4) ↦ y (z₀ + t • v) 2) hy
    have h3 := congrArg (fun y : ℂ → EuclideanSpace ℝ (Fin 4) ↦ y (z₀ + t • v) 3) hy
    simp only [covariantTranslation_apply_two, covariantTranslation_apply_three, Pi.zero_apply,
      PiLp.zero_apply] at h2 h3
    convert ((hp'.fun_pow 2).add (hq'.fun_pow 2)).const_mul 4 using 1
    linear_combination (-8 * x (z₀ + t • v) 2) * h2 - 8 * x (z₀ + t • v) 3 * h3
  have hconst (t : ℝ) : g t = g 0 :=
    is_const_of_deriv_eq_zero (fun t ↦ (hderiv t).differentiableAt)
      (fun t ↦ (hderiv t).deriv) t 0
  have hg0 : g 0 = 0 := by
    have := sq_norm_sectionValue x z₀
    rw [hz₀, norm_zero] at this
    simp only [hg, zero_smul, add_zero]
    linarith
  have hline : Tendsto (fun t : ℝ ↦ z₀ + t • v) atTop (cocompact ℂ) := by
    refine tendsto_cocompact_of_tendsto_dist_comp_atTop z₀ ?_
    have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine (tendsto_id.atTop_mul_const hv').congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht, id]
  have hlim' := hlim.comp hline
  have : Tendsto g atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun t ↦ ((hconst t).trans hg0).symm
  exact one_ne_zero (tendsto_nhds_unique hlim' this)

/-- If the section of `x` has a zero and unit modulus at infinity, then `v ↦ y_v` is
injective, so the covariant translations span a two-dimensional real space of variations. -/
theorem covariantTranslation_injective (hp : Differentiable ℝ (fun w ↦ x w 2))
    (hq : Differentiable ℝ (fun w ↦ x w 3))
    (hlim : Tendsto (fun z ↦ 4 * (x z 2 ^ 2 + x z 3 ^ 2)) (cocompact ℂ) (𝓝 1)) {z₀ : ℂ}
    (hz₀ : sectionValue x z₀ = 0) :
    Function.Injective (covariantTranslation x) := by
  intro v w h
  have hsub : covariantTranslation x (v - w) = 0 := by
    have := covariantTranslation_add x (v - w) w
    rw [sub_add_cancel, h] at this
    simpa using this.symm
  exact sub_eq_zero.1 ((covariantTranslation_eq_zero_iff hp hq hlim hz₀).1 hsub)

end TauCeti.Vortex
