/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Haar.Basic
public import Mathlib.Basic.ENNReal.Holder
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.MeanInequalities
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.Convex.Sequence.LogConvex
import TauCeti.Data.ENNReal.Holder
import TauCeti.Analysis.InnerProductSpace.NormPow
import TauCeti.Analysis.MeanInequalities
import TauCeti.Analysis.Normed.Module.Multilinear.Basis

/-!
# The Gagliardo–Nirenberg interpolation inequality and the Moser product estimate

Let `E` be a finite-dimensional real normed space with an additive Haar measure `μ`, and let
`2 ≤ p < ∞`. This file proves the Gagliardo–Nirenberg inequality for intermediate derivatives with
an `L^∞` endpoint: for `0 ≤ j ≤ k`, `k ≠ 0`, and `1 / q = (j / k) (1 / p)`,

`‖D^j u‖_{L^q} ≤ C ‖u‖_{L^∞} ^ (1 - j / k) ‖D^k u‖_{L^p} ^ (j / k)`

for every `C^k` function `u : E → F` with compact support, with values in a real inner product
space `F` (`TauCeti.exists_eLpNorm_iteratedFDeriv_le`). As a consequence, for a continuous bilinear
map `B` the `k`-th derivative of `x ↦ B (u x) (v x)` satisfies the Moser product estimate

`‖D^k (B (u, v))‖_{L^p} ≤ C ‖B‖ (‖u‖_{L^∞} ‖D^k v‖_{L^p} + ‖D^k u‖_{L^p} ‖v‖_{L^∞})`

(`TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le`). This is the estimate behind the algebra
property of `W^{k,p} ∩ L^∞` and behind bootstrap arguments for nonlinear elliptic equations, in
which `B (u, u)` is shown to be as regular as `u`.

## The argument

The basic step (`ContDiff.eLpNorm_fderiv_apply_sq_le`) is the inequality
`‖∂ᵥU‖_q ^ 2 ≤ (q - 1) ‖U‖_a ‖∂ᵥ²U‖_b` for `1 / a + 1 / b = 2 / q` and `2 ≤ q < ∞`. With
`w = ∂ᵥU`, integration by parts against `‖w‖ ^ (q - 2) • w`, whose derivative along `v` has norm at
most `(q - 1) ‖w‖ ^ (q - 2) ‖∂ᵥw‖` (`TauCeti.hasFDerivAt_norm_rpow_smul_self`), gives

`∫ ‖w‖ ^ q = -∫ ⟪U, ∂ᵥ(‖w‖ ^ (q - 2) • w)⟫ ≤ (q - 1) ∫ ‖U‖ ‖w‖ ^ (q - 2) ‖∂ᵥw‖`,

and Hölder's inequality bounds the right side by `(q - 1) ‖U‖_a ‖∂ᵥw‖_b ‖w‖_q ^ (q - 2)`.

Applied to the partial derivatives along a basis, with `q = k p / j`, `a = k p / (j - 1)` and
`b = k p / (j + 1)`, it shows that the sums `a_j` of the `L^{k p / j}` norms of the partial
derivatives of order `j` satisfy `a_j ^ 2 ≤ c a_{j-1} a_{j+1}` for `0 < j < k`; here `q ≥ p ≥ 2`.
Such a sequence is logarithmically convex up to a constant, so
`a_j ^ k ≤ C a_0 ^ (k - j) a_k ^ j` (`TauCeti.pow_le_mul_pow_mul_pow_of_sq_le_mul`), with
`a_0 = ‖u‖_∞`. The full derivative is compared with its partial derivatives by
`ContinuousMultilinearMap.opNorm_le_prod_mul_sum_norm_apply_basis`.

The product estimate follows from the Leibniz rule in `L^p`
`ContinuousLinearMap.eLpNorm_iteratedFDeriv_le_of_bilinear`, with the exponents
`k p / i` and `k p / (k - i)`, the Gagliardo–Nirenberg inequality for both factors, and the
weighted arithmetic-geometric mean inequality.

The integration-by-parts step needs `q ≥ 2`, which is why `p ≥ 2` is assumed; the inequality also
holds for `1 ≤ p < 2`, by a different argument.

## Main results

* `ContDiff.eLpNorm_fderiv_apply_sq_le`: the one-step inequality
  `‖∂ᵥU‖_q ^ 2 ≤ (q - 1) ‖U‖_a ‖∂ᵥ²U‖_b`.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_le`: the Gagliardo–Nirenberg inequality.
* `TauCeti.exists_eLpNorm_iteratedFDeriv_bilinear_le`: the Moser product estimate.

## References

* L. Nirenberg, *On elliptic partial differential equations*, Ann. Scuola Norm. Sup. Pisa (3) 13
  (1959), 115–162.
* M. E. Taylor, *Partial Differential Equations III*, 2nd ed., Springer, 2011, Chapter 13, §3.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The derivative `‖y‖ ^ r • id + (r ‖y‖ ^ (r - 2) ⟪y, ·⟫) y` of `y ↦ ‖y‖ ^ r • y` at `y`
(`TauCeti.hasFDerivAt_norm_rpow_smul_self`). -/
private noncomputable def normRpowSmulDeriv (r : ℝ) (y : F) : F →L[ℝ] F :=
  ‖y‖ ^ r • ContinuousLinearMap.id ℝ F + ((r * ‖y‖ ^ (r - 2)) • innerSL ℝ y).smulRight y

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The test field `x ↦ ‖w x‖ ^ r • w x` of a `C¹` map `w` has line derivative
`normRpowSmulDeriv r (w x) (∂ᵥ w x)` along `v`. -/
private theorem hasLineDerivAt_norm_rpow_smul {w : E → F} (hw : ContDiff ℝ 1 w) {r : ℝ}
    (hr : 0 ≤ r) (x v : E) :
    HasLineDerivAt ℝ (fun y ↦ ‖w y‖ ^ r • w y) (normRpowSmulDeriv r (w x) (fderiv ℝ w x v))
    x v := by
  have h := ((hasFDerivAt_norm_rpow_smul_self hr (w x)).comp x
    ((hw.differentiable one_ne_zero) x).hasFDerivAt).hasLineDerivAt v
  rw [Function.comp_def, ContinuousLinearMap.comp_apply] at h
  rwa [normRpowSmulDeriv]

private theorem norm_normRpowSmulDeriv_apply_le {r : ℝ} (hr : 0 ≤ r) (y z : F) :
    ‖normRpowSmulDeriv r y z‖ ≤ (1 + r) * ‖y‖ ^ r * ‖z‖ := by
  refine ((normRpowSmulDeriv r y).le_opNorm z).trans ?_
  rw [normRpowSmulDeriv]
  have h := norm_rpow_smul_id_add_smulRight_le r y
  rw [abs_of_nonneg hr] at h
  exact mul_le_mul_of_nonneg_right h (norm_nonneg _)

omit [μ.IsAddHaarMeasure] in
private theorem aestronglyMeasurable_normRpowSmulDeriv_apply {w w' : E → F} (hw : Continuous w)
    (hw' : Continuous w') (r : ℝ) :
    AEStronglyMeasurable (fun x ↦ normRpowSmulDeriv r (w x) (w' x)) μ := by
  have hwm : Measurable fun x ↦ ‖w x‖ := hw.norm.measurable
  have heq : (fun x ↦ normRpowSmulDeriv r (w x) (w' x)) =
      fun x ↦ ‖w x‖ ^ r • w' x + (r * ‖w x‖ ^ (r - 2) * ⟪w x, w' x⟫) • w x := by
    funext x
    simp [normRpowSmulDeriv, mul_smul]
  rw [heq]
  refine ((hwm.pow_const r).aestronglyMeasurable.smul hw'.aestronglyMeasurable).add ?_
  exact (((hwm.pow_const (r - 2)).const_mul r).aestronglyMeasurable.mul
    (hw.inner hw').aestronglyMeasurable).smul hw.aestronglyMeasurable

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The directional derivative `∂ᵥw` of a `C¹` map is continuous. -/
private theorem continuous_fderiv_apply_const {w : E → F} (hw : ContDiff ℝ 1 w) (v : E) :
    Continuous fun x ↦ fderiv ℝ w x v :=
  (hw.continuous_fderiv one_ne_zero).clm_apply continuous_const

omit [NormedSpace ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E] [MeasurableSpace E]
  [BorelSpace E] in
/-- The weight `x ↦ ‖w x‖ ^ r` of a continuous map `w` and an exponent `r ≥ 0` is continuous. -/
private theorem continuous_norm_rpow {w : E → F} (hw : Continuous w) {r : ℝ} (hr : 0 ≤ r) :
    Continuous fun x ↦ ‖w x‖ ^ r :=
  hw.norm.rpow_const fun _ ↦ Or.inr hr

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- The directional derivative `∂ᵥU` of a `C²` map is `C¹`. -/
private theorem contDiff_one_fderiv_apply {U : E → F} (hU : ContDiff ℝ 2 U) (v : E) :
    ContDiff ℝ 1 fun x ↦ fderiv ℝ U x v :=
  (hU.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

/-- Integration by parts against the test field `‖w‖ ^ (q - 2) • w`, for `w = ∂ᵥU`:
`∫ ‖w‖ ^ q = -∫ ⟪U, ∂ᵥ(‖w‖ ^ (q - 2) • w)⟫`. -/
private theorem integral_norm_fderiv_apply_rpow_eq {U : E → F} (hU : ContDiff ℝ 2 U)
    (hc : HasCompactSupport U) (v : E) {q : ℝ} (hq : 2 ≤ q) :
    ∫ x, ‖fderiv ℝ U x v‖ ^ q ∂μ = -∫ x, ⟪U x, normRpowSmulDeriv (q - 2) (fderiv ℝ U x v)
      (fderiv ℝ (fun y ↦ fderiv ℝ U y v) x v)⟫ ∂μ := by
  have hr : 0 ≤ q - 2 := by linarith
  set w : E → F := fun x ↦ fderiv ℝ U x v
  set g : E → F := fun x ↦ ‖w x‖ ^ (q - 2) • w x
  have hw : ContDiff ℝ 1 w := contDiff_one_fderiv_apply hU v
  have hw' : Continuous fun x ↦ fderiv ℝ w x v := continuous_fderiv_apply_const hw v
  have hwr : Continuous fun x ↦ ‖w x‖ ^ (q - 2) := continuous_norm_rpow hw.continuous hr
  have hgc : Continuous g := hwr.smul hw.continuous
  have hdom : Continuous fun x ↦ ‖U x‖ * ((1 + (q - 2)) * ‖w x‖ ^ (q - 2) * ‖fderiv ℝ w x v‖) := by
    fun_prop
  have hint : Integrable (fun x ↦ ⟪U x, normRpowSmulDeriv (q - 2) (w x) (fderiv ℝ w x v)⟫) μ :=
    (hdom.integrable_of_hasCompactSupport hc.norm.mul_right).mono'
      (hU.continuous.aestronglyMeasurable.inner
        (aestronglyMeasurable_normRpowSmulDeriv_apply hw.continuous hw' _))
      (Eventually.of_forall fun x ↦ (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_normRpowSmulDeriv_apply_le hr _ _) (norm_nonneg _)))
  have hibp : ∫ x, ⟪U x, normRpowSmulDeriv (q - 2) (w x) (fderiv ℝ w x v)⟫ ∂μ =
      -∫ x, ⟪w x, g x⟫ ∂μ :=
    integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable (B := innerSL ℝ) (v := v)
      ((hw.continuous.inner hgc).integrable_of_hasCompactSupport
        ((hc.fderiv_apply (𝕜 := ℝ) v).mono fun _ hx h0 ↦ hx (by simp [g, show w _ = 0 from h0])))
      hint ((hU.continuous.inner hgc).integrable_of_hasCompactSupport
        (hc.mono fun _ hx h0 ↦ hx (by simp [g, h0])))
      (fun x _ ↦ ((hU.differentiable two_ne_zero) x).hasFDerivAt.hasLineDerivAt v)
      (fun x _ ↦ hasLineDerivAt_norm_rpow_smul hw hr x v)
  have hlhs : ∀ x, ⟪w x, g x⟫ = ‖w x‖ ^ q := by
    intro x
    simp only [g, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg _) (by norm_num; linarith)]
    norm_num
  rw [hibp, neg_neg]
  exact integral_congr_ae (Eventually.of_forall fun x ↦ (hlhs x).symm)

private theorem integral_norm_fderiv_apply_rpow_le {U : E → F} (hU : ContDiff ℝ 2 U)
    (hc : HasCompactSupport U) (v : E) {q : ℝ} (hq : 2 ≤ q) :
    ∫ x, ‖fderiv ℝ U x v‖ ^ q ∂μ ≤
      (q - 1) * ∫ x, ‖U x‖ * ‖fderiv ℝ U x v‖ ^ (q - 2) *
        ‖fderiv ℝ (fun y ↦ fderiv ℝ U y v) x v‖ ∂μ := by
  have hr : 0 ≤ q - 2 := by linarith
  set w : E → F := fun x ↦ fderiv ℝ U x v
  have hw : ContDiff ℝ 1 w := contDiff_one_fderiv_apply hU v
  have hdom : Continuous fun x ↦ ‖U x‖ * ‖w x‖ ^ (q - 2) * ‖fderiv ℝ w x v‖ := by
    have := continuous_norm_rpow hw.continuous hr
    have := continuous_fderiv_apply_const hw v
    fun_prop
  rw [integral_norm_fderiv_apply_rpow_eq hU hc v hq, ← integral_const_mul]
  refine (neg_le_abs _).trans ((abs_integral_le_integral_abs).trans
    (integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ abs_nonneg _)
      ((hdom.integrable_of_hasCompactSupport hc.norm.mul_right.mul_right).const_mul _)
      (Eventually.of_forall fun x ↦ ?_)))
  refine (abs_real_inner_le_norm _ _).trans ?_
  have := mul_le_mul_of_nonneg_left (norm_normRpowSmulDeriv_apply_le hr (w x) (fderiv ℝ w x v))
    (norm_nonneg (U x))
  convert this using 1
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Hölder's inequality for the product of the norms of two functions. -/
private theorem eLpNorm_norm_mul_norm_le {U w' : E → F} (hU : AEStronglyMeasurable U μ)
    (hw' : AEStronglyMeasurable w' μ) {a b r : ℝ≥0∞} [ENNReal.HolderTriple a b r] :
    eLpNorm (fun x ↦ ‖U x‖ * ‖w' x‖) r μ ≤ eLpNorm U a μ * eLpNorm w' b μ := by
  rw [← eLpNorm_norm U hU, ← eLpNorm_norm w' hw']
  exact eLpNorm_smul_le_mul_eLpNorm hU.norm hw'.norm

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [InnerProductSpace ℝ F] [FiniteDimensional ℝ E]
  [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- The `L^(q / (q - 2))` norm of `‖w‖ ^ (q - 2)` is at most the `(q - 2)`-th power of the `L^q`
norm of `w`; for `q = 2` the left side is the `L^∞` norm of the constant `1`. -/
private theorem eLpNorm_norm_rpow_sub_two_le {w : E → F} (hw : AEStronglyMeasurable w μ) {q : ℝ}
    (hq : 2 ≤ q) :
    eLpNorm (fun x ↦ ‖w x‖ ^ (q - 2)) (ENNReal.ofReal ((q - 2) / q))⁻¹ μ ≤
      eLpNorm w (ENNReal.ofReal q) μ ^ (q - 2) := by
  rcases hq.eq_or_lt with rfl | hq2
  · simp only [sub_self, Real.rpow_zero, ENNReal.rpow_zero]
    exact (eLpNorm_le_of_ae_bound (C := 1) aestronglyMeasurable_const
      (Eventually.of_forall fun _ ↦ by simp)).trans (by simp)
  · have hq0 : 0 < q := by linarith
    have hcq : (ENNReal.ofReal ((q - 2) / q))⁻¹ * ENNReal.ofReal (q - 2) = ENNReal.ofReal q := by
      rw [← ENNReal.ofReal_inv_of_pos (div_pos (by linarith) hq0), inv_div,
        ← ENNReal.ofReal_mul (div_nonneg hq0.le (by linarith))]
      congr 1
      field_simp
    rw [eLpNorm_norm_rpow w hw (by linarith), hcq]

omit [InnerProductSpace ℝ F] in
/-- Hölder's inequality for the three factors of the integration-by-parts bound. -/
private theorem ofReal_integral_norm_mul_rpow_mul_norm_le {U w w' : E → F} (hU : Continuous U)
    (hc : HasCompactSupport U) (hw : Continuous w) (hw' : Continuous w') {q : ℝ} (hq : 2 ≤ q)
    {a b : ℝ≥0∞} [ENNReal.HolderTriple a b (ENNReal.ofReal (q / 2))] :
    ENNReal.ofReal (∫ x, ‖U x‖ * ‖w x‖ ^ (q - 2) * ‖w' x‖ ∂μ) ≤
      eLpNorm U a μ * eLpNorm w' b μ * eLpNorm w (ENNReal.ofReal q) μ ^ (q - 2) := by
  have hq0 : 0 < q := by linarith
  have : ENNReal.HolderTriple (ENNReal.ofReal (q / 2)) (ENNReal.ofReal ((q - 2) / q))⁻¹ 1 := by
    constructor
    rw [inv_inv, ← ENNReal.ofReal_inv_of_pos (by positivity), ← ENNReal.ofReal_add
      (by positivity) (div_nonneg (by linarith) hq0.le), inv_one, inv_div]
    rw [show 2 / q + (q - 2) / q = 1 by field_simp; ring, ENNReal.ofReal_one]
  have hwr : Continuous fun x ↦ ‖w x‖ ^ (q - 2) := continuous_norm_rpow hw (by linarith)
  have hint : Integrable (fun x ↦ ‖U x‖ * ‖w x‖ ^ (q - 2) * ‖w' x‖) μ :=
    ((hU.norm.mul hwr).mul hw'.norm).integrable_of_hasCompactSupport
      (hc.norm.mul_right.mul_right)
  rw [ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun x ↦ by positivity)]
  calc ∫⁻ x, ENNReal.ofReal (‖U x‖ * ‖w x‖ ^ (q - 2) * ‖w' x‖) ∂μ
      = eLpNorm (fun x ↦ (‖U x‖ * ‖w' x‖) * ‖w x‖ ^ (q - 2)) 1 μ := by
        rw [eLpNorm_one_eq_lintegral_eNorm (f := fun x ↦ (‖U x‖ * ‖w' x‖) * ‖w x‖ ^ (q - 2))
          ((hU.norm.mul hw'.norm).mul hwr).aestronglyMeasurable]
        refine lintegral_congr fun x ↦ ?_
        rw [Real.eNorm_of_nonneg (by positivity)]
        ring_nf
    _ ≤ eLpNorm (fun x ↦ ‖U x‖ * ‖w' x‖) (ENNReal.ofReal (q / 2)) μ *
          eLpNorm (fun x ↦ ‖w x‖ ^ (q - 2)) (ENNReal.ofReal ((q - 2) / q))⁻¹ μ :=
        eLpNorm_smul_le_mul_eLpNorm (hU.norm.mul hw'.norm).aestronglyMeasurable
          hwr.aestronglyMeasurable
    _ ≤ eLpNorm U a μ * eLpNorm w' b μ * eLpNorm w (ENNReal.ofReal q) μ ^ (q - 2) := by
        gcongr
        · exact eLpNorm_norm_mul_norm_le hU.aestronglyMeasurable hw'.aestronglyMeasurable
        · exact eLpNorm_norm_rpow_sub_two_le hw.aestronglyMeasurable hq

/-- **The one-step interpolation inequality.** For a `C²` function `U` with compact support, a
direction `v` and `2 ≤ q < ∞`, the derivative `∂ᵥU` in `L^q` is controlled by `U` in `L^a` and
`∂ᵥ²U` in `L^b` whenever `1/a + 1/b = 2/q`:
`‖∂ᵥU‖_q ^ 2 ≤ (q - 1) ‖U‖_a ‖∂ᵥ²U‖_b`. -/
theorem _root_.ContDiff.eLpNorm_fderiv_apply_sq_le {U : E → F} (hU : ContDiff ℝ 2 U)
    (hc : HasCompactSupport U)
    (v : E) {q : ℝ} (hq : 2 ≤ q) {a b : ℝ≥0∞} [ENNReal.HolderTriple a b (ENNReal.ofReal (q / 2))] :
    eLpNorm (fun x ↦ fderiv ℝ U x v) (ENNReal.ofReal q) μ ^ 2 ≤
      ENNReal.ofReal (q - 1) * eLpNorm U a μ *
        eLpNorm (fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ U y v) x v) b μ := by
  have hq0 : 0 < q := by linarith
  set w : E → F := fun x ↦ fderiv ℝ U x v
  set w' : E → F := fun x ↦ fderiv ℝ (fun y ↦ fderiv ℝ U y v) x v
  have hw : ContDiff ℝ 1 w := contDiff_one_fderiv_apply hU v
  have hw' : Continuous w' := continuous_fderiv_apply_const hw v
  have hwc : HasCompactSupport w := hc.fderiv_apply (𝕜 := ℝ) v
  have hmem : MemLp w (ENNReal.ofReal q) μ := hw.continuous.memLp_of_hasCompactSupport hwc
  set X := eLpNorm w (ENNReal.ofReal q) μ with hX_def
  -- `X ^ q` is the integral of `‖w‖ ^ q`
  have hXq : X ^ q = ENNReal.ofReal (∫ x, ‖w x‖ ^ q ∂μ) := by
    rw [hX_def, hmem.eLpNorm_eq_integral_rpow_norm (by simpa using hq0) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hq0.le, ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0.le,
      Real.rpow_inv_rpow (integral_nonneg fun x ↦ by positivity) hq0.ne']
  have key : X ^ q ≤ ENNReal.ofReal (q - 1) * eLpNorm U a μ * eLpNorm w' b μ * X ^ (q - 2) := by
    rw [hXq]
    refine (ENNReal.ofReal_le_ofReal (integral_norm_fderiv_apply_rpow_le hU hc v hq)).trans ?_
    rw [ENNReal.ofReal_mul (by linarith), mul_assoc _ (eLpNorm U a μ), mul_assoc]
    gcongr
    exact ofReal_integral_norm_mul_rpow_mul_norm_le hU.continuous hc hw.continuous hw' hq
  rcases eq_or_ne X 0 with hX | hX
  · rw [hX]; simp
  have hXt : X ≠ ⊤ := hmem.eLpNorm_ne_top
  have hsplit : X ^ q = X ^ 2 * X ^ (q - 2) := by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_add _ _ hX hXt]; norm_num
  rw [hsplit] at key
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.rpow_pos (pos_iff_ne_zero.2 hX) hXt).ne'
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) hXt)).1 key

/-- The one-step inequality for partial derivatives along a basis: the derivative along `b i` of
`∂_τ u` is controlled by `∂_τ u` and its second derivative along `b i`. -/
private theorem eLpNorm_iteratedFDeriv_cons_sq_le {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u)
    (hc : HasCompactSupport u) {ι : Type*} (b : ι → E) {j : ℕ} (hj : j + 1 < k) (i : ι)
    (τ : Fin j → ι) {q : ℝ} (hq : 2 ≤ q) {a c : ℝ≥0∞}
    [ENNReal.HolderTriple a c (ENNReal.ofReal (q / 2))] :
    eLpNorm (fun x ↦ iteratedFDeriv ℝ (j + 1) u x (fun l ↦ b ((Fin.cons i τ : Fin (j + 1) → ι) l)))
        (ENNReal.ofReal q) μ ^ 2 ≤
      ENNReal.ofReal (q - 1) * eLpNorm (fun x ↦ iteratedFDeriv ℝ j u x (fun l ↦ b (τ l))) a μ *
        eLpNorm (fun x ↦ iteratedFDeriv ℝ (j + 2) u x
          (fun l ↦ b ((Fin.cons i (Fin.cons i τ : Fin (j + 1) → ι) : Fin (j + 2) → ι) l))) c μ := by
  set U : E → F := fun x ↦ iteratedFDeriv ℝ j u x (fun l ↦ b (τ l))
  have hU : ContDiff ℝ 2 U :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j ↦ E) F (fun l ↦ b (τ l))).contDiff.comp
      (hu.iteratedFDeriv_right (by exact_mod_cast (show 2 + j ≤ k by omega)))
  have hUc : HasCompactSupport U := hc.iteratedFDeriv_apply _
  have h1 : ∀ y, fderiv ℝ U y (b i) =
      iteratedFDeriv ℝ (j + 1) u y (fun l ↦ b ((Fin.cons i τ : Fin (j + 1) → ι) l)) := fun y ↦ by
    rw [fderiv_iteratedFDeriv_apply
      ((hu.differentiable_iteratedFDeriv (by exact_mod_cast (show j < k by omega))) y)]
    exact congrArg _ (Fin.comp_cons b i τ).symm
  have h2 : ∀ x, fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (j + 1) u y
        (fun l ↦ b ((Fin.cons i τ : Fin (j + 1) → ι) l))) x (b i) =
      iteratedFDeriv ℝ (j + 2) u x
        (fun l ↦ b ((Fin.cons i (Fin.cons i τ : Fin (j + 1) → ι) : Fin (j + 2) → ι) l)) :=
    fun x ↦ by
    rw [fderiv_iteratedFDeriv_apply ((hu.differentiable_iteratedFDeriv (by exact_mod_cast hj)) x)]
    exact congrArg _ (Fin.comp_cons b i (Fin.cons i τ)).symm
  have := hU.eLpNorm_fderiv_apply_sq_le (μ := μ) hUc (b i) hq (a := a) (b := c)
  rwa [show (fun x ↦ fderiv ℝ U x (b i)) = _ from funext h1,
    show (fun x ↦ fderiv ℝ (fun y ↦ iteratedFDeriv ℝ (j + 1) u y
      (fun l ↦ b ((Fin.cons i τ : Fin (j + 1) → ι) l))) x (b i)) = _ from funext h2] at this

section BasisSum

variable {ι : Type*} [Fintype ι]

/-- The sum over all `n`-tuples of directions from the family `b` of the `L^r` norms of the
corresponding partial derivatives `∂_{b σ₁} ⋯ ∂_{b σₙ} u` of order `n`. -/
private noncomputable def basisSum (μ : Measure E) (b : ι → E) (u : E → F) (n : ℕ)
    (r : ℝ≥0∞) : ℝ≥0∞ :=
  ∑ σ : Fin n → ι, eLpNorm (fun x ↦ iteratedFDeriv ℝ n u x (fun l ↦ b (σ l))) r μ

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
/-- Each partial derivative along a tuple of directions from `b` is at most `basisSum`. -/
private theorem eLpNorm_iteratedFDeriv_apply_le_basisSum (b : ι → E) (u : E → F) {n : ℕ}
    (σ : Fin n → ι) (r : ℝ≥0∞) :
    eLpNorm (fun x ↦ iteratedFDeriv ℝ n u x (fun l ↦ b (σ l))) r μ ≤ basisSum μ b u n r :=
  Finset.single_le_sum (f := fun τ : Fin n → ι ↦
    eLpNorm (fun x ↦ iteratedFDeriv ℝ n u x (fun l ↦ b (τ l))) r μ)
    (fun _ _ ↦ by positivity) (Finset.mem_univ σ)

omit [FiniteDimensional ℝ E] in
private theorem basisSum_ne_top {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u)
    (hc : HasCompactSupport u) (b : ι → E) {n : ℕ} (hn : n ≤ k) (r : ℝ≥0∞) :
    basisSum μ b u n r ≠ ∞ :=
  ENNReal.sum_ne_top.2 fun _ _ ↦
    (hu.memLp_iteratedFDeriv_apply_of_hasCompactSupport (by exact_mod_cast hn) hc _).eLpNorm_ne_top

omit [FiniteDimensional ℝ E] [BorelSpace E] [μ.IsAddHaarMeasure] in
private theorem basisSum_zero (b : ι → E) (u : E → F) : basisSum μ b u 0 ∞ = eLpNorm u ∞ μ := by
  simp [basisSum]

omit [μ.IsAddHaarMeasure] in
private theorem basisSum_le (b : ι → E) {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u) (r : ℝ≥0∞) :
    basisSum μ b u k r ≤ (Fintype.card ι ^ k : ℝ≥0∞) * ENNReal.ofReal ((∑ i, ‖b i‖) ^ k) *
      eLpNorm (iteratedFDeriv ℝ k u) r μ := by
  have hterm : ∀ σ : Fin k → ι, eLpNorm (fun x ↦ iteratedFDeriv ℝ k u x (fun l ↦ b (σ l))) r μ ≤
      ENNReal.ofReal ((∑ i, ‖b i‖) ^ k) * eLpNorm (iteratedFDeriv ℝ k u) r μ := fun σ ↦ by
    refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (hu.continuous_iteratedFDeriv_apply le_rfl _).aestronglyMeasurable
      (Eventually.of_forall fun x ↦ ?_) r
    refine ((iteratedFDeriv ℝ k u x).le_opNorm _).trans ?_
    rw [mul_comm]
    gcongr
    calc ∏ l, ‖b (σ l)‖ ≤ ∏ _l : Fin k, ∑ i, ‖b i‖ := by
          gcongr with l
          exact Finset.single_le_sum (f := fun i ↦ ‖b i‖) (fun _ _ ↦ norm_nonneg _)
            (Finset.mem_univ _)
      _ = (∑ i, ‖b i‖) ^ k := by simp
  calc basisSum μ b u k r
      ≤ ∑ _σ : Fin k → ι, ENNReal.ofReal ((∑ i, ‖b i‖) ^ k) * eLpNorm (iteratedFDeriv ℝ k u) r μ :=
        Finset.sum_le_sum fun σ _ ↦ hterm σ
    _ = _ := by simp [Finset.sum_const, mul_assoc]

omit [μ.IsAddHaarMeasure] in
private theorem eLpNorm_iteratedFDeriv_le_basisSum (b : Module.Basis ι ℝ E) {u : E → F} {k : ℕ}
    (hu : ContDiff ℝ k u) {n : ℕ} (hn : n ≤ k) {r : ℝ≥0∞} (hr : 1 ≤ r) :
    eLpNorm (iteratedFDeriv ℝ n u) r μ ≤
      ENNReal.ofReal (‖b.equivFunL.toContinuousLinearMap‖ ^ n) * basisSum μ b u n r := by
  set g : E → ℝ := fun x ↦ ∑ σ : Fin n → ι, ‖iteratedFDeriv ℝ n u x (fun l ↦ b (σ l))‖
  have hcont : ∀ σ : Fin n → ι, Continuous fun x ↦ iteratedFDeriv ℝ n u x (fun l ↦ b (σ l)) :=
    fun σ ↦ hu.continuous_iteratedFDeriv_apply (by exact_mod_cast hn) _
  calc eLpNorm (iteratedFDeriv ℝ n u) r μ
      ≤ ENNReal.ofReal (‖b.equivFunL.toContinuousLinearMap‖ ^ n) * eLpNorm g r μ := by
        refine eLpNorm_le_mul_eLpNorm_of_ae_le_mul
          (hu.continuous_iteratedFDeriv (by exact_mod_cast hn)).aestronglyMeasurable
          (Eventually.of_forall fun x ↦ ?_) r
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ ↦ norm_nonneg _)]
        simpa using (iteratedFDeriv ℝ n u x).opNorm_le_prod_mul_sum_norm_apply_basis fun _ ↦ b
    _ ≤ ENNReal.ofReal (‖b.equivFunL.toContinuousLinearMap‖ ^ n) *
          ∑ σ : Fin n → ι, eLpNorm (fun x ↦ ‖iteratedFDeriv ℝ n u x (fun l ↦ b (σ l))‖) r μ := by
        gcongr
        have : g = ∑ σ : Fin n → ι, fun x ↦ ‖iteratedFDeriv ℝ n u x (fun l ↦ b (σ l))‖ := by
          funext x; simp [g]
        rw [this]
        exact eLpNorm_sum_le hr
    _ = _ := by
        simp only [basisSum]
        congr 1
        exact Finset.sum_congr rfl fun σ _ ↦ eLpNorm_norm _ (hcont σ).aestronglyMeasurable

private theorem toReal_basisSum_sq_le {u : E → F} {k : ℕ} (hu : ContDiff ℝ k u)
    (hc : HasCompactSupport u) (b : ι → E) {j : ℕ} (hj : j + 1 < k) {q : ℝ} (hq : 2 ≤ q)
    {a c : ℝ≥0∞} [ENNReal.HolderTriple a c (ENNReal.ofReal (q / 2))] :
    (basisSum μ b u (j + 1) (ENNReal.ofReal q)).toReal ^ 2 ≤
      (Fintype.card ι : ℝ) ^ (2 * (j + 1)) * (q - 1) * (basisSum μ b u j a).toReal *
        (basisSum μ b u (j + 2) c).toReal := by
  set A := basisSum μ b u j a
  set C := basisSum μ b u (j + 2) c
  set t : (Fin (j + 1) → ι) → ℝ := fun σ ↦
    (eLpNorm (fun x ↦ iteratedFDeriv ℝ (j + 1) u x (fun l ↦ b (σ l))) (ENNReal.ofReal q) μ).toReal
  have hterm : ∀ σ, t σ ^ 2 ≤ (q - 1) * A.toReal * C.toReal := by
    intro σ
    have h := eLpNorm_iteratedFDeriv_cons_sq_le (μ := μ) hu hc b hj (σ 0) (Fin.tail σ) hq
      (a := a) (c := c)
    rw [Fin.cons_self_tail] at h
    have h1 := eLpNorm_iteratedFDeriv_apply_le_basisSum (μ := μ) b u (Fin.tail σ) a
    have h2 := eLpNorm_iteratedFDeriv_apply_le_basisSum (μ := μ) b u
      (Fin.cons (σ 0) σ : Fin (j + 2) → ι) c
    have h3 : _ ≤ ENNReal.ofReal (q - 1) * A * C := h.trans (by gcongr)
    have hA : A ≠ ⊤ := basisSum_ne_top hu hc b (by omega) a
    have hC : C ≠ ⊤ := basisSum_ne_top hu hc b (by omega) c
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA)
      hC) h3
    rwa [ENNReal.toReal_pow, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith)] at this
  have hsum : (basisSum μ b u (j + 1) (ENNReal.ofReal q)).toReal = ∑ σ, t σ :=
    ENNReal.toReal_sum fun σ _ ↦ (hu.memLp_iteratedFDeriv_apply_of_hasCompactSupport
      (by exact_mod_cast hj.le) hc _).eLpNorm_ne_top
  have hcard : (Fintype.card (Fin (j + 1) → ι) : ℝ) = (Fintype.card ι : ℝ) ^ (j + 1) := by
    simp
  rw [hsum]
  calc (∑ σ, t σ) ^ 2 ≤ (Fintype.card (Fin (j + 1) → ι) : ℝ) * ∑ σ, t σ ^ 2 := by
        simpa using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := t)
    _ ≤ (Fintype.card (Fin (j + 1) → ι) : ℝ) *
          (Fintype.card (Fin (j + 1) → ι) * ((q - 1) * A.toReal * C.toReal)) := by
        gcongr
        simpa using Finset.sum_le_card_nsmul Finset.univ _ _ fun σ _ ↦ hterm σ
    _ = _ := by rw [hcard]; ring

end BasisSum

/-- The Lebesgue exponent `(n / (k p))⁻¹` of the `n`-th derivative in the Gagliardo–Nirenberg
inequality between `L^∞` and the `k`-th derivative in `L^p`; it is `∞` for `n = 0` and
`k p / n` otherwise. -/
private noncomputable def gnExponent (k : ℕ) (p : ℝ) (n : ℕ) : ℝ≥0∞ :=
  (ENNReal.ofReal (n / (k * p)))⁻¹

private theorem gnExponent_zero (k : ℕ) (p : ℝ) : gnExponent k p 0 = ∞ := by
  simp [gnExponent]

private theorem gnExponent_of_pos {k n : ℕ} {p : ℝ} (hkp : 0 < k * p) (hn : 0 < n) :
    gnExponent k p n = ENNReal.ofReal (k * p / n) := by
  rw [gnExponent, ← ENNReal.ofReal_inv_of_pos (div_pos (by exact_mod_cast hn) hkp), inv_div]

private theorem holderTriple_gnExponent {k : ℕ} {p : ℝ} (hkp : 0 < k * p) (m : ℕ) :
    ENNReal.HolderTriple (gnExponent k p m) (gnExponent k p (m + 2))
      (ENNReal.ofReal (k * p / (m + 1 : ℕ) / 2)) := by
  constructor
  rw [gnExponent, gnExponent, inv_inv, inv_inv, ← ENNReal.ofReal_add (by positivity)
    (by positivity), ← ENNReal.ofReal_inv_of_pos (by positivity)]
  congr 1
  push_cast
  field_simp
  ring


private theorem one_le_gnExponent {k : ℕ} {p : ℝ} (hp : 1 ≤ p) {n : ℕ} (hnk : n ≤ k) :
    1 ≤ gnExponent k p n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [gnExponent_zero]
  have hk : (0 : ℝ) < k := by exact_mod_cast hn.trans_le hnk
  rw [gnExponent_of_pos (by positivity) hn, ← ENNReal.ofReal_one]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [le_div_iff₀ (by exact_mod_cast hn)]
  have : (n : ℝ) ≤ k := by exact_mod_cast hnk
  nlinarith

/-- The geometric interpolation bound for the sums of the `L^{k p / n}` norms of the partial
derivatives of order `n` along a family of directions. -/
private theorem toReal_basisSum_pow_le {ι : Type*} [Fintype ι] {u : E → F} {k : ℕ}
    (hu : ContDiff ℝ k u) (hc : HasCompactSupport u) (b : ι → E) {p : ℝ} (hp : 2 ≤ p) {j : ℕ}
    (hjk : j ≤ k) :
    (basisSum μ b u j (gnExponent k p j)).toReal ^ k ≤
      ((max 1 (Fintype.card ι : ℝ)) ^ (2 * k) * (k * p)) ^ (j * (k - j) * k) *
        (basisSum μ b u 0 (gnExponent k p 0)).toReal ^ (k - j) *
        (basisSum μ b u k (gnExponent k p k)).toReal ^ j := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · obtain rfl : j = 0 := by omega
    simp
  set N : ℝ := (Fintype.card ι : ℝ)
  set c : ℝ := (max 1 N) ^ (2 * k) * (k * p)
  have hrec : ∀ n, 0 < n → n < k →
      (basisSum μ b u n (gnExponent k p n)).toReal ^ 2 ≤
        c * (basisSum μ b u (n - 1) (gnExponent k p (n - 1))).toReal *
          (basisSum μ b u (n + 1) (gnExponent k p (n + 1))).toReal := by
    intro n hn hnk
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hkp : 0 < (k : ℝ) * p := mul_pos (by exact_mod_cast hk) (by linarith)
    have hmk : ((m + 1 : ℕ) : ℝ) ≤ k := by exact_mod_cast hnk.le
    have hm0 : (0 : ℝ) < (m + 1 : ℕ) := by positivity
    have hq : p ≤ k * p / (m + 1 : ℕ) := by rw [le_div_iff₀ hm0]; nlinarith
    have hq' : k * p / (m + 1 : ℕ) ≤ k * p := div_le_self hkp.le (by exact_mod_cast le_add_self)
    have := holderTriple_gnExponent hkp m
    have h := toReal_basisSum_sq_le (μ := μ) hu hc b (j := m) (by omega) (hp.trans hq)
      (a := gnExponent k p m) (c := gnExponent k p (m + 2))
    rw [← gnExponent_of_pos hkp (Nat.succ_pos m)] at h
    simp only [Nat.add_sub_cancel]
    refine h.trans ?_
    gcongr
    have hN : N ^ (2 * (m + 1)) ≤ (max 1 N) ^ (2 * k) :=
      (pow_le_pow_left₀ (by positivity) (le_max_right _ _) _).trans
        (pow_le_pow_right₀ (le_max_left _ _) (by omega))
    exact mul_le_mul hN (by linarith) (by linarith) (by positivity)
  have hc : 1 ≤ c := by
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (le_max_left _ _)) (by nlinarith)
  refine (pow_le_mul_pow_mul_pow_of_sq_le_mul (zero_le_one.trans hc) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg hrec hjk).trans ?_
  gcongr
  exact Nat.div_le_self _ _



/-- Taking `k`-th roots in a geometric bound `x ^ k ≤ D ^ k A ^ (k - j) B ^ j`. -/
private theorem le_mul_rpow_mul_rpow_of_pow_le {j k : ℕ} (hk : k ≠ 0) (hjk : j ≤ k) {x A B D : ℝ}
    (hx : 0 ≤ x) (hA : 0 ≤ A) (hB : 0 ≤ B) (hD : 0 ≤ D)
    (h : x ^ k ≤ D ^ k * A ^ (k - j) * B ^ j) :
    x ≤ D * A ^ (1 - (j : ℝ) / k) * B ^ ((j : ℝ) / k) := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  refine (pow_le_pow_iff_left₀ hx (by positivity) hk).1 (h.trans_eq ?_)
  rw [mul_pow, mul_pow, ← Real.rpow_mul_natCast hA, ← Real.rpow_mul_natCast hB,
    show (1 - (j : ℝ) / k) * k = ((k - j : ℕ) : ℝ) by rw [Nat.cast_sub hjk]; field_simp,
    show (j : ℝ) / k * k = (j : ℕ) by field_simp, Real.rpow_natCast, Real.rpow_natCast]

/-- Passing from a real bound on `toReal` values back to `ℝ≥0∞`. -/
private theorem le_ofReal_mul_rpow_mul_rpow {X A B : ℝ≥0∞} {C s t : ℝ} (hX : X ≠ ∞)
    (hA : A ≠ ∞) (hB : B ≠ ∞) (hs : 0 ≤ s) (ht : 0 ≤ t)
    (h : X.toReal ≤ C * A.toReal ^ s * B.toReal ^ t) :
    X ≤ ENNReal.ofReal C * A ^ s * B ^ t := by
  rw [← ENNReal.ofReal_toReal hX, ← ENNReal.ofReal_toReal hA, ← ENNReal.ofReal_toReal hB,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hs,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg ht, ← ENNReal.ofReal_mul'
      (by positivity), ← ENNReal.ofReal_mul' (by positivity)]
  exact ENNReal.ofReal_le_ofReal h

/-- The exponent `q` with `k / q = j / p` is the exponent `gnExponent k p j`. -/
private theorem eq_gnExponent {p q : ℝ≥0∞} (hp : p ≠ ∞) (hp0 : p ≠ 0) {j k : ℕ} (hk : k ≠ 0)
    (hq : (k : ℝ≥0∞) * q⁻¹ = j * p⁻¹) : q = gnExponent k p.toReal j := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [← inv_inv q, gnExponent, inv_inj]
  refine (ENNReal.mul_right_inj (a := (k : ℝ≥0∞)) (by exact_mod_cast hk) (by simp)).1 ?_
  have hpinv : p⁻¹ = ENNReal.ofReal p.toReal⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos hpr, ENNReal.ofReal_toReal hp]
  rw [hq, hpinv, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast k,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  field_simp

/-- The Gagliardo–Nirenberg inequality for the `toReal` values of the norms, with the exponent
`gnExponent k p j = k p / j` of `D^j u`. -/
private theorem exists_toReal_eLpNorm_iteratedFDeriv_le {p : ℝ} (hp : 2 ≤ p) {j k : ℕ}
    (hk : k ≠ 0) (hjk : j ≤ k) :
    ∃ C : ℝ, ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      (eLpNorm (iteratedFDeriv ℝ j u) (gnExponent k p j) μ).toReal ≤
        C * (eLpNorm u ∞ μ).toReal ^ (1 - (j : ℝ) / k) *
          (eLpNorm (iteratedFDeriv ℝ k u) (gnExponent k p k) μ).toReal ^ ((j : ℝ) / k) := by
  set b := Module.finBasis ℝ E
  set N : ℝ := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ)
  set β := ‖b.equivFunL.toContinuousLinearMap‖
  set β' := ∑ i, ‖b i‖
  set c : ℝ := (max 1 N) ^ (2 * k) * (k * p)
  refine ⟨β ^ j * c ^ (j * (k - j)) * (N * β') ^ j, fun u hu hc ↦ ?_⟩
  set a : ℕ → ℝ := fun n ↦ (basisSum μ b u n (gnExponent k p n)).toReal
  have hlog := toReal_basisSum_pow_le (μ := μ) hu hc b hp hjk
  have hXk : eLpNorm (iteratedFDeriv ℝ k u) (gnExponent k p k) μ ≠ ∞ :=
    (hu.memLp_iteratedFDeriv_of_hasCompactSupport le_rfl hc).eLpNorm_ne_top
  have ha0 : a 0 = (eLpNorm u ∞ μ).toReal := by simp [a, gnExponent_zero, basisSum_zero]
  have hak : a k ≤
      N ^ k * β' ^ k * (eLpNorm (iteratedFDeriv ℝ k u) (gnExponent k p k) μ).toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp)
      ENNReal.ofReal_ne_top) hXk) (basisSum_le (μ := μ) b hu (gnExponent k p k))
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
    simpa [a, N] using this
  have hL : (eLpNorm (iteratedFDeriv ℝ j u) (gnExponent k p j) μ).toReal ≤ β ^ j * a j := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (basisSum_ne_top hu hc b hjk _))
      (eLpNorm_iteratedFDeriv_le_basisSum (μ := μ) b hu hjk
        (one_le_gnExponent (k := k) (p := p) (by linarith) hjk))
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  refine hL.trans (le_mul_rpow_mul_rpow_of_pow_le hk hjk (by positivity) ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (by positivity) ?_)
  calc (β ^ j * a j) ^ k = β ^ (j * k) * a j ^ k := by ring
    _ ≤ β ^ (j * k) * (c ^ (j * (k - j) * k) * a 0 ^ (k - j) * a k ^ j) := by gcongr
    _ ≤ β ^ (j * k) * (c ^ (j * (k - j) * k) * (eLpNorm u ∞ μ).toReal ^ (k - j) *
          (N ^ k * β' ^ k * (eLpNorm (iteratedFDeriv ℝ k u) (gnExponent k p k) μ).toReal) ^ j) := by
        rw [ha0]; gcongr
    _ = _ := by ring

/-- **The Gagliardo–Nirenberg interpolation inequality** with an `L^∞` endpoint. Let `2 ≤ p < ∞`,
`0 ≤ j ≤ k` with `k ≠ 0`, and let `q` be given by `1 / q = (j / k) (1 / p)`. There is a constant
`C` such that every `C^k` function `u` with compact support satisfies

`‖D^j u‖_{L^q} ≤ C ‖u‖_{L^∞} ^ (1 - j / k) ‖D^k u‖_{L^p} ^ (j / k)`.

For `j = 0` this is `‖u‖_∞ ≤ C ‖u‖_∞` (with `q = ∞`), for `j = k` it is `‖D^k u‖_p ≤ C ‖D^k u‖_p`.
-/
theorem exists_eLpNorm_iteratedFDeriv_le {p q : ℝ≥0∞} (hp : 2 ≤ p) (hp' : p ≠ ∞) {j k : ℕ}
    (hk : k ≠ 0) (hjk : j ≤ k) (hq : (k : ℝ≥0∞) * q⁻¹ = j * p⁻¹) :
    ∃ C : ℝ≥0, ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ j u) q μ ≤
        C * eLpNorm u ∞ μ ^ (1 - (j : ℝ) / k) *
          eLpNorm (iteratedFDeriv ℝ k u) p μ ^ ((j : ℝ) / k) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le (by norm_num) hp).ne'
  have hpr : 2 ≤ p.toReal := by simpa using ENNReal.toReal_mono hp' hp
  have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  have hgk : gnExponent k p.toReal k = p := by
    rw [gnExponent_of_pos (by positivity) (Nat.pos_of_ne_zero hk), mul_div_cancel_left₀ _
      hkpos.ne', ENNReal.ofReal_toReal hp']
  obtain ⟨C, hGN⟩ := exists_toReal_eLpNorm_iteratedFDeriv_le (μ := μ) (F := F) hpr hk hjk
  refine ⟨C.toNNReal, fun u hu hc ↦ ?_⟩
  rw [eq_gnExponent hp' hp0 hk hq, ENNReal.ofNNReal_toNNReal]
  conv_rhs => rw [← hgk]
  refine le_ofReal_mul_rpow_mul_rpow ?_ ?_ ?_ (by
    rw [sub_nonneg, div_le_one hkpos]; exact_mod_cast hjk) (by positivity) (hGN u hu hc)
  · exact (hu.memLp_iteratedFDeriv_of_hasCompactSupport (by exact_mod_cast hjk) hc).eLpNorm_ne_top
  · exact (hu.continuous.memLp_of_hasCompactSupport hc).eLpNorm_ne_top
  · exact (hu.memLp_iteratedFDeriv_of_hasCompactSupport le_rfl hc).eLpNorm_ne_top

section Bilinear

variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [NormedAddCommGroup H]
  [NormedSpace ℝ H]

/-- The product of the two Gagliardo–Nirenberg bounds for `D^i u` and `D^(k - i) v` is at most the
sum of the two endpoint products. -/
private theorem mul_rpow_mul_mul_rpow_le {k i : ℕ} (hk : k ≠ 0) (hi : i ≤ k)
    {a b c d : ℝ≥0∞} :
    a ^ (1 - (i : ℝ) / k) * b ^ ((i : ℝ) / k) *
        (c ^ (1 - ((k - i : ℕ) : ℝ) / k) * d ^ (((k - i : ℕ) : ℝ) / k)) ≤
      a * d + b * c := by
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hθ0 : (0 : ℝ) ≤ (i : ℝ) / k := by positivity
  have hθ1 : (i : ℝ) / k ≤ 1 := by
    rw [div_le_one (by positivity)]; exact_mod_cast hi
  have h1 : 1 - ((k - i : ℕ) : ℝ) / k = (i : ℝ) / k := by
    rw [Nat.cast_sub hi]; field_simp; ring
  have h2 : ((k - i : ℕ) : ℝ) / k = 1 - (i : ℝ) / k := by linarith
  rw [h1, h2]
  calc a ^ (1 - (i : ℝ) / k) * b ^ ((i : ℝ) / k) * (c ^ ((i : ℝ) / k) * d ^ (1 - (i : ℝ) / k))
      = (a * d) ^ (1 - (i : ℝ) / k) * (b * c) ^ ((i : ℝ) / k) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith), ENNReal.mul_rpow_of_nonneg _ _ hθ0]
        ring
    _ ≤ a * d + b * c := (ENNReal.geom_mean_le_arith_mean2_weighted_ofReal hθ0 hθ1 _ _).trans
        (add_le_add (mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2 (by linarith)))
          (mul_le_of_le_one_left' (ENNReal.ofReal_le_one.2 hθ1)))

/-- **The Moser product estimate.** For `2 ≤ p < ∞`, every order `k` and every continuous bilinear
map `B`, the `k`-th derivative of `x ↦ B (u x) (v x)` is controlled in `L^p` by the endpoint
products of `u` and `v`: there is a constant `C`, independent of `B`, `u` and `v`, with

`‖D^k (B (u, v))‖_{L^p} ≤ C ‖B‖ (‖u‖_{L^∞} ‖D^k v‖_{L^p} + ‖D^k u‖_{L^p} ‖v‖_{L^∞})`

for all `C^k` functions `u` and `v` with compact support. The intermediate terms of the Leibniz
expansion are estimated by Hölder's inequality and the Gagliardo–Nirenberg inequality
`TauCeti.exists_eLpNorm_iteratedFDeriv_le`. -/
theorem exists_eLpNorm_iteratedFDeriv_bilinear_le {p : ℝ≥0∞} (hp : 2 ≤ p) (hp' : p ≠ ∞) (k : ℕ) :
    ∃ C : ℝ≥0, ∀ (B : F →L[ℝ] G →L[ℝ] H) (u : E → F) (v : E → G), ContDiff ℝ k u →
      HasCompactSupport u → ContDiff ℝ k v → HasCompactSupport v →
      eLpNorm (iteratedFDeriv ℝ k (fun x ↦ B (u x) (v x))) p μ ≤
        C * ‖B‖ₑ * (eLpNorm u ∞ μ * eLpNorm (iteratedFDeriv ℝ k v) p μ +
          eLpNorm (iteratedFDeriv ℝ k u) p μ * eLpNorm v ∞ μ) := by
  have hp1 : 1 ≤ p := le_trans (by norm_num) hp
  rcases eq_or_ne k 0 with rfl | hk
  · -- `‖B (u, v)‖_p ≤ ‖B‖ ‖u‖_∞ ‖v‖_p`.
    refine ⟨1, fun B u v hu _ hv _ ↦ ?_⟩
    rw [eLpNorm_iteratedFDeriv_zero, eLpNorm_iteratedFDeriv_zero, eLpNorm_iteratedFDeriv_zero,
      ENNReal.coe_one, one_mul]
    refine (eLpNorm_le_eNorm_mul_eLpNorm_mul_eLpNorm (p := ∞) (q := p) B
      hu.continuous.aestronglyMeasurable hv.continuous.aestronglyMeasurable).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_right le_self_add _
  set q : ℕ → ℝ≥0∞ := fun i ↦ ((i : ℝ≥0∞) * p⁻¹ / k)⁻¹
  have hGNu : ∀ i ≤ k, ∃ C : ℝ≥0, ∀ u : E → F, ContDiff ℝ k u → HasCompactSupport u →
      eLpNorm (iteratedFDeriv ℝ i u) (q i) μ ≤ C * eLpNorm u ∞ μ ^ (1 - (i : ℝ) / k) *
        eLpNorm (iteratedFDeriv ℝ k u) p μ ^ ((i : ℝ) / k) := fun i hi ↦
    exists_eLpNorm_iteratedFDeriv_le hp hp' hk hi (ENNReal.natCast_mul_inv_inv_div hk i)
  have hGNv : ∀ i ≤ k, ∃ C : ℝ≥0, ∀ v : E → G, ContDiff ℝ k v → HasCompactSupport v →
      eLpNorm (iteratedFDeriv ℝ (k - i) v) (q (k - i)) μ ≤
        C * eLpNorm v ∞ μ ^ (1 - ((k - i : ℕ) : ℝ) / k) *
          eLpNorm (iteratedFDeriv ℝ k v) p μ ^ (((k - i : ℕ) : ℝ) / k) := fun i _ ↦
    exists_eLpNorm_iteratedFDeriv_le hp hp' hk (Nat.sub_le k i)
      (ENNReal.natCast_mul_inv_inv_div hk _)
  choose! CF hCF using hGNu
  choose! CG hCG using hGNv
  refine ⟨∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ≥0) * CF i * CG i,
    fun B u v hu hc hv hc' ↦ ?_⟩
  refine (B.eLpNorm_iteratedFDeriv_le_of_bilinear (μ := μ) hu hv le_rfl hp1 (q := q)
    (r := fun i ↦ q (k - i)) (fun i hi ↦ ENNReal.HolderTriple.natCast_mul_inv_div hk hi)).trans ?_
  rw [ENNReal.ofNNReal_finsetSum, Finset.sum_mul, Finset.sum_mul]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  have hik : i ≤ k := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  calc ‖B‖ₑ * (k.choose i : ℝ≥0∞) * eLpNorm (iteratedFDeriv ℝ i u) (q i) μ *
        eLpNorm (iteratedFDeriv ℝ (k - i) v) (q (k - i)) μ
      ≤ ‖B‖ₑ * (k.choose i : ℝ≥0∞) *
          (CF i * eLpNorm u ∞ μ ^ (1 - (i : ℝ) / k) *
            eLpNorm (iteratedFDeriv ℝ k u) p μ ^ ((i : ℝ) / k)) *
          (CG i * eLpNorm v ∞ μ ^ (1 - ((k - i : ℕ) : ℝ) / k) *
            eLpNorm (iteratedFDeriv ℝ k v) p μ ^ (((k - i : ℕ) : ℝ) / k)) := by
        gcongr
        exacts [hCF i hik u hu hc, hCG i hik v hv hc']
    _ = ‖B‖ₑ * (k.choose i : ℝ≥0∞) * CF i * CG i *
          (eLpNorm u ∞ μ ^ (1 - (i : ℝ) / k) *
            eLpNorm (iteratedFDeriv ℝ k u) p μ ^ ((i : ℝ) / k) *
          (eLpNorm v ∞ μ ^ (1 - ((k - i : ℕ) : ℝ) / k) *
            eLpNorm (iteratedFDeriv ℝ k v) p μ ^ (((k - i : ℕ) : ℝ) / k))) := by ring
    _ ≤ ‖B‖ₑ * (k.choose i : ℝ≥0∞) * CF i * CG i *
          (eLpNorm u ∞ μ * eLpNorm (iteratedFDeriv ℝ k v) p μ +
            eLpNorm (iteratedFDeriv ℝ k u) p μ * eLpNorm v ∞ μ) := by
        gcongr
        exact mul_rpow_mul_mul_rpow_le hk hik
    _ = _ := by push_cast; ring

end Bilinear

end TauCeti
