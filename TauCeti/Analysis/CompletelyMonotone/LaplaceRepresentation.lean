/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import TauCeti.Analysis.CompletelyMonotone.BernsteinMeasures

/-!
# Laplace representations for completely monotone functions

This file contains the Laplace-transform side of the finite-measure
Hausdorff--Bernstein--Widder theorem on `ℝ≥0`: helper lemmas for finite-measure Laplace
transforms and the predicate that a finite measure represents a function by its Laplace transform.

## References

The finite-measure representation is the Hausdorff--Bernstein--Widder theorem, after
S. Bernstein (1928) and D. V. Widder, *The Laplace Transform*, Chapter IV. The extraction
argument follows the Bernstein-kernel proof described by D. Chafaï (2013). The Lean proofs of
`chafai_identity` and the Bernstein-to-Laplace kernel convergence were adapted from Tau Ceti's
Hille--Yosida formalization in `HilleYosida/BernsteinChafai.lean` and completed here; in
particular, the `chafai_identity` that was `sorry` there is now proved.
-/

public section

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction ContDiff ENNReal NNReal Topology

namespace TauCeti

/-! ## Laplace transforms of finite measures on `ℝ≥0` -/

/-- The Laplace transform of a measure on `ℝ≥0`, evaluated at a real parameter `t`.

The theorem statements in this file use the transform only for `0 ≤ t`; for negative `t`, the
Bochner integral is still a total Lean term, but may be the default value when the integrand is not
integrable. -/
noncomputable abbrev laplaceTransform (μ : Measure ℝ≥0) (t : ℝ) : ℝ :=
  ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ

/-- The defining formula for `laplaceTransform`. -/
@[simp]
lemma laplaceTransform_apply (μ : Measure ℝ≥0) (t : ℝ) :
    laplaceTransform μ t = ∫ x, Real.exp (-(t * (x : ℝ))) ∂μ := rfl

/-- The Laplace kernel is measurable as a function of the measure variable. -/
lemma measurable_laplaceKernel (t : ℝ) :
    Measurable fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- The Laplace kernel is continuous as a function of the measure variable. -/
lemma continuous_laplaceKernel (t : ℝ) :
    Continuous fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ))) := by
  fun_prop

/-- For `0 ≤ t`, the Laplace kernel is integrable against every finite measure on `ℝ≥0`. -/
lemma integrable_laplaceKernel_of_nonneg (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => Real.exp (-(t * (x : ℝ)))) μ := by
  convert (laplaceKernelBoundedContinuous ht).integrable μ using 1
  ext x
  simp

/-- The value of the Laplace transform at zero is the total finite mass. -/
@[simp]
lemma laplaceTransform_zero (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    laplaceTransform μ 0 = μ.real univ := by
  simp [laplaceTransform]

/-- The Laplace transform of a positive measure is nonnegative. -/
lemma laplaceTransform_nonneg (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (t : ℝ) :
    0 ≤ laplaceTransform μ t := by
  exact integral_nonneg fun x => Real.exp_nonneg _

/-! ## Easy direction: finite measures give completely monotone Laplace transforms -/

/-- The Laplace transform of a finite measure on `ℝ≥0` is continuous on `[0, ∞)`.

This is dominated convergence in the parameter `t`, using the constant function `1` as an
integrable dominating function on the half-line. -/
theorem laplaceTransform_continuousOn_halfLine (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ContinuousOn (laplaceTransform μ) (Ici 0) := by
  simpa [laplaceTransform] using
    continuousOn_of_dominated (μ := μ)
      (F := fun (t : ℝ) (x : ℝ≥0) => Real.exp (-(t * (x : ℝ))))
      (bound := fun _ : ℝ≥0 => (1 : ℝ)) (s := Ici (0 : ℝ))
      (by
        intro t _ht
        exact (continuous_laplaceKernel t).aestronglyMeasurable)
      (by
        intro t ht
        refine Filter.Eventually.of_forall fun x => ?_
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        rw [Real.exp_le_one_iff]
        exact neg_nonpos.mpr (mul_nonneg ht x.2))
      (integrable_const (1 : ℝ))
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        exact (by fun_prop :
          Continuous fun t : ℝ => Real.exp (-(t * (x : ℝ)))).continuousOn)

/-- The `n`-th signed moment kernel integral attached to a Laplace transform.

For `0 < t`, this is the `n`-th ordinary derivative of `laplaceTransform μ` at `t`. -/
private noncomputable def laplaceMomentTransform (μ : Measure ℝ≥0) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ≥0, (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ))) ∂μ

/-- A polynomial times a decaying exponential is bounded on the closed half-line. -/
private lemma exists_bound_pow_mul_exp_neg (n : ℕ) {b : ℝ} (hb : 0 < b) :
    ∃ C : ℝ, ∀ x : ℝ, 0 ≤ x → ‖x ^ n * Real.exp (-(b * x))‖ ≤ C := by
  have hsmall : (fun y : ℝ => y ^ n) =O[atTop] (fun y : ℝ => Real.exp (b * y)) :=
    (isLittleO_pow_exp_pos_mul_atTop n hb).isBigO
  rcases hsmall.bound with ⟨Ctail, hCtail⟩
  have htail : ∀ᶠ y in atTop, ‖y ^ n * Real.exp (-(b * y))‖ ≤ Ctail := by
    filter_upwards [hCtail] with y hy
    have h_exp_ne : Real.exp (b * y) ≠ 0 := Real.exp_ne_zero _
    have hy' : ‖y ^ n‖ / ‖Real.exp (b * y)‖ ≤ Ctail := by
      have hnorm_pos : 0 < ‖Real.exp (b * y)‖ := norm_pos_iff.mpr h_exp_ne
      exact (div_le_iff₀ hnorm_pos).mpr (by simpa [mul_comm] using hy)
    calc
      ‖y ^ n * Real.exp (-(b * y))‖ = ‖y ^ n‖ / ‖Real.exp (b * y)‖ := by
        rw [norm_mul, Real.exp_neg, norm_inv]
        rfl
      _ ≤ Ctail := hy'
  rcases eventually_atTop.1 htail with ⟨R, hR⟩
  set A : ℝ := max R 0 with hA
  obtain ⟨Ccomp, hCcomp⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) A)).exists_bound_of_continuousOn
      ((by fun_prop : Continuous fun x : ℝ => x ^ n * Real.exp (-(b * x))).continuousOn)
  refine ⟨max Ccomp Ctail, fun x hx => ?_⟩
  by_cases hxA : x ≤ A
  · exact (hCcomp x ⟨hx, hxA⟩).trans (le_max_left Ccomp Ctail)
  · have hRx : R ≤ x := by
      have hRA : R ≤ A := by simp [A]
      exact hRA.trans (le_of_not_ge hxA)
    exact (hR x hRx).trans (le_max_right Ccomp Ctail)

/-- Signed moment kernels with exponential damping are integrable against finite measures on
`ℝ≥0`. -/
private lemma integrable_laplaceMomentTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ := by
  obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg n ht
  refine Integrable.of_bound (C := C) (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  simpa [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg x.2] using hC (x : ℝ) x.2

/-- Moment integrability controls the signed Laplace moment kernel on the closed half-line. -/
private lemma integrable_laplaceMomentTransform_of_nonneg (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) (n : ℕ) {t : ℝ}
    (ht : 0 ≤ t) :
    Integrable (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ := by
  refine (hmom n).mono' (by fun_prop) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp_le : Real.exp (-(t * (x : ℝ))) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg ht hx)
  calc
    ‖(-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))‖
        = (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
          rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg hx,
            Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    _ ≤ (x : ℝ) ^ n := by
          simpa [mul_one] using mul_le_mul_of_nonneg_left hexp_le hpow

/-- Differentiation under the integral for the signed Laplace moment kernels on `(0, ∞)`. -/
private lemma hasDerivAt_laplaceMomentTransform (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (n : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) t) t := by
  let s : Set ℝ := Metric.ball t (t / 2)
  have hs : s ∈ 𝓝 t := Metric.ball_mem_nhds t (half_pos ht)
  obtain ⟨C, hC⟩ := exists_bound_pow_mul_exp_neg (n + 1) (half_pos ht)
  have hF_int :
      Integrable (fun x : ℝ≥0 =>
        (-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) μ :=
    integrable_laplaceMomentTransform μ n ht
  have h :=
    hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := t) (s := s)
      (F := fun (y : ℝ) (x : ℝ≥0) =>
        (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))))
      (F' := fun (y : ℝ) (x : ℝ≥0) =>
        (-(x : ℝ)) ^ (n + 1) * Real.exp (-(y * (x : ℝ))))
      (bound := fun _ : ℝ≥0 => C)
      hs
      (by
        refine Filter.Eventually.of_forall fun y => ?_
        exact (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ≥0 => (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ)))) μ))
      hF_int
      (by
        exact (by fun_prop : AEStronglyMeasurable
          (fun x : ℝ≥0 => (-(x : ℝ)) ^ (n + 1) *
            Real.exp (-(t * (x : ℝ)))) μ))
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        intro y hy
        have hypos : t / 2 ≤ y := by
          have hdist : dist y t < t / 2 := hy
          rw [Real.dist_eq] at hdist
          have hleft := (abs_lt.mp hdist).1
          linarith
        have hnonneg : 0 ≤ (x : ℝ) := x.2
        have hle_exp :
            Real.exp (-(y * (x : ℝ))) ≤ Real.exp (-((t / 2) * (x : ℝ))) := by
          exact Real.exp_le_exp.mpr
            (neg_le_neg (mul_le_mul_of_nonneg_right hypos hnonneg))
        have hpow_nonneg : 0 ≤ (x : ℝ) ^ (n + 1) := pow_nonneg hnonneg _
        calc
          ‖(-(x : ℝ)) ^ (n + 1) * Real.exp (-(y * (x : ℝ)))‖
              = (x : ℝ) ^ (n + 1) * Real.exp (-(y * (x : ℝ))) := by
                rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_neg, abs_of_nonneg hnonneg,
                  Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ (x : ℝ) ^ (n + 1) * Real.exp (-((t / 2) * (x : ℝ))) := by
                exact mul_le_mul_of_nonneg_left hle_exp hpow_nonneg
          _ = ‖(x : ℝ) ^ (n + 1) * Real.exp (-((t / 2) * (x : ℝ)))‖ := by
                rw [norm_mul, norm_pow, Real.norm_eq_abs, abs_of_nonneg hnonneg,
                  Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
          _ ≤ C := hC (x : ℝ) x.2)
      (integrable_const C)
      (by
        refine Filter.Eventually.of_forall fun x => ?_
        intro y _hy
        have hlin : HasDerivAt (fun y : ℝ => -(y * (x : ℝ))) (-(x : ℝ)) y := by
          have hmul : HasDerivAt (fun y : ℝ => y * (x : ℝ)) (x : ℝ) y :=
            hasDerivAt_mul_const (x : ℝ)
          exact hmul.neg
        have hder := hlin.exp.const_mul ((-(x : ℝ)) ^ n)
        simpa [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hder)
  -- Rewrite the private moment-transform definition to the differentiated integral just proved.
  rw [show laplaceMomentTransform μ n =
      (fun y : ℝ => ∫ x : ℝ≥0, (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))) ∂μ) by
        rfl]
  rw [show laplaceMomentTransform μ (n + 1) t =
      ∫ x : ℝ≥0, (-(x : ℝ)) ^ (n + 1) * Real.exp (-(t * (x : ℝ))) ∂μ by
        rfl]
  exact h.2

private lemma abs_exp_neg_sub_one_le {a : ℝ} (ha : 0 ≤ a) :
    |Real.exp (-a) - 1| ≤ a := by
  have hexp_le : Real.exp (-a) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr ha
  have hlinear := Real.add_one_le_exp (-a)
  rw [abs_of_nonpos (sub_nonpos.mpr hexp_le)]
  linarith

private lemma norm_laplaceMomentKernel_slope_zero_le (n : ℕ) {y : ℝ} (hy : 0 ≤ y)
    (x : ℝ≥0) :
    ‖slope (fun z : ℝ => (-(x : ℝ)) ^ n * Real.exp (-(z * (x : ℝ)))) 0 y‖ ≤
      (x : ℝ) ^ (n + 1) := by
  by_cases hy_zero : y = 0
  · subst y
    simp
  have hy_pos : 0 < y := lt_of_le_of_ne' hy hy_zero
  have hx : 0 ≤ (x : ℝ) := x.2
  have harg_nonneg : 0 ≤ y * (x : ℝ) := mul_nonneg hy hx
  have hpow_abs : |(-(x : ℝ)) ^ n| = (x : ℝ) ^ n := by
    rw [abs_pow, abs_neg, abs_of_nonneg hx]
  have hquot :
      |(Real.exp (-(y * (x : ℝ))) - 1) / y| ≤ (x : ℝ) := by
    rw [abs_div, abs_of_pos hy_pos]
    exact (div_le_iff₀ hy_pos).mpr
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using
        abs_exp_neg_sub_one_le harg_nonneg)
  have hpow_nonneg : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  calc
    ‖slope (fun z : ℝ => (-(x : ℝ)) ^ n * Real.exp (-(z * (x : ℝ)))) 0 y‖
        = |(-(x : ℝ)) ^ n| * |(Real.exp (-(y * (x : ℝ))) - 1) / y| := by
          rw [Real.norm_eq_abs, slope_def_field]
          simp only [sub_zero, zero_mul, neg_zero, Real.exp_zero, mul_one]
          rw [show (((-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ))) -
                (-(x : ℝ)) ^ n) / y) =
              (-(x : ℝ)) ^ n * ((Real.exp (-(y * (x : ℝ))) - 1) / y) by ring,
            abs_mul]
    _ ≤ (x : ℝ) ^ n * (x : ℝ) := by
          simpa [hpow_abs] using mul_le_mul_of_nonneg_left hquot hpow_nonneg
    _ = (x : ℝ) ^ (n + 1) := by rw [pow_succ]

private lemma hasDerivWithinAt_laplaceMomentTransform_zero (μ : Measure ℝ≥0)
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) (n : ℕ) :
    HasDerivWithinAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) 0)
      (Ici 0) 0 := by
  let l : Filter ℝ := 𝓝[Ici (0 : ℝ) \ {0}] (0 : ℝ)
  let K : ℝ → ℝ≥0 → ℝ := fun y x =>
    (-(x : ℝ)) ^ n * Real.exp (-(y * (x : ℝ)))
  have hlim :
      Tendsto (fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ) l
        (𝓝 (∫ x : ℝ≥0, (-(x : ℝ)) ^ (n + 1) ∂μ)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (bound := fun x : ℝ≥0 => (x : ℝ) ^ (n + 1))
      ?_ ?_ (hmom (n + 1)) ?_
    · exact Filter.Eventually.of_forall fun y => by
        simpa [slope_def_field] using
          (by fun_prop : AEStronglyMeasurable
            (fun x : ℝ≥0 => (K y x - K 0 x) / (y - 0)) μ)
    · filter_upwards [eventually_mem_nhdsWithin] with y hy
      refine Filter.Eventually.of_forall fun x => ?_
      exact norm_laplaceMomentKernel_slope_zero_le n hy.1 x
    · refine Filter.Eventually.of_forall fun x => ?_
      have hderiv :
          HasDerivWithinAt (fun y : ℝ => K y x) ((-(x : ℝ)) ^ (n + 1)) (Ici 0) 0 := by
        have hlin : HasDerivAt (fun y : ℝ => -(y * (x : ℝ))) (-(x : ℝ)) 0 := by
          exact (hasDerivAt_mul_const (x : ℝ)).neg
        have hder := hlin.exp.const_mul ((-(x : ℝ)) ^ n)
        simpa [K, pow_succ, mul_assoc, mul_comm, mul_left_comm] using hder.hasDerivWithinAt
      exact (hasDerivWithinAt_iff_tendsto_slope.mp hderiv)
  have hslope :
      (fun y : ℝ => slope (laplaceMomentTransform μ n) 0 y)
        =ᶠ[l] fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ := by
    filter_upwards [eventually_mem_nhdsWithin] with y hy
    have hy_nonneg : 0 ≤ y := hy.1
    have hKy : Integrable (fun x : ℝ≥0 => K y x) μ :=
      integrable_laplaceMomentTransform_of_nonneg μ hmom n hy_nonneg
    have hK0 : Integrable (fun x : ℝ≥0 => K 0 x) μ :=
      integrable_laplaceMomentTransform_of_nonneg μ hmom n le_rfl
    calc
      slope (laplaceMomentTransform μ n) 0 y
          = (y - 0)⁻¹ *
              ((∫ x : ℝ≥0, K y x ∂μ) - ∫ x : ℝ≥0, K 0 x ∂μ) := by
                simp [slope_def_field, laplaceMomentTransform, K, div_eq_inv_mul]
      _ = (y - 0)⁻¹ * (∫ x : ℝ≥0, K y x - K 0 x ∂μ) := by
            rw [integral_sub hKy hK0]
      _ = ∫ x : ℝ≥0, (y - 0)⁻¹ * (K y x - K 0 x) ∂μ := by
            rw [integral_const_mul]
      _ = ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ := by
            congr with x
  rw [hasDerivWithinAt_iff_tendsto_slope]
  have hlim' :
      Tendsto (fun y : ℝ => ∫ x : ℝ≥0, slope (fun z : ℝ => K z x) 0 y ∂μ) l
        (𝓝 (laplaceMomentTransform μ (n + 1) 0)) := by
    simpa [laplaceMomentTransform] using hlim
  simpa [l] using Tendsto.congr' hslope.symm hlim'

/-- Differentiation under the integral for signed Laplace moment kernels within `[0, ∞)`.

At positive parameters this is the existing open-neighbourhood differentiation theorem; at `0`
it is the one-sided dominated-convergence argument using the next moment as a bound. -/
private lemma hasDerivWithinAt_laplaceMomentTransform_Ici (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (laplaceMomentTransform μ n) (laplaceMomentTransform μ (n + 1) t)
      (Ici 0) t := by
  by_cases ht_pos : 0 < t
  · exact (hasDerivAt_laplaceMomentTransform μ n ht_pos).hasDerivWithinAt
  have ht_zero : t = 0 := le_antisymm (le_of_not_gt ht_pos) ht
  subst t
  exact hasDerivWithinAt_laplaceMomentTransform_zero μ hmom n

/-- The derivative within `[0, ∞)` of the `n`-th signed Laplace moment kernel is the next
signed moment kernel. -/
private lemma derivWithin_laplaceMomentTransform_eq (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    derivWithin (laplaceMomentTransform μ n) (Ici 0) t =
      laplaceMomentTransform μ (n + 1) t := by
  exact (hasDerivWithinAt_laplaceMomentTransform_Ici μ hmom n ht).derivWithin
    ((uniqueDiffOn_Ici (0 : ℝ)) t (mem_Ici.mpr ht))

/-- On the closed half-line, the iterated within-derivatives of a finite-measure Laplace transform
with all moments finite are the signed moment kernel integrals. -/
private lemma iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ)
    (n : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin n (laplaceTransform μ) (Ici 0) t =
      laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      calc
        derivWithin (iteratedDerivWithin n (laplaceTransform μ) (Ici 0)) (Ici 0) t
            = derivWithin (laplaceMomentTransform μ n) (Ici 0) t := by
              exact derivWithin_congr (fun y hy => ih hy) (ih ht)
        _ = laplaceMomentTransform μ (n + 1) t :=
              derivWithin_laplaceMomentTransform_eq μ hmom n ht

/-- If all moments of the representing measure are finite, its Laplace transform is smooth on the
closed half-line in the existing `iteratedDerivWithin` sense. -/
lemma laplaceTransform_contDiffOn_Ici_of_moments
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceTransform μ) (Ici 0) := by
  refine contDiffOn_of_differentiableOn_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (s := Ici (0 : ℝ)) (f := laplaceTransform μ) ?_
  intro m _hm
  have hdiff_moment : DifferentiableOn ℝ (laplaceMomentTransform μ m) (Ici 0) := by
    intro t ht
    exact (hasDerivWithinAt_laplaceMomentTransform_Ici μ hmom m ht).differentiableWithinAt
  exact hdiff_moment.congr fun t ht =>
    iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici μ hmom m ht

/-- On the open half-line, the iterated within-derivatives of a finite-measure Laplace transform
are the signed moment kernel integrals. -/
private lemma iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDerivWithin n (laplaceTransform μ) (Ioi 0) t =
      laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDerivWithin_succ]
      calc
        derivWithin (iteratedDerivWithin n (laplaceTransform μ) (Ioi 0)) (Ioi 0) t
            = derivWithin (laplaceMomentTransform μ n) (Ioi 0) t := by
              exact derivWithin_congr (fun y hy => ih hy) (ih ht)
        _ = deriv (laplaceMomentTransform μ n) t := by
              rw [derivWithin_of_mem_nhds (isOpen_Ioi.mem_nhds ht)]
        _ = laplaceMomentTransform μ (n + 1) t :=
              (hasDerivAt_laplaceMomentTransform μ n ht).deriv

/-- On the open half-line, the ordinary iterated derivatives of a finite-measure Laplace transform
are the signed moment kernel integrals. -/
private lemma iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] (n : ℕ) {t : ℝ} (ht : 0 < t) :
    iteratedDeriv n (laplaceTransform μ) t = laplaceMomentTransform μ n t := by
  induction n generalizing t with
  | zero => simp [laplaceMomentTransform, laplaceTransform]
  | succ n ih =>
      rw [iteratedDeriv_succ]
      have hev : (fun y : ℝ => iteratedDeriv n (laplaceTransform μ) y) =ᶠ[𝓝 t]
          laplaceMomentTransform μ n :=
        eventually_of_mem (isOpen_Ioi.mem_nhds ht) fun y hy => ih hy
      rw [Filter.EventuallyEq.deriv_eq hev]
      exact (hasDerivAt_laplaceMomentTransform μ n ht).deriv

/-- A finite-measure Laplace transform is smooth on the open half-line. -/
lemma laplaceTransform_contDiffOn_Ioi (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    ContDiffOn ℝ (⊤ : ℕ∞) (laplaceTransform μ) (Ioi 0) := by
  refine contDiffOn_of_differentiableOn_deriv (𝕜 := ℝ) (n := (⊤ : ℕ∞))
    (s := Ioi (0 : ℝ)) (f := laplaceTransform μ) ?_
  intro m _hm
  have hdiff_moment : DifferentiableOn ℝ (laplaceMomentTransform μ m) (Ioi 0) := by
    intro t ht
    exact (hasDerivAt_laplaceMomentTransform μ m ht).differentiableAt.differentiableWithinAt
  exact hdiff_moment.congr fun t ht =>
    iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform μ m ht

/-- Every finite-measure Laplace transform is completely monotone on `(0, ∞)`. -/
theorem laplaceTransform_isCompletelyMonotoneOnIoi
    (μ : Measure ℝ≥0) [IsFiniteMeasure μ] :
    IsCompletelyMonotoneOnIoi (laplaceTransform μ) := by
  refine ⟨laplaceTransform_contDiffOn_Ioi μ, fun n t ht => ?_⟩
  rw [iteratedDeriv_laplaceTransform_eq_laplaceMomentTransform μ n ht]
  rw [laplaceMomentTransform]
  rw [← integral_const_mul]
  refine integral_nonneg fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp : 0 ≤ Real.exp (-(t * (x : ℝ))) := Real.exp_nonneg _
  have heq : (-1 : ℝ) ^ n * ((-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) =
      (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  simpa [heq] using mul_nonneg hpow hexp

/-- The Laplace transform of a finite measure is completely monotone in the closed-half-line
roadmap sense. -/
theorem laplaceTransform_isClosedCompletelyMonotone
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ] :
    IsClosedCompletelyMonotone (laplaceTransform μ) :=
  isClosedCompletelyMonotone_iff.mpr
    ⟨laplaceTransform_continuousOn_halfLine μ, laplaceTransform_isCompletelyMonotoneOnIoi μ⟩

/-- Strong easy direction: with all moments finite, the Laplace transform satisfies the existing
`IsCompletelyMonotone` predicate using derivatives within `[0, ∞)`. -/
theorem laplaceTransform_isCompletelyMonotone_of_moments
    (μ : Measure ℝ≥0) [hμ : IsFiniteMeasure μ]
    (hmom : ∀ n : ℕ, Integrable (fun x : ℝ≥0 => (x : ℝ) ^ n) μ) :
    IsCompletelyMonotone (laplaceTransform μ) := by
  refine ⟨laplaceTransform_contDiffOn_Ici_of_moments μ hmom, fun n t ht => ?_⟩
  rw [iteratedDerivWithin_laplaceTransform_eq_laplaceMomentTransform_Ici μ hmom n ht]
  rw [laplaceMomentTransform]
  rw [← integral_const_mul]
  refine integral_nonneg fun x => ?_
  have hx : 0 ≤ (x : ℝ) := x.2
  have hpow : 0 ≤ (x : ℝ) ^ n := pow_nonneg hx n
  have hexp : 0 ≤ Real.exp (-(t * (x : ℝ))) := Real.exp_nonneg _
  have heq : (-1 : ℝ) ^ n * ((-(x : ℝ)) ^ n * Real.exp (-(t * (x : ℝ)))) =
      (x : ℝ) ^ n * Real.exp (-(t * (x : ℝ))) := by
    rw [← mul_assoc, ← mul_pow, neg_one_mul, neg_neg]
  simpa [heq] using mul_nonneg hpow hexp

/-! ## Representation predicate -/

/-- A finite measure represents a function by its Laplace transform on the nonnegative
half-line. -/
def RepresentsLaplace (f : ℝ → ℝ) (μ : Measure ℝ≥0) : Prop :=
  IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t

/-- `RepresentsLaplace f μ` unfolds to finiteness of `μ` and equality with the Laplace transform
on the nonnegative half-line. -/
lemma representsLaplace_iff {f : ℝ → ℝ} {μ : Measure ℝ≥0} :
    RepresentsLaplace f μ ↔
      IsFiniteMeasure μ ∧ ∀ t : ℝ, 0 ≤ t → f t = laplaceTransform μ t :=
  Iff.rfl

namespace RepresentsLaplace

variable {f : ℝ → ℝ} {μ : Measure ℝ≥0}

/-- A representing measure is finite. -/
lemma isFiniteMeasure (h : RepresentsLaplace f μ) : IsFiniteMeasure μ := h.1

/-- A representing measure has the advertised Laplace-transform values on `[0, ∞)`. -/
lemma eq_laplaceTransform (h : RepresentsLaplace f μ) {t : ℝ} (ht : 0 ≤ t) :
    f t = laplaceTransform μ t :=
  h.2 t ht

end RepresentsLaplace

end TauCeti
