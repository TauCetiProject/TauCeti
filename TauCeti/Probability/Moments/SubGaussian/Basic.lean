/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Moments.MGFAnalytic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import TauCeti.Analysis.Calculus.DerivativeTest
import TauCeti.MeasureTheory.Integral.Bochner.Fatou

/-!
# Basic properties of sub-Gaussian moment-generating functions

A sub-Gaussian moment-generating function bound forces the total mass to be at most `1`, so the
measure is finite; the zero random variable satisfies the bound exactly when the total mass is at
most `1`, and a random variable has variance proxy `0` exactly when, in addition, it vanishes
almost everywhere.

Under a zero or probability measure, the quadratic MGF bound forces a sub-Gaussian random
variable to have mean zero and bounds its second moment by the variance proxy. The bound is
monotone in the proxy and, under any measure, bounds the first absolute moment by `√(2c)`. By
Fatou's lemma, an almost everywhere limit of sub-Gaussian random variables with a common variance
proxy is sub-Gaussian with the same proxy; in particular a fixed proxy survives uniform
approximation (`ProbabilityTheory.HasSubgaussianMGF.of_forall_exists_abs_sub_le`), so a Lipschitz
function inherits the concentration of its smooth approximations.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real
open scoped NNReal Topology

namespace ProbabilityTheory.HasSubgaussianMGF

/-- Monotonicity of `HasSubgaussianMGF` in the variance proxy. -/
theorem mono {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ} {c₁ c₂ : ℝ≥0}
    (h : HasSubgaussianMGF X c₁ μ) (hle : c₁ ≤ c₂) : HasSubgaussianMGF X c₂ μ :=
  ⟨h.integrable_exp_mul, fun t ↦ (h.mgf_le t).trans <| by gcongr⟩

/-- A sub-Gaussian moment-generating function bound forces the total mass to be at most `1`. -/
theorem measure_univ_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : μ Set.univ ≤ 1 := by
  simpa using (HasSubgaussianMGF_iff_kernel.1 h).measure_univ_le_one

/-- A measure carrying a random variable with a sub-Gaussian moment-generating function bound is
finite. -/
theorem isFiniteMeasure {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : IsFiniteMeasure μ :=
  ⟨h.measure_univ_le_one.trans_lt ENNReal.one_lt_top⟩

/-- A sub-Gaussian moment-generating function bound forces the real-valued total mass to be at
most `1`: it is the moment-generating function at `0`. -/
theorem measureReal_univ_le_one {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : μ.real Set.univ ≤ 1 := by
  simpa using h.mgf_le 0

/-- Under a zero or probability measure, a sub-Gaussian MGF bound forces the expectation to
vanish. -/
theorem integral_eq_zero {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) : μ[X] = 0 := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  have hset := hX.integrableExpSet_eq_univ
  have hm : 0 ∈ interior (integrableExpSet X μ) := by simp [hset]
  let g : ℝ → ℝ := (fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) - mgf X μ
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [g, Pi.sub_apply] using sub_nonneg.mpr (hX.mgf_le t)
  have hd : HasDerivAt g (-μ[X]) 0 := by
    have he : HasDerivAt (fun t : ℝ ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) 0 0 := by
      convert (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul (c : ℝ)).div_const 2 |>.exp
        using 1 <;> simp
    have hx : HasDerivAt (mgf X μ) μ[X] 0 := by
      simpa using hasDerivAt_mgf hm
    simpa only [g, zero_sub] using he.sub hx
  exact neg_eq_zero.mp (hmin.hasDerivAt_eq_zero hd)

/-- Under a zero or probability measure, the second moment of a sub-Gaussian random variable is at
most its variance proxy. -/
theorem integral_sq_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsZeroOrProbabilityMeasure μ]
    {X : Ω → ℝ} {c : ℝ≥0} (hX : HasSubgaussianMGF X c μ) :
    ∫ ω, X ω ^ 2 ∂μ ≤ c := by
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hprob
  · simp
  have hm (t : ℝ) : t ∈ interior (integrableExpSet X μ) := by
    simp [hX.integrableExpSet_eq_univ]
  let g : ℝ → ℝ := (fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2)) - mgf X μ
  have hmin : IsLocalMin g 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [g, Pi.sub_apply] using sub_nonneg.mpr (hX.mgf_le t)
  have he (t : ℝ) : HasDerivAt (fun t : ℝ ↦ Real.exp ((c : ℝ) * t ^ 2 / 2))
      (Real.exp ((c : ℝ) * t ^ 2 / 2) * ((c : ℝ) * t)) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (c : ℝ)).div_const 2 |>.exp using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  have hderiv : deriv g = fun t ↦ Real.exp ((c : ℝ) * t ^ 2 / 2) * ((c : ℝ) * t) -
      deriv (mgf X μ) t := by
    funext t
    exact ((he t).sub (differentiableAt_mgf (hm t)).hasDerivAt).deriv
  have hx : HasDerivAt (deriv (mgf X μ)) (∫ ω, X ω ^ 2 ∂μ) 0 := by
    simpa only [iteratedDeriv_one, Nat.reduceAdd, zero_mul, exp_zero, mul_one] using
      hasDerivAt_iteratedDeriv_mgf (hm 0) 1
  have hsecond : HasDerivAt (deriv g) ((c : ℝ) - ∫ ω, X ω ^ 2 ∂μ) 0 := by
    rw [hderiv]
    convert! ((he 0).mul ((hasDerivAt_id (0 : ℝ)).const_mul (c : ℝ))).sub hx using 1
    simp
  have hnonneg := TauCeti.deriv_deriv_nonneg_of_isLocalMin
    ((he 0).continuousAt.sub (differentiableAt_mgf (hm 0)).continuousAt) hmin
  rw [hsecond.deriv] at hnonneg
  linarith

/-- The first absolute moment of a sub-Gaussian random variable is at most `√(2c)`. -/
theorem integral_abs_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    {c : ℝ≥0} (h : HasSubgaussianMGF X c μ) : ∫ x, |X x| ∂μ ≤ sqrt (2 * c) := by
  by_cases hc : c = 0
  · subst c
    simpa using (integral_congr_ae <|
      h.ae_eq_zero_of_hasSubgaussianMGF_zero.fun_comp abs).le
  have hc' : 0 < (c : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hc)
  let t : ℝ := sqrt (2 / c)
  have ht : 0 < t := sqrt_pos.2 (div_pos (by norm_num) hc')
  have ht2 : (c : ℝ) * t ^ 2 / 2 = 1 := by
    dsimp [t]
    rw [sq_sqrt (by positivity)]
    field_simp
  have hts : t * sqrt (2 * c) = 2 := by
    rw [← sqrt_mul (by positivity : 0 ≤ 2 / (c : ℝ))]
    field_simp
    apply (sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  -- Normalize the exponential comparison at the scale of the variance proxy.
  have hpoint (x : Ω) :
      t * |X x| ≤ (exp (t * X x) + exp ((-t) * X x)) * exp (-1) := by
    calc t * |X x|
        ≤ exp (t * |X x| - 1) := by simpa using add_one_le_exp (t * |X x| - 1)
      _ = exp |t * X x| * exp (-1) := by rw [abs_mul, abs_of_pos ht, ← exp_add, sub_eq_add_neg]
      _ ≤ (exp (t * X x) + exp ((-t) * X x)) * exp (-1) := by
        simpa only [neg_mul] using mul_le_mul_of_nonneg_right (exp_abs_le (t * X x))
          (exp_pos (-1)).le
  have hbound : t * ∫ x, |X x| ∂μ ≤ 2 := by
    calc t * ∫ x, |X x| ∂μ
        ≤ (mgf X μ t + mgf X μ (-t)) * exp (-1) := by
          simpa only [Pi.add_apply, integral_const_mul, integral_mul_const,
            integral_add (h.integrable_exp_mul t) (h.integrable_exp_mul (-t)), mgf] using
            integral_mono (h.integrable.abs.const_mul t)
              (((h.integrable_exp_mul t).add (h.integrable_exp_mul (-t))).mul_const
                (exp (-1))) hpoint
      _ ≤ (exp (c * t ^ 2 / 2) + exp (c * (-t) ^ 2 / 2)) * exp (-1) :=
        mul_le_mul_of_nonneg_right (add_le_add (h.mgf_le t) (h.mgf_le (-t)))
          (exp_pos (-1)).le
      _ = 2 := by rw [neg_sq, ht2, ← two_mul, mul_assoc, ← exp_add]; norm_num
  exact (mul_le_mul_iff_right₀ ht).1 (hbound.trans_eq hts.symm)

/-- An almost everywhere limit, along a countably generated filter, of random variables that are
frequently sub-Gaussian with variance proxy `c` is sub-Gaussian with variance proxy `c`. -/
theorem of_tendsto {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    [l.IsCountablyGenerated] {X : ι → Ω → ℝ} {Y : Ω → ℝ} {c : ℝ≥0}
    (h : ∃ᶠ i in l, HasSubgaussianMGF (X i) c μ)
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun i ↦ X i ω) l (𝓝 (Y ω))) : HasSubgaussianMGF Y c μ := by
  obtain ⟨u, hu, hX⟩ := exists_seq_forall_of_frequently h
  -- Apply Fatou's lemma to the exponentials along a sequence of sub-Gaussian terms.
  have hexp (t : ℝ) :
      ∀ᵐ ω ∂μ, Tendsto (fun n ↦ exp (t * X (u n) ω)) atTop (𝓝 (exp (t * Y ω))) :=
    hlim.mono fun ω hω ↦ ((hω.comp hu).const_mul t).rexp
  have hint (t : ℝ) : ∀ᶠ n in atTop, Integrable (fun ω ↦ exp (t * X (u n) ω)) μ :=
    .of_forall fun n ↦ (hX n).integrable_exp_mul t
  have hpos (t : ℝ) : ∀ᶠ n in atTop, 0 ≤ᵐ[μ] fun ω ↦ exp (t * X (u n) ω) :=
    .of_forall fun _ ↦ .of_forall fun _ ↦ (exp_pos _).le
  have hbound (t : ℝ) :
      ∃ᶠ n in atTop, ∫ ω, exp (t * X (u n) ω) ∂μ ≤ exp (c * t ^ 2 / 2) :=
    .of_forall fun n ↦ by
      rw [← mgf]
      exact (hX n).mgf_le t
  refine ⟨fun t ↦ TauCeti.integrable_of_tendsto_of_integral_le (hint t) (hpos t) (hexp t)
    (hbound t), fun t ↦ ?_⟩
  rw [mgf]
  exact TauCeti.integral_le_of_tendsto_of_integral_le (hint t) (hpos t) (hexp t) (hbound t)

/-- Sub-Gaussianity with a fixed variance proxy is stable under uniform approximation: if for
every `ε > 0` some `c`-sub-Gaussian variable is within `ε` of `X` almost everywhere, then `X` is
`c`-sub-Gaussian. -/
theorem of_forall_exists_abs_sub_le {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0}
    (h : ∀ ε > 0, ∃ Y : Ω → ℝ, HasSubgaussianMGF Y c μ ∧ ∀ᵐ ω ∂μ, |X ω - Y ω| ≤ ε) :
    HasSubgaussianMGF X c μ := by
  choose Y hY hXY using h
  -- `X` is the almost-everywhere limit of the approximants at `ε = 1 / (n + 1)`.
  refine of_tendsto (l := atTop) (X := fun n : ℕ ↦ Y (1 / (n + 1)) (by positivity))
    (.of_forall fun n ↦ hY _ _) ?_
  filter_upwards [ae_all_iff.2 fun n : ℕ ↦ hXY (1 / (n + 1)) (by positivity)] with ω hω
  refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat)
  rw [Real.dist_eq, abs_sub_comm]
  exact hω n

end ProbabilityTheory.HasSubgaussianMGF

namespace ProbabilityTheory

/-- The zero random variable has a sub-Gaussian moment-generating function bound, with any
variance proxy, exactly when the total mass is at most `1`. -/
@[simp]
theorem hasSubgaussianMGF_fun_zero_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {c : ℝ≥0} : HasSubgaussianMGF (fun _ : Ω ↦ (0 : ℝ)) c μ ↔ μ Set.univ ≤ 1 := by
  refine ⟨HasSubgaussianMGF.measure_univ_le_one, fun hμ ↦ ?_⟩
  have : IsFiniteMeasure μ := ⟨hμ.trans_lt ENNReal.one_lt_top⟩
  refine ⟨fun t ↦ by simp, fun t ↦ ?_⟩
  have hreal : μ.real Set.univ ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa)
  calc mgf (fun _ ↦ (0 : ℝ)) μ t = μ.real Set.univ := mgf_zero_fun
    _ ≤ 1 := hreal
    _ ≤ exp ((c : ℝ) * t ^ 2 / 2) := Real.one_le_exp (by positivity)

/-- A random variable has a sub-Gaussian moment-generating function bound with variance proxy `0`
exactly when it vanishes almost everywhere and the total mass is at most `1`. -/
@[simp]
theorem hasSubgaussianMGF_zero_proxy_iff {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X : Ω → ℝ} : HasSubgaussianMGF X 0 μ ↔ (∀ᵐ ω ∂μ, X ω = 0) ∧ μ Set.univ ≤ 1 :=
  ⟨fun h ↦ ⟨h.ae_eq_zero_of_hasSubgaussianMGF_zero, h.measure_univ_le_one⟩,
    fun ⟨hX, hμ⟩ ↦ (hasSubgaussianMGF_fun_zero_iff.2 hμ).congr (hX.mono fun _ h ↦ h.symm)⟩

end ProbabilityTheory
