/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# The Donsker–Varadhan variational formula for relative entropy

For finite measures `μ` and `ν`, Mathlib's relative entropy `klDiv μ ν` is the `I`-divergence
`∫ klFun (dμ/dν) dν`, where `klFun x = x log x + 1 - x`, and it carries the mass correction
`ν univ - μ univ`. The convex conjugate of `klFun` is `y ↦ exp y - 1`, and integrating the
Fenchel–Young inequality gives a variational formula with the mass correction built in:
`klDiv μ ν = sup_f (∫ f dμ - ∫ (exp f - 1) dν)`, the supremum running over bounded measurable
functions. On a pseudometrizable Borel space the bounded continuous functions already give the
supremum. For probability measures the formula takes the classical Donsker–Varadhan form
`klDiv μ ν = sup_f (∫ f dμ - log ∫ exp f dν)`.

Each functional `(μ, ν) ↦ ∫ f dμ - ∫ (exp f - 1) dν` with `f` bounded and continuous is continuous
for the weak topology, so the continuous form of the formula makes `klDiv` jointly lower
semicontinuous on pairs of finite measures, and on pairs of probability measures. This is the
lower semicontinuity used by stability and limit theorems for entropic optimal transport, where
both the coupling and the reference measure move.

## Main statements

* `TauCeti.mul_sub_exp_sub_one_le_klFun`: the Fenchel–Young inequality
  `x * y - (exp y - 1) ≤ klFun x` for `x ≥ 0`.
* `TauCeti.ofReal_integral_sub_integral_exp_sub_one_le_klDiv` and
  `TauCeti.ofReal_integral_sub_log_integral_exp_le_klDiv`: the variational lower bounds, for
  every integrable `f` with integrable `exp ∘ f`.
* `TauCeti.klDiv_eq_iSup_integral_sub_integral_exp_sub_one` and
  `TauCeti.klDiv_eq_iSup_integral_sub_log_integral_exp`: the variational formulas over bounded
  measurable functions, on an arbitrary measurable space.
* `TauCeti.klDiv_eq_iSup_boundedContinuousFunction_integral_sub_integral_exp_sub_one` and
  `TauCeti.klDiv_eq_iSup_boundedContinuousFunction_integral_sub_log_integral_exp`: the same
  formulas over bounded continuous functions, on a pseudometrizable Borel space.
* `TauCeti.lowerSemicontinuous_klDiv_finiteMeasure` and
  `TauCeti.lowerSemicontinuous_klDiv_probabilityMeasure`: joint weak lower semicontinuity.

## References

* M. D. Donsker and S. R. S. Varadhan, *Asymptotic evaluation of certain Markov process
  expectations for large time. IV*, Comm. Pure Appl. Math. 36 (1983), 183–212.
* Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University
  Press, 2025, Chapter 4 (variational characterizations and lower semicontinuity of divergence).
-/

public section

open MeasureTheory Real InformationTheory Filter Set Topology
open scoped ENNReal BoundedContinuousFunction

namespace TauCeti

/-- The **Fenchel–Young inequality** for `klFun`: the convex conjugate of
`klFun x = x log x + 1 - x` on `[0, ∞)` is `y ↦ exp y - 1`. -/
theorem mul_sub_exp_sub_one_le_klFun {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    x * y - (exp y - 1) ≤ klFun x := by
  rw [klFun_apply]
  rcases hx.eq_or_lt with rfl | hx
  · simp [(exp_pos y).le]
  · -- `exp (y - log x) ≥ 1 + y - log x`, multiplied by `x`.
    have h := mul_le_mul_of_nonneg_left (add_one_le_exp (y - log x)) hx.le
    rw [exp_sub, exp_log hx, mul_div_cancel₀ _ hx.ne'] at h
    linarith

variable {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ}

/-- For `μ ≪ ν`, the variational objective is a single `ν`-integral against the density. -/
private lemma integral_sub_integral_exp_sub_one_eq [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμν : μ ≪ ν) (hf : Integrable f μ) (hef : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν =
      ∫ x, ((μ.rnDeriv ν x).toReal * f x - (exp (f x) - 1)) ∂ν := by
  have hef' : Integrable (fun x ↦ exp (f x) - 1) ν := hef.sub (integrable_const 1)
  rw [integral_sub ((integrable_toReal_rnDeriv_mul_iff hμν).2 hf) hef',
    integral_toReal_rnDeriv_mul hμν]

/-- **Variational lower bound** for relative entropy between finite measures, with the mass
correction built in: `∫ f dμ - ∫ (exp f - 1) dν ≤ klDiv μ ν`. -/
theorem ofReal_integral_sub_integral_exp_sub_one_le_klDiv [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : Integrable f μ) (hef : Integrable (fun x ↦ exp (f x)) ν) :
    ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν) ≤ klDiv μ ν := by
  by_cases h : klDiv μ ν = ∞
  · simp [h]
  obtain ⟨hμν, hllr⟩ := klDiv_ne_top_iff.1 h
  rw [klDiv_eq_integral_klFun, ite_eq_left ⟨hμν, hllr⟩,
    integral_sub_integral_exp_sub_one_eq hμν hf hef]
  have hef' : Integrable (fun x ↦ exp (f x) - 1) ν := hef.sub (integrable_const 1)
  refine ENNReal.ofReal_le_ofReal (integral_mono
    (((integrable_toReal_rnDeriv_mul_iff hμν).2 hf).sub hef')
    ((integrable_klFun_rnDeriv_iff hμν).2 hllr) fun x ↦ ?_)
  exact mul_sub_exp_sub_one_le_klFun ENNReal.toReal_nonneg _

/-- Against a probability measure, the mass-corrected objective is at most the
Donsker–Varadhan objective, since `log z ≤ z - 1`. -/
private lemma integral_sub_integral_exp_sub_one_le_integral_sub_log_integral_exp
    [IsProbabilityMeasure ν] (hef : Integrable (fun x ↦ exp (f x)) ν) :
    ∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν ≤ ∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν) := by
  rw [integral_sub hef (integrable_const 1)]
  have := log_le_sub_one_of_pos (integral_exp_pos hef)
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith

/-- The **Donsker–Varadhan lower bound** (Gibbs variational inequality) for probability measures:
`∫ f dμ - log ∫ exp f dν ≤ klDiv μ ν`. -/
theorem ofReal_integral_sub_log_integral_exp_le_klDiv [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hf : Integrable f μ) (hef : Integrable (fun x ↦ exp (f x)) ν) :
    ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) ≤ klDiv μ ν := by
  set Z := ∫ x, exp (f x) ∂ν
  have hZ : 0 < Z := integral_exp_pos hef
  have hexp : (fun x ↦ exp (f x - log Z)) = fun x ↦ exp (f x) / Z := by
    ext x; rw [exp_sub, exp_log hZ]
  have hef' : Integrable (fun x ↦ exp (f x - log Z)) ν := hexp ▸ hef.div_const Z
  have hf' : Integrable (fun x ↦ f x - log Z) μ := hf.sub (integrable_const _)
  convert ofReal_integral_sub_integral_exp_sub_one_le_klDiv hf' hef' using 2
  rw [integral_sub hf (integrable_const _), integral_sub hef' (integrable_const _), hexp,
    integral_div, div_self hZ.ne']
  simp

/-- A bounded measurable function is integrable, and so is its exponential. -/
private lemma integrable_and_integrable_exp [IsFiniteMeasure μ] (hf : Measurable f) {C : ℝ}
    (hC : ∀ x, |f x| ≤ C) : Integrable f μ ∧ Integrable (fun x ↦ exp (f x)) μ :=
  ⟨.of_bound hf.aestronglyMeasurable C (ae_of_all _ hC),
    .of_bound hf.exp.aestronglyMeasurable (exp C) (ae_of_all _ fun x ↦ by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      exact exp_le_exp.2 (le_of_abs_le (hC x)))⟩

/-- Off the absolutely continuous case, the objectives along `n • 1_s`, for a `ν`-null measurable
set `s` of positive `μ`-measure, are unbounded. -/
private lemma exists_seq_of_not_absolutelyContinuous [IsFiniteMeasure μ]
    (hμν : ¬ μ ≪ ν) :
    ∃ g : ℕ → α → ℝ, (∀ n, Measurable (g n)) ∧ (∀ n, ∃ C, ∀ x, |g n x| ≤ C) ∧
      klDiv μ ν ≤ ⨆ n, ENNReal.ofReal (∫ x, g n x ∂μ - ∫ x, (exp (g n x) - 1) ∂ν) := by
  obtain ⟨s, hνs, hμs⟩ : ∃ s, ν s = 0 ∧ μ s ≠ 0 := by
    simpa [Measure.AbsolutelyContinuous] using hμν
  set t := toMeasurable ν s
  have ht : MeasurableSet t := measurableSet_toMeasurable ν s
  have hνt : ν t = 0 := (measure_toMeasurable s).trans hνs
  have hμt : 0 < μ.real t := ENNReal.toReal_pos
    (fun h ↦ hμs (measure_mono_null (subset_toMeasurable ν s) h)) (measure_ne_top μ t)
  refine ⟨fun n ↦ t.indicator fun _ ↦ (n : ℝ), fun n ↦ measurable_const.indicator ht,
    fun n ↦ ⟨n, fun x ↦ ?_⟩, ?_⟩
  · by_cases hx : x ∈ t <;> simp [hx]
  rw [klDiv_of_not_ac hμν]
  refine (ENNReal.eq_top_of_forall_nnreal_le fun r ↦ ?_).ge
  obtain ⟨n, hn⟩ := exists_nat_ge ((r : ℝ) / μ.real t)
  refine le_trans ?_ (le_iSup _ n)
  have hν0 : ∀ᵐ x ∂ν, exp (t.indicator (fun _ ↦ (n : ℝ)) x) - 1 = 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hνt] with x hx
    simp [hx]
  rw [integral_congr_ae hν0, integral_zero, sub_zero, integral_indicator_const _ ht,
    smul_eq_mul, ← ENNReal.ofReal_coe_nnreal]
  exact ENNReal.ofReal_le_ofReal (by rwa [div_le_iff₀ hμt, mul_comm] at hn)

/-- The density `r` clamped to `[(n + 1)⁻¹, n + 1]`, which lies between `1` and `r`. -/
private lemma clamp_spec (r : ℝ) (n : ℕ) :
    0 < max (min r (n + 1)) (1 / (n + 1)) ∧
      0 ≤ (max (min r (n + 1)) (1 / (n + 1)) - 1) * (r - max (min r (n + 1)) (1 / (n + 1))) ∧
      |log (max (min r (n + 1)) (1 / (n + 1)))| ≤ log (n + 1) := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  have hn1 : (1 : ℝ) ≤ n + 1 := by simp
  have hinv : 1 / ((n : ℝ) + 1) ≤ 1 := (div_le_one hn).2 hn1
  set c := max (min r (n + 1)) (1 / (n + 1)) with hc
  have hc0 : 0 < c := lt_max_of_lt_right (by positivity)
  have hcle : c ≤ n + 1 := max_le (min_le_right _ _) (hinv.trans hn1)
  have hcge : 1 / ((n : ℝ) + 1) ≤ c := le_max_right _ _
  refine ⟨hc0, ?_, abs_le.2 ⟨?_, log_le_log hc0 hcle⟩⟩
  · rcases le_or_gt 1 r with h1 | h1
    · have hmin : 1 ≤ min r (n + 1) := le_min h1 hn1
      rw [hc, max_eq_left (hinv.trans hmin)]
      exact mul_nonneg (by linarith) (by linarith [min_le_left r (n + 1)])
    · rw [hc, min_eq_left (h1.le.trans hn1)]
      exact mul_nonneg_of_nonpos_of_nonpos (by linarith [max_le h1.le hinv])
        (by linarith [le_max_left r (1 / (n + 1))])
  · have := log_le_log (by positivity) hcge
    rw [one_div, log_inv] at this
    linarith

/-- `r log c - (c - 1) ≥ 0` when `c > 0` lies between `1` and `r`. -/
private lemma mul_log_sub_sub_one_nonneg {r c : ℝ} (hr : 0 ≤ r) (hc : 0 < c)
    (h : 0 ≤ (c - 1) * (r - c)) : 0 ≤ r * log c - (c - 1) := by
  have h1 := mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hc) hr
  have h2 : r * (1 - c⁻¹) - (c - 1) = (c - 1) * (r - c) / c := by field_simp
  have h3 : 0 ≤ (c - 1) * (r - c) / c := div_nonneg h hc.le
  linarith

/-- The clamped densities converge to `r`. -/
private lemma tendsto_clamp {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ ↦ max (min r (n + 1)) (1 / (n + 1))) atTop (𝓝 r) := by
  have hmin : Tendsto (fun n : ℕ ↦ min r (n + 1)) atTop (𝓝 r) :=
    tendsto_const_nhds.congr' <| (eventually_ge_atTop ⌈r⌉₊).mono fun n hn ↦
      (min_eq_left ((Nat.le_ceil r).trans (by exact_mod_cast hn.trans (Nat.le_succ n)))).symm
  simpa [max_eq_left hr] using hmin.max (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))

/-- The objectives along the logarithms of the clamped densities `dμ/dν` converge to
`klDiv μ ν`, by Fatou's lemma; only the resulting inequality is recorded. Together with the
non-absolutely-continuous case, every finite pair has a sequence of bounded measurable functions
whose objectives reach `klDiv μ ν`. -/
private lemma exists_seq_klDiv_le_iSup [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    ∃ g : ℕ → α → ℝ, (∀ n, Measurable (g n)) ∧ (∀ n, ∃ C, ∀ x, |g n x| ≤ C) ∧
      klDiv μ ν ≤ ⨆ n, ENNReal.ofReal (∫ x, g n x ∂μ - ∫ x, (exp (g n x) - 1) ∂ν) := by
  by_cases hμν : μ ≪ ν
  swap; · exact exists_seq_of_not_absolutelyContinuous hμν
  set ρ : α → ℝ := fun x ↦ (μ.rnDeriv ν x).toReal
  have hρ : Measurable ρ := (Measure.measurable_rnDeriv μ ν).ennreal_toReal
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x ↦ ENNReal.toReal_nonneg
  set c : ℕ → α → ℝ := fun n x ↦ max (min (ρ x) (n + 1)) (1 / (n + 1))
  have hcm : ∀ n, Measurable (c n) := fun n ↦
    (hρ.min measurable_const).max measurable_const
  set g : ℕ → α → ℝ := fun n x ↦ log (c n x)
  have hgm : ∀ n, Measurable (g n) := fun n ↦ (hcm n).log
  have hgC : ∀ n x, |g n x| ≤ log (n + 1) := fun n x ↦ (clamp_spec (ρ x) n).2.2
  refine ⟨g, hgm, fun n ↦ ⟨_, hgC n⟩, ?_⟩
  -- The integrand of the `n`-th objective against `ν`, which is nonnegative.
  set h : ℕ → α → ℝ := fun n x ↦ ρ x * log (c n x) - (c n x - 1)
  have hh0 : ∀ n x, 0 ≤ h n x := fun n x ↦
    mul_log_sub_sub_one_nonneg (hρ0 x) (clamp_spec (ρ x) n).1 (clamp_spec (ρ x) n).2.1
  have hval : ∀ n, ENNReal.ofReal (∫ x, g n x ∂μ - ∫ x, (exp (g n x) - 1) ∂ν) =
      ∫⁻ x, ENNReal.ofReal (h n x) ∂ν := fun n ↦ by
    obtain ⟨hgi, _⟩ := integrable_and_integrable_exp (μ := μ) (hgm n) (hgC n)
    obtain ⟨-, hegi'⟩ := integrable_and_integrable_exp (μ := ν) (hgm n) (hgC n)
    have heq : (fun x ↦ ρ x * g n x - (exp (g n x) - 1)) = h n := by
      ext x
      simp only [h, g]
      rw [exp_log (show 0 < c n x from (clamp_spec (ρ x) n).1)]
    rw [integral_sub_integral_exp_sub_one_eq hμν hgi hegi', heq,
      ofReal_integral_eq_lintegral_ofReal (heq ▸
        ((integrable_toReal_rnDeriv_mul_iff hμν).2 hgi).sub
          (hegi'.sub (integrable_const 1))) (ae_of_all _ (hh0 n))]
  -- Pointwise, the integrands converge to `klFun ρ`.
  have hlim : ∀ x, Tendsto (fun n ↦ ENNReal.ofReal (h n x)) atTop
      (𝓝 (ENNReal.ofReal (klFun (ρ x)))) := fun x ↦ by
    refine (ENNReal.continuous_ofReal.tendsto _).comp ?_
    rw [klFun_apply, show ρ x * log (ρ x) + 1 - ρ x = ρ x * log (ρ x) - (ρ x - 1) by ring]
    refine Tendsto.sub ?_ ((tendsto_clamp (hρ0 x)).sub_const 1)
    rcases (hρ0 x).eq_or_lt with h0 | h0
    · simp [← h0]
    · exact ((continuousAt_log h0.ne').tendsto.comp (tendsto_clamp (hρ0 x))).const_mul _
  calc klDiv μ ν = ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (h n x)) atTop ∂ν := by
        rw [klDiv_eq_lintegral_klFun_of_ac hμν]
        exact lintegral_congr fun x ↦ (hlim x).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (h n x) ∂ν) atTop :=
        lintegral_liminf_le fun n ↦ ENNReal.measurable_ofReal.comp
          ((hρ.mul (hcm n).log).sub ((hcm n).sub_const 1))
    _ ≤ ⨆ n, ∫⁻ x, ENNReal.ofReal (h n x) ∂ν := le_trans liminf_le_limsup limsup_le_iSup
    _ = _ := by simp_rw [hval]

/-- The **variational formula** for the relative entropy of finite measures, with the mass
correction built in: `klDiv μ ν` is the supremum of `∫ f dμ - ∫ (exp f - 1) dν` over bounded
measurable functions `f`. -/
theorem klDiv_eq_iSup_integral_sub_integral_exp_sub_one [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = ⨆ (f : α → ℝ) (_ : Measurable f) (_ : ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦ iSup_le fun ⟨C, hC⟩ ↦
    ofReal_integral_sub_integral_exp_sub_one_le_klDiv
      (integrable_and_integrable_exp hf hC).1 (integrable_and_integrable_exp hf hC).2)
  obtain ⟨g, hgm, hgC, hle⟩ := exists_seq_klDiv_le_iSup (μ := μ) (ν := ν)
  exact hle.trans (iSup_le fun n ↦ le_iSup₂_of_le (g n) (hgm n) (le_iSup_of_le (hgC n) le_rfl))

/-- The **Donsker–Varadhan variational formula**: for probability measures, `klDiv μ ν` is the
supremum of `∫ f dμ - log ∫ exp f dν` over bounded measurable functions `f`. -/
theorem klDiv_eq_iSup_integral_sub_log_integral_exp [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    klDiv μ ν = ⨆ (f : α → ℝ) (_ : Measurable f) (_ : ∃ C, ∀ x, |f x| ≤ C),
      ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) := by
  refine le_antisymm ?_ (iSup₂_le fun f hf ↦ iSup_le fun ⟨C, hC⟩ ↦
    ofReal_integral_sub_log_integral_exp_le_klDiv
      (integrable_and_integrable_exp hf hC).1 (integrable_and_integrable_exp hf hC).2)
  rw [klDiv_eq_iSup_integral_sub_integral_exp_sub_one]
  refine iSup₂_mono fun f hf ↦ iSup_mono fun ⟨C, hC⟩ ↦ ENNReal.ofReal_le_ofReal ?_
  exact integral_sub_integral_exp_sub_one_le_integral_sub_log_integral_exp
    (integrable_and_integrable_exp hf hC).2

section Topological

variable [TopologicalSpace α] [TopologicalSpace.PseudoMetrizableSpace α] [BorelSpace α]

omit [TopologicalSpace.PseudoMetrizableSpace α] in
/-- A bounded continuous function is integrable, and so is its exponential. -/
private lemma integrable_and_integrable_exp_of_boundedContinuousFunction [IsFiniteMeasure μ]
    (f : α →ᵇ ℝ) : Integrable f μ ∧ Integrable (fun x ↦ exp (f x)) μ :=
  integrable_and_integrable_exp f.continuous.measurable fun x ↦
    (Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm x)

/-- A bounded measurable function `f ≤ C` is approximated, in the variational objective, by a
bounded continuous function: approximate `f` in `L¹(μ + ν)` and truncate at `C`, using that
`exp` is `exp C`-Lipschitz on `(-∞, C]`. -/
private lemma exists_boundedContinuousFunction_le [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hf : Measurable f) {C : ℝ} (hC : ∀ x, |f x| ≤ C) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : α →ᵇ ℝ, ∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν - ε ≤
      ∫ x, g x ∂μ - ∫ x, (exp (g x) - 1) ∂ν := by
  have hδ : 0 < ε / (1 + exp C) := by positivity
  obtain ⟨g₀, hg₀, -⟩ :=
    (integrable_and_integrable_exp (μ := μ + ν) hf hC).1.exists_boundedContinuous_integral_sub_le hδ
  set g : α →ᵇ ℝ := g₀ ⊓ BoundedContinuousFunction.const α C
  have hg : ∀ x, g x = min (g₀ x) C := fun x ↦ by simp [g]
  have hdist : ∀ x, |f x - g x| ≤ ‖f x - g₀ x‖ := fun x ↦ by
    have := abs_min_sub_min_le_max (f x) C (g₀ x) C
    rwa [sub_self, abs_zero, max_eq_left (abs_nonneg _), min_eq_left (le_of_abs_le (hC x)),
      ← hg, ← Real.norm_eq_abs] at this
  have hexp : ∀ x, exp (g x) - exp (f x) ≤ exp C * ‖f x - g₀ x‖ := fun x ↦ by
    have h1 := mul_le_mul_of_nonneg_left (add_one_le_exp (f x - g x)) (exp_pos (g x)).le
    rw [exp_sub, mul_div_cancel₀ _ (exp_pos _).ne'] at h1
    have h2 : exp (g x) ≤ exp C := exp_le_exp.2 ((hg x).trans_le (min_le_right _ _))
    have h3 := (le_abs_self (g x - f x)).trans ((abs_sub_comm _ _).trans_le (hdist x))
    nlinarith [exp_pos (g x), norm_nonneg (f x - g₀ x)]
  -- Integrability of everything in sight.
  obtain ⟨hfμ, -⟩ := integrable_and_integrable_exp (μ := μ) hf hC
  obtain ⟨-, hefν⟩ := integrable_and_integrable_exp (μ := ν) hf hC
  obtain ⟨hgμ, -⟩ := integrable_and_integrable_exp_of_boundedContinuousFunction (μ := μ) g
  obtain ⟨-, hegν⟩ := integrable_and_integrable_exp_of_boundedContinuousFunction (μ := ν) g
  have hD : Integrable (fun x ↦ ‖f x - g₀ x‖) (μ + ν) :=
    ((integrable_and_integrable_exp hf hC).1.sub (g₀.integrable _)).norm
  obtain ⟨hDμ, hDν⟩ := integrable_add_measure.1 hD
  rw [integral_add_measure hDμ hDν] at hg₀
  have hA : ∫ x, f x ∂μ - ∫ x, g x ∂μ ≤ ∫ x, ‖f x - g₀ x‖ ∂μ := by
    rw [← integral_sub hfμ hgμ]
    exact integral_mono (hfμ.sub hgμ) hDμ fun x ↦ (le_abs_self _).trans (hdist x)
  have hB : ∫ x, (exp (g x) - 1) ∂ν - ∫ x, (exp (f x) - 1) ∂ν ≤
      exp C * ∫ x, ‖f x - g₀ x‖ ∂ν := by
    have hg1 : Integrable (fun x ↦ exp (g x) - 1) ν := hegν.sub (integrable_const 1)
    have hf1 : Integrable (fun x ↦ exp (f x) - 1) ν := hefν.sub (integrable_const 1)
    rw [← integral_sub hg1 hf1, ← integral_const_mul]
    exact integral_mono (hg1.sub hf1) (hDν.const_mul _) fun x ↦ by
      dsimp only
      linarith [hexp x]
  have hDμ0 : 0 ≤ ∫ x, ‖f x - g₀ x‖ ∂μ := integral_nonneg fun _ ↦ norm_nonneg _
  have hDν0 : 0 ≤ ∫ x, ‖f x - g₀ x‖ ∂ν := integral_nonneg fun _ ↦ norm_nonneg _
  have hε' : (1 + exp C) * (ε / (1 + exp C)) = ε := by field_simp
  have h1 := mul_le_mul_of_nonneg_left hg₀ (by positivity : (0 : ℝ) ≤ 1 + exp C)
  have h2 := mul_nonneg (exp_pos C).le hDμ0
  exact ⟨g, by linarith⟩

/-- The **variational formula** for the relative entropy of finite measures on a
pseudometrizable Borel space: `klDiv μ ν` is the supremum of `∫ f dμ - ∫ (exp f - 1) dν` over
bounded continuous functions `f`. -/
theorem klDiv_eq_iSup_boundedContinuousFunction_integral_sub_integral_exp_sub_one
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv μ ν = ⨆ f : α →ᵇ ℝ, ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν) := by
  refine le_antisymm ?_ (iSup_le fun f ↦ ofReal_integral_sub_integral_exp_sub_one_le_klDiv
    (integrable_and_integrable_exp_of_boundedContinuousFunction f).1
    (integrable_and_integrable_exp_of_boundedContinuousFunction f).2)
  obtain ⟨g, hgm, hgC, hle⟩ := exists_seq_klDiv_le_iSup (μ := μ) (ν := ν)
  refine hle.trans (iSup_le fun n ↦ ENNReal.le_of_forall_pos_le_add fun ε hε _ ↦ ?_)
  obtain ⟨C, hC⟩ := hgC n
  obtain ⟨h, hh⟩ := exists_boundedContinuousFunction_le (μ := μ) (ν := ν) (hgm n) hC
    (NNReal.coe_pos.2 hε)
  calc ENNReal.ofReal (∫ x, g n x ∂μ - ∫ x, (exp (g n x) - 1) ∂ν)
      ≤ ENNReal.ofReal ((∫ x, h x ∂μ - ∫ x, (exp (h x) - 1) ∂ν) + ε) :=
        ENNReal.ofReal_le_ofReal (by linarith)
    _ ≤ ENNReal.ofReal (∫ x, h x ∂μ - ∫ x, (exp (h x) - 1) ∂ν) + ε := by
        rw [← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_add_le
    _ ≤ _ := by
        gcongr
        exact le_iSup (fun f : α →ᵇ ℝ ↦
          ENNReal.ofReal (∫ x, f x ∂μ - ∫ x, (exp (f x) - 1) ∂ν)) h

/-- The **Donsker–Varadhan variational formula** on a pseudometrizable Borel space: for
probability measures, `klDiv μ ν` is the supremum of `∫ f dμ - log ∫ exp f dν` over bounded
continuous functions `f`. -/
theorem klDiv_eq_iSup_boundedContinuousFunction_integral_sub_log_integral_exp
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    klDiv μ ν = ⨆ f : α →ᵇ ℝ, ENNReal.ofReal (∫ x, f x ∂μ - log (∫ x, exp (f x) ∂ν)) := by
  refine le_antisymm ?_ (iSup_le fun f ↦ ofReal_integral_sub_log_integral_exp_le_klDiv
    (integrable_and_integrable_exp_of_boundedContinuousFunction f).1
    (integrable_and_integrable_exp_of_boundedContinuousFunction f).2)
  rw [klDiv_eq_iSup_boundedContinuousFunction_integral_sub_integral_exp_sub_one]
  exact iSup_mono fun f ↦ ENNReal.ofReal_le_ofReal
    (integral_sub_integral_exp_sub_one_le_integral_sub_log_integral_exp
      (integrable_and_integrable_exp_of_boundedContinuousFunction f).2)

/-- **Lower semicontinuity of relative entropy**: `(μ, ν) ↦ klDiv μ ν` is jointly lower
semicontinuous for the weak topology on pairs of finite measures. -/
theorem lowerSemicontinuous_klDiv_finiteMeasure :
    LowerSemicontinuous fun p : FiniteMeasure α × FiniteMeasure α ↦
      klDiv (p.1 : Measure α) (p.2 : Measure α) := by
  simp_rw [klDiv_eq_iSup_boundedContinuousFunction_integral_sub_integral_exp_sub_one]
  refine lowerSemicontinuous_iSup fun f ↦ Continuous.lowerSemicontinuous ?_
  -- `x ↦ exp (f x) - 1` is again bounded and continuous.
  obtain ⟨e, he⟩ : ∃ e : α →ᵇ ℝ, ∀ x, e x = exp (f x) - 1 := by
    refine ⟨.mkOfBound ⟨fun x ↦ exp (f x) - 1, by fun_prop⟩ (exp ‖f‖) fun x y ↦ ?_,
      fun _ ↦ rfl⟩
    have hb : ∀ x, exp (f x) ≤ exp ‖f‖ := fun x ↦ exp_le_exp.2
      ((le_abs_self _).trans ((Real.norm_eq_abs _).symm.trans_le (f.norm_coe_le_norm x)))
    simp only [ContinuousMap.coe_mk, Real.dist_eq]
    exact abs_sub_le_iff.2 ⟨by linarith [hb x, exp_pos (f y)], by linarith [hb y, exp_pos (f x)]⟩
  simp_rw [← he]
  exact ENNReal.continuous_ofReal.comp
    (((FiniteMeasure.continuous_integral_boundedContinuousFunction f).comp continuous_fst).sub
      ((FiniteMeasure.continuous_integral_boundedContinuousFunction e).comp continuous_snd))

/-- **Lower semicontinuity of relative entropy**: `(μ, ν) ↦ klDiv μ ν` is jointly lower
semicontinuous for the weak topology on pairs of probability measures. -/
theorem lowerSemicontinuous_klDiv_probabilityMeasure :
    LowerSemicontinuous fun p : ProbabilityMeasure α × ProbabilityMeasure α ↦
      klDiv (p.1 : Measure α) (p.2 : Measure α) :=
  lowerSemicontinuous_klDiv_finiteMeasure.comp
    (ProbabilityMeasure.toFiniteMeasure_continuous.prodMap
      ProbabilityMeasure.toFiniteMeasure_continuous)

end Topological

end TauCeti
