/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Centering
import Mathlib.Probability.Martingale.OptionalSampling
import Mathlib.Probability.Process.HittingTime

/-!
# Tail bounds for discrete Doob compensators

Mathlib's Doob decomposition writes an adapted integrable process `f` indexed by `ℕ` as the sum of
the martingale `martingalePart f ℱ μ` and the predictable process `A = predictablePart f ℱ μ`,
the compensator of `f`. This file controls the upper tail of the compensator of a submartingale at
a fixed index `N` by increments of `f` itself between stopping times and `N`.

* `MeasureTheory.predictablePart_eq_sub`: the compensator is the process minus its martingale
  part.
* `MeasureTheory.integrable_predictablePart`, `MeasureTheory.integral_predictablePart`: the
  compensator of an integrable process is integrable, with expectation `E[f_N] - E[f_0]`.
* `MeasureTheory.setIntegral_predictablePart_sub_stoppedValue`: on an event known at a stopping
  time `σ ≤ N`, the compensator grows from `σ` to `N` by the same amount, on average, as `f`.
* `MeasureTheory.Submartingale.exists_setIntegral_predictablePart_le`: for a submartingale and
  `c > 0` there are stopping times `σ, ρ ≤ N` with
  `∫_{c ≤ A_N} A_N ≤ ∫_{σ < N} (f_N - f_σ) + 2 ∫_{ρ < N} (f_N - f_ρ)`, where the events
  `{σ < N}` and `{ρ < N}` have probability at most `E[f_N - f_0] / c` and
  `2 E[f_N - f_0] / c`.

The stopping times are the first indices at which the compensator is about to reach `c` and
`c / 2`; they are stopping times because the compensator is predictable. When `f` samples a
continuous-time submartingale on a finite grid, the right side involves only values of the process
at bounded stopping times, which is how the class DL property makes discrete compensators along a
sequence of grids uniformly integrable.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, proof of Theorem 1.4.10.
* M. Beiglböck, W. Schachermayer, B. Veliyev, *A short proof of the Doob–Meyer theorem*,
  Stochastic Process. Appl. 122 (2012), 1204–1209.
-/

public section

open Filter Set

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {ℱ : Filtration ℕ m0}

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℕ → Ω → E}

/-- The compensator is the process minus its martingale part. -/
theorem predictablePart_eq_sub (n : ℕ) :
    predictablePart f ℱ μ n = f n - martingalePart f ℱ μ n :=
  eq_sub_of_add_eq' (congrFun (martingalePart_add_predictablePart ℱ μ f) n)

/-- The compensator of an integrable process is integrable at every index. -/
theorem integrable_predictablePart [CompleteSpace E] (hint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    Integrable (predictablePart f ℱ μ n) μ := by
  rw [predictablePart_eq_sub]
  exact (hint n).sub (integrable_martingalePart hint n)

/-- The compensator of an integrable process at `n` has expectation `E[f_n] - E[f_0]`. -/
theorem integral_predictablePart [CompleteSpace E] [SigmaFiniteFiltration μ ℱ]
    (hint : ∀ n, Integrable (f n) μ) (n : ℕ) :
    ∫ ω, predictablePart f ℱ μ n ω ∂μ = ∫ ω, f n ω ∂μ - ∫ ω, f 0 ω ∂μ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [predictablePart_add_one, integral_add' (integrable_predictablePart hint n)
      integrable_condExp, integral_condExp (ℱ.le n), integral_sub' (hint (n + 1)) (hint n), ih]
    abel

/-- **Optional sampling for the Doob compensator.** On an event known at a stopping time
`σ ≤ N`, the compensator of an adapted integrable process grows from `σ` to `N` by the same
amount, on average, as the process itself. -/
theorem setIntegral_predictablePart_sub_stoppedValue [CompleteSpace E] [SigmaFiniteFiltration μ ℱ]
    (hf : StronglyAdapted ℱ f) (hint : ∀ n, Integrable (f n) μ) {σ : Ω → WithTop ℕ}
    (hσ : IsStoppingTime ℱ σ) {N : ℕ} (hσN : ∀ ω, σ ω ≤ N) {s : Set Ω}
    (hs : MeasurableSet[hσ.measurableSpace] s) :
    ∫ ω in s, (predictablePart f ℱ μ N ω - stoppedValue (predictablePart f ℱ μ) σ ω) ∂μ =
      ∫ ω in s, (f N ω - stoppedValue f σ ω) ∂μ := by
  have hM := martingale_martingalePart hf hint (μ := μ)
  have := hσ.sigmaFinite_stopping_time (μ := μ)
  -- Optional sampling for the martingale part removes its increment.
  have hMσ : ∫ ω in s, stoppedValue (martingalePart f ℱ μ) σ ω ∂μ =
      ∫ ω in s, martingalePart f ℱ μ N ω ∂μ := by
    rw [setIntegral_congr_ae (hσ.measurableSpace_le _ hs)
      ((hM.stoppedValue_ae_eq_condExp_of_le_const hσ hσN).mono fun _ h _ ↦ h)]
    exact setIntegral_condExp hσ.measurableSpace_le (hM.integrable N) hs
  have hdec (n : ℕ) (ω : Ω) :
      predictablePart f ℱ μ n ω = f n ω - martingalePart f ℱ μ n ω := by
    rw [predictablePart_eq_sub, Pi.sub_apply]
  have hpt (ω : Ω) :
      predictablePart f ℱ μ N ω - stoppedValue (predictablePart f ℱ μ) σ ω =
        (f N ω - stoppedValue f σ ω) -
          (martingalePart f ℱ μ N ω - stoppedValue (martingalePart f ℱ μ) σ ω) := by
    simp only [stoppedValue, hdec]
    abel
  have hfσ := integrable_stoppedValue ℕ hσ hint hσN
  have hMσi := integrable_stoppedValue ℕ hσ (integrable_martingalePart (ℱ := ℱ) hint) hσN
  simp_rw [hpt]
  rw [integral_sub ((hint N).sub' hfσ).integrableOn
      ((integrable_martingalePart hint N).sub' hMσi).integrableOn,
    integral_sub (integrable_martingalePart hint N).integrableOn hMσi.integrableOn, hMσ,
    sub_self, sub_zero]

end NormedSpace

variable {f : ℕ → Ω → ℝ}

/-- The first index `k ≤ N` at which the compensator at `k + 1` reaches `c`, or `N` if there is
none. The compensator at `k + 1` is known at `k`, so this is a stopping time. -/
private noncomputable def compensatorHit (f : ℕ → Ω → ℝ) (ℱ : Filtration ℕ m0) (μ : Measure Ω)
    (c : ℝ) (N : ℕ) (ω : Ω) : WithTop ℕ :=
  (hittingBtwn (fun k ↦ predictablePart f ℱ μ (k + 1)) (Ici c) 0 N ω : ℕ)

private theorem isStoppingTime_compensatorHit (c : ℝ) (N : ℕ) :
    IsStoppingTime ℱ (compensatorHit f ℱ μ c N) :=
  Adapted.isStoppingTime_hittingBtwn (fun k ↦ (stronglyAdapted_predictablePart k).measurable)
    measurableSet_Ici

private theorem compensatorHit_le (c : ℝ) (N : ℕ) (ω : Ω) : compensatorHit f ℱ μ c N ω ≤ N :=
  WithTop.coe_le_coe.2 (hittingBtwn_le ω)

private theorem compensatorHit_lt_iff {c : ℝ} {N : ℕ} {ω : Ω} :
    compensatorHit f ℱ μ c N ω < N ↔ ∃ j < N, c ≤ predictablePart f ℱ μ (j + 1) ω := by
  simp [compensatorHit, hittingBtwn_lt_iff N le_rfl]

/-- Before the hit, the compensator stays below the level. -/
private theorem stoppedValue_compensatorHit_lt {c : ℝ} (hc : 0 < c) (N : ℕ) (ω : Ω) :
    stoppedValue (predictablePart f ℱ μ) (compensatorHit f ℱ μ c N) ω < c := by
  simp only [stoppedValue, compensatorHit, WithTop.untopA, Nat.cast_withTop, WithTop.untopD_coe]
  rcases h : hittingBtwn (fun k ↦ predictablePart f ℱ μ (k + 1)) (Ici c) 0 N ω with _ | i
  · simpa [predictablePart_zero] using hc
  · have hi : i < hittingBtwn (fun k ↦ predictablePart f ℱ μ (k + 1)) (Ici c) 0 N ω := by
      rw [h]
      exact Nat.lt_succ_self i
    simpa using notMem_of_lt_hittingBtwn hi (Nat.zero_le i)

private theorem subset_compensatorHit_lt {c : ℝ} (hc : 0 < c) (N : ℕ) :
    {ω | c ≤ predictablePart f ℱ μ N ω} ⊆ {ω | compensatorHit f ℱ μ c N ω < N} := by
  intro ω hω
  rcases N with _ | n
  · simp only [predictablePart_zero, mem_ofPred_eq, Pi.zero_apply] at hω
    linarith
  · exact compensatorHit_lt_iff.2 ⟨n, Nat.lt_succ_self n, hω⟩

private theorem ae_le_of_compensatorHit_lt (hf : Submartingale f ℱ μ) (c : ℝ) (N : ℕ) :
    ∀ᵐ ω ∂μ, compensatorHit f ℱ μ c N ω < N → c ≤ predictablePart f ℱ μ N ω := by
  filter_upwards [hf.monotone_predictablePart] with ω hmono h
  obtain ⟨j, hj, hcj⟩ := compensatorHit_lt_iff.1 h
  exact hcj.trans (hmono (by omega : j + 1 ≤ N))

private theorem compensatorHit_lt_ae_eq (hf : Submartingale f ℱ μ) {c : ℝ} (hc : 0 < c)
    (N : ℕ) :
    {ω | compensatorHit f ℱ μ c N ω < N} =ᵐ[μ] {ω | c ≤ predictablePart f ℱ μ N ω} := by
  filter_upwards [ae_le_of_compensatorHit_lt hf c N] with ω h
  exact ⟨h, fun h' ↦ subset_compensatorHit_lt hc N h'⟩

/-- Between the hit of level `c` and `N`, the compensator exceeds `c` by at most the average
increment of the submartingale. -/
private theorem setIntegral_predictablePart_sub_le [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) {c : ℝ} (hc : 0 < c) (N : ℕ) :
    ∫ ω in {ω | compensatorHit f ℱ μ c N ω < N}, (predictablePart f ℱ μ N ω - c) ∂μ ≤
      ∫ ω in {ω | compensatorHit f ℱ μ c N ω < N},
        (f N ω - stoppedValue f (compensatorHit f ℱ μ c N) ω) ∂μ := by
  have hσ := isStoppingTime_compensatorHit (f := f) (ℱ := ℱ) (μ := μ) c N
  rw [← setIntegral_predictablePart_sub_stoppedValue hf.stronglyAdapted hf.integrable hσ
    (compensatorHit_le c N) (s := {ω | compensatorHit f ℱ μ c N ω < N})
    (hσ.measurableSet_lt_of_countable' N)]
  refine integral_mono ((integrable_predictablePart hf.integrable N).sub
    (integrable_const c)).integrableOn
    ((integrable_predictablePart hf.integrable N).sub
      (integrable_stoppedValue ℕ hσ (integrable_predictablePart hf.integrable)
        (compensatorHit_le c N))).integrableOn fun ω ↦ ?_
  exact sub_le_sub_left (stoppedValue_compensatorHit_lt hc N ω).le _

/-- On the event that the compensator reaches `c` before `N`, its value at `N` is almost
everywhere at least `c`. -/
private theorem ae_restrict_sub_nonneg (hf : Submartingale f ℱ μ) (c : ℝ) (N : ℕ) :
    0 ≤ᵐ[μ.restrict {ω | compensatorHit f ℱ μ c N ω < N}]
      fun ω ↦ predictablePart f ℱ μ N ω - c := by
  have hσ := isStoppingTime_compensatorHit (f := f) (ℱ := ℱ) (μ := μ) c N
  have hs : MeasurableSet {ω | compensatorHit f ℱ μ c N ω < N} :=
    hσ.measurableSpace_le _ (hσ.measurableSet_lt_of_countable' N)
  rw [EventuallyLE, ae_restrict_iff' hs]
  filter_upwards [ae_le_of_compensatorHit_lt hf c N] with ω h hω
  simpa using h hω

/-- **Tail bound for the discrete Doob compensator.** For a submartingale `f` with compensator
`A = predictablePart f ℱ μ` and a level `c > 0`, there are stopping times `σ, ρ ≤ N` with
`∫_{c ≤ A_N} A_N ≤ ∫_{σ < N} (f_N - f_σ) + 2 ∫_{ρ < N} (f_N - f_ρ)`, where
`c P(σ < N) ≤ E[f_N - f_0]` and `c P(ρ < N) ≤ 2 E[f_N - f_0]`. -/
theorem Submartingale.exists_setIntegral_predictablePart_le [IsFiniteMeasure μ]
    (hf : Submartingale f ℱ μ) (N : ℕ) {c : ℝ} (hc : 0 < c) :
    ∃ σ ρ : Ω → WithTop ℕ, IsStoppingTime ℱ σ ∧ IsStoppingTime ℱ ρ ∧
      (∀ ω, σ ω ≤ N) ∧ (∀ ω, ρ ω ≤ N) ∧
      c * μ.real {ω | σ ω < N} ≤ ∫ ω, (f N ω - f 0 ω) ∂μ ∧
      c * μ.real {ω | ρ ω < N} ≤ 2 * ∫ ω, (f N ω - f 0 ω) ∂μ ∧
      ∫ ω in {ω | c ≤ predictablePart f ℱ μ N ω}, predictablePart f ℱ μ N ω ∂μ ≤
        ∫ ω in {ω | σ ω < N}, (f N ω - stoppedValue f σ ω) ∂μ +
          2 * ∫ ω in {ω | ρ ω < N}, (f N ω - stoppedValue f ρ ω) ∂μ := by
  have hc2 : 0 < c / 2 := half_pos hc
  set A := predictablePart f ℱ μ N
  have hAint : Integrable A μ := integrable_predictablePart hf.integrable N
  have hAnn : 0 ≤ᵐ[μ] A := by
    filter_upwards [hf.predictablePart_nonneg] with ω h
    exact h N
  have hAmeas : Measurable A :=
    ((stronglyAdapted_predictablePart' N).mono (ℱ.le N)).measurable
  have hEA : ∫ ω, A ω ∂μ = ∫ ω, (f N ω - f 0 ω) ∂μ := by
    rw [integral_predictablePart hf.integrable,
      integral_sub (hf.integrable N) (hf.integrable 0)]
  set S := {ω | c ≤ A ω}
  have hS : MeasurableSet S := measurableSet_le measurable_const hAmeas
  have hSρ : S ⊆ {ω | compensatorHit f ℱ μ (c / 2) N ω < N} := fun ω hω ↦ by
    have hcA : c ≤ A ω := hω
    exact subset_compensatorHit_lt hc2 N (show c / 2 ≤ A ω by linarith)
  refine ⟨compensatorHit f ℱ μ c N, compensatorHit f ℱ μ (c / 2) N,
    isStoppingTime_compensatorHit c N, isStoppingTime_compensatorHit (c / 2) N,
    compensatorHit_le c N, compensatorHit_le (c / 2) N, ?_, ?_, ?_⟩
  · rw [measureReal_congr (compensatorHit_lt_ae_eq hf hc N), ← hEA]
    exact mul_meas_ge_le_integral_of_nonneg hAnn hAint c
  · have h := mul_meas_ge_le_integral_of_nonneg hAnn hAint (c / 2)
    rw [← measureReal_congr (compensatorHit_lt_ae_eq hf hc2 N), hEA] at h
    linarith
  -- Split off the level, then compare each piece with an increment of `f` after a hit.
  have hsplit : ∫ ω in S, A ω ∂μ = ∫ ω in S, (A ω - c) ∂μ + c * μ.real S := by
    rw [integral_sub hAint.integrableOn (integrable_const c).integrableOn, setIntegral_const,
      smul_eq_mul, mul_comm]
    ring
  have hlevel : ∫ ω in S, (A ω - c) ∂μ ≤
      ∫ ω in {ω | compensatorHit f ℱ μ c N ω < N}, (A ω - c) ∂μ :=
    setIntegral_mono_set (hAint.sub (integrable_const c)).integrableOn
      (ae_restrict_sub_nonneg hf c N)
      (ae_of_all _ fun _ h ↦ subset_compensatorHit_lt hc N h)
  have hhalf : c / 2 * μ.real S ≤
      ∫ ω in {ω | compensatorHit f ℱ μ (c / 2) N ω < N}, (A ω - c / 2) ∂μ := by
    calc c / 2 * μ.real S = ∫ ω in S, c / 2 ∂μ := by rw [setIntegral_const, smul_eq_mul, mul_comm]
      _ ≤ ∫ ω in S, (A ω - c / 2) ∂μ := setIntegral_mono_on (integrable_const _).integrableOn
          (hAint.sub (integrable_const _)).integrableOn hS fun ω hω ↦ by
            simp only [S, mem_ofPred_eq] at hω
            linarith
      _ ≤ _ := setIntegral_mono_set (hAint.sub (integrable_const _)).integrableOn
          (ae_restrict_sub_nonneg hf (c / 2) N) (ae_of_all _ fun _ h ↦ hSρ h)
  have h1 := setIntegral_predictablePart_sub_le hf hc N
  have h2 := setIntegral_predictablePart_sub_le hf hc2 N
  linarith [hsplit, hlevel, hhalf, h1, h2]

end MeasureTheory
