/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
public import TauCeti.Statistics.Convergence.BoundedInProbability
import TauCeti.MeasureTheory.Function.ConvergenceInMeasure
import TauCeti.MeasureTheory.Function.TendstoInDistribution

/-!
# The delta method

If a sequence of estimators `Tₙ` satisfies `aₙ (Tₙ - θ) = O_P(1)` for a diverging rate `aₙ → ∞`
and `g : E → F` is Fréchet differentiable at `θ` with derivative `D`, then `Tₙ → θ` in
probability and the linearization remainder `aₙ (g (Tₙ) - g θ) - D (aₙ (Tₙ - θ))` tends to `0` in
probability. When `aₙ (Tₙ - θ) → Z` in distribution, Slutsky's replacement lemma yields
`aₙ (g (Tₙ) - g θ) → D Z` in distribution, with the `aₙ = √n` case giving the classical delta
method.

## Main statements

* `TauCeti.tendstoInMeasure_const_of_isBoundedInProbability_smul_sub` — `aₙ (Tₙ - θ) = O_P(1)`
  with `aₙ → ∞` implies `Tₙ → θ` in probability.
* `TauCeti.tendstoInMeasure_delta_method_remainder` — the linearization remainder
  `aₙ • (g (Tₙ) - g θ) - D (aₙ • (Tₙ - θ))` converges to `0` in probability whenever
  `aₙ • (Tₙ - θ)` is bounded in probability, with no measurability assumptions.
* `TauCeti.tendstoInDistribution_of_hasFDerivAt` — general-rate delta method in seminormed real
  vector spaces without second-countability assumptions.
* `TauCeti.tendstoInDistribution_delta_method` — the classical `√n`-rate delta method.

## References

* A. W. van der Vaart, *Asymptotic Statistics*, Cambridge University Press, 1998, Theorem 3.1,
  p. 26.
-/

public section

noncomputable section

open Filter MeasureTheory
open scoped Topology

namespace TauCeti

variable {Ω E F : Type*} [MeasurableSpace Ω]
  [SeminormedAddCommGroup E] [NormedSpace ℝ E]

/-- If `aₙ • (Tₙ - θ)` is bounded in probability for a diverging sequence `aₙ → ∞`, then `Tₙ → θ`
in probability, under any finite measure and without measurability assumptions. -/
theorem tendstoInMeasure_const_of_isBoundedInProbability_smul_sub
    {μ : Measure Ω} [IsFiniteMeasure μ] {a : ℕ → ℝ} {T : ℕ → Ω → E} {θ : E}
    (ha : Tendsto a atTop atTop)
    (hbd : IsBoundedInProbability μ (fun n ω ↦ a n • (T n ω - θ))) :
    TendstoInMeasure μ T atTop (fun _ ↦ θ) := by
  have hinv : TendstoInMeasure μ (fun n _ ↦ (a n)⁻¹) atTop (fun _ ↦ (0 : ℝ)) :=
    (tendsto_inv_atTop_zero.comp ha).tendstoInMeasure_const
  have hprod := tendstoInMeasure_smul_zero_of_tendstoInMeasure_zero hinv hbd
  rw [tendstoInMeasure_iff_norm] at hprod ⊢
  intro ε hε
  refine (hprod ε hε).congr' ?_
  filter_upwards [ha.eventually_gt_atTop 0] with n hn
  congr 1
  ext ω
  simp [inv_smul_smul₀ hn.ne']

/-- **Delta method remainder bound.** If `aₙ • (Tₙ - θ)` is bounded in probability for a diverging
sequence `aₙ → ∞` and `g : E → F` is Fréchet differentiable at `θ` with derivative `D`, then the
linearization remainder `aₙ • (g (Tₙ) - g θ) - D (aₙ • (Tₙ - θ))` converges to `0` in probability,
under any finite measure and without measurability assumptions. -/
theorem tendstoInMeasure_delta_method_remainder
    [SeminormedAddCommGroup F] [NormedSpace ℝ F]
    {μ : Measure Ω} [IsFiniteMeasure μ]
    {a : ℕ → ℝ} {T : ℕ → Ω → E} {θ : E} {g : E → F} {D : E →L[ℝ] F}
    (ha : Tendsto a atTop atTop)
    (hbd : IsBoundedInProbability μ (fun n ω ↦ a n • (T n ω - θ)))
    (hd : HasFDerivAt g D θ) :
    TendstoInMeasure μ
      (fun n ω ↦ a n • (g (T n ω) - g θ) - D (a n • (T n ω - θ)))
      atTop (fun _ ↦ 0) := by
  have hT := tendstoInMeasure_const_of_isBoundedInProbability_smul_sub ha hbd
  let r : E → ℝ := fun x ↦ ‖g x - g θ - D (x - θ)‖ / ‖x - θ‖
  have hr_cont : ContinuousAt r θ := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    obtain ⟨δ, hδ, hlip⟩ :=
      Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hd.isLittleO (half_pos hε))
    refine ⟨δ, hδ, fun {x} hx ↦ ?_⟩
    have hrθ : r θ = 0 := by simp [r]
    rw [hrθ, Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _))]
    by_cases h0 : ‖x - θ‖ = 0
    · simp [h0, hε]
    · have hpos : 0 < ‖x - θ‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      exact ((div_le_iff₀ hpos).2 (hlip hx)).trans_lt (half_lt_self hε)
  have hr_lim : TendstoInMeasure μ (fun n ω ↦ r (T n ω)) atTop (fun _ ↦ 0) := by
    simpa [r] using hT.continuousAt_const_comp hr_cont
  have hprod := tendstoInMeasure_smul_zero_of_tendstoInMeasure_zero hr_lim hbd
  obtain ⟨δ, hδ, hlip⟩ :=
    Metric.eventually_nhds_iff.1 (Asymptotics.isLittleO_iff.1 hd.isLittleO zero_lt_one)
  refine hprod.zero_of_norm_le_on (A := fun n ↦ {ω | dist (T n ω) θ < δ}) ?_ ?_
  · simpa only [Set.compl_ofPred, not_lt] using tendstoInMeasure_iff_dist.1 hT δ hδ
  · filter_upwards [ha.eventually_ge_atTop 0] with n hn ω hω
    rw [map_smul, ← smul_sub, norm_smul, Real.norm_of_nonneg hn,
      norm_smul, norm_smul, Real.norm_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)),
      Real.norm_of_nonneg hn]
    by_cases h0 : ‖T n ω - θ‖ = 0
    · have hzero : ‖g (T n ω) - g θ - D (T n ω - θ)‖ ≤ 0 := by
        simpa [h0] using hlip (Set.mem_ofPred_eq.mp hω)
      have hzero' : ‖g (T n ω) - g θ - D (T n ω - θ)‖ = 0 := le_antisymm hzero (norm_nonneg _)
      rw [hzero', h0, mul_zero]
      norm_num
    · exact le_of_eq (by field_simp)

/-- **General-rate delta method.** If `aₙ • (Tₙ - θ) → Z` in distribution for a diverging sequence
`aₙ → ∞` and `g : E → F` is Fréchet differentiable at `θ` with derivative `D`, with each `g ∘ Tₙ`
almost-everywhere measurable, then `aₙ • (g (Tₙ) - g θ) → D ∘ Z` in distribution. Neither
second countability nor `BorelSpace E` is required. -/
theorem tendstoInDistribution_of_hasFDerivAt
    {Ω' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {a : ℕ → ℝ} {T : ℕ → Ω → E} {θ : E} {Z : Ω' → E} {g : E → F} {D : E →L[ℝ] F}
    (ha : Tendsto a atTop atTop)
    (hlim : TendstoInDistribution (fun n ω ↦ a n • (T n ω - θ)) atTop Z (fun _ ↦ μ) μ')
    (hgT : ∀ n, AEMeasurable (fun ω ↦ g (T n ω)) μ)
    (hd : HasFDerivAt g D θ) :
    TendstoInDistribution (fun n ω ↦ a n • (g (T n ω) - g θ)) atTop (D ∘ Z) (fun _ ↦ μ) μ' := by
  have hbd := isBoundedInProbability_of_tendstoInDistribution hlim
  have hrem := tendstoInMeasure_delta_method_remainder ha hbd hd
  have hlin := hlim.continuous_comp D.continuous
  have hmeas : ∀ n, AEMeasurable (fun ω ↦ a n • (g (T n ω) - g θ)) μ := fun n ↦
    ((continuous_const_smul (a n)).comp
      (continuous_sub_right (g θ))).measurable.comp_aemeasurable (hgT n)
  exact hlin.congr_of_tendstoInMeasure_sub hmeas hrem

/-- **The delta method** at the classical `√n` rate. If `√n • (Tₙ - θ) → Z` in distribution and
`g : E → F` is Fréchet differentiable at `θ` with derivative `D`, with each `g ∘ Tₙ`
almost-everywhere measurable, then `√n • (g (Tₙ) - g θ) → D ∘ Z` in distribution. -/
theorem tendstoInDistribution_delta_method
    {Ω' : Type*} [MeasurableSpace Ω']
    [MeasurableSpace E] [OpensMeasurableSpace E]
    [SeminormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {μ' : Measure Ω'} [IsProbabilityMeasure μ']
    {T : ℕ → Ω → E} {θ : E} {Z : Ω' → E} {g : E → F} {D : E →L[ℝ] F}
    (hlim : TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (T n ω - θ)) atTop Z
      (fun _ ↦ μ) μ')
    (hgT : ∀ n, AEMeasurable (fun ω ↦ g (T n ω)) μ)
    (hd : HasFDerivAt g D θ) :
    TendstoInDistribution (fun (n : ℕ) ω ↦ √(n : ℝ) • (g (T n ω) - g θ)) atTop (D ∘ Z)
      (fun _ ↦ μ) μ' :=
  tendstoInDistribution_of_hasFDerivAt
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop) hlim hgT hd

end TauCeti
