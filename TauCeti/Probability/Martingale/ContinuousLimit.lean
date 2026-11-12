/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Martingale.LpLimit
public import TauCeti.Probability.Martingale.UniformApproximation
public import TauCeti.Probability.Process.UniformLimit
public import TauCeti.Probability.Process.Predictable.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Continuous martingale completion on raw filtrations

Continuous martingale approximants which are Cauchy in Lᵖ at each date, for
`1 ≤ p ≤ ∞`, admit a predictable continuous martingale limit. Convergence is in Lᵖ
at each date and uniformly in probability on each finite horizon. A single
subsequence converges almost surely uniformly on every finite horizon. Continuity always
means continuity outside one common null set; the selected process need not be continuous
on exceptional paths.

This combines fixed-time Lᵖ completion with weak maximal estimates and continuous
adapted limit selection. In particular, it supplies the continuous-process completion
step for elementary stochastic integrals without assuming usual filtration conditions
or identifying separate-time versions with indistinguishable processes.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second
  edition, Springer, 1991, §3.2.B.
-/

public section

noncomputable section

open Filter Set
open scoped Topology ENNReal NNReal

namespace MeasureTheory

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [IsFiniteMeasure μ]

variable {ℱ : Filtration ℝ≥0 mΩ} {M : ℕ → ℝ≥0 → Ω → E}

/-- Continuous martingales with fixed-time Lᵖ-Cauchy values have a predictable martingale
limit with almost surely continuous paths, fixed-time Lᵖ convergence, and uniform
convergence in outer probability on each finite horizon. One subsequence
converges uniformly on every finite horizon outside a single null set. This includes
`p = 1` and `p = ∞`, and requires neither completeness nor right continuity of the filtration. -/
theorem exists_continuous_martingale_of_cauchySeq_Lp {p : ℝ≥0∞} [hp : Fact (1 ≤ p)]
    (hM : ∀ n, Martingale (M n) ℱ μ)
    (hc : ∀ n, ∀ᵐ ω ∂μ, Continuous (fun t ↦ M n t ω))
    (hmem : ∀ n t, MemLp (M n t) p μ)
    (hcau : ∀ t, CauchySeq (fun n ↦ (hmem n t).toLp (M n t))) :
    ∃ Y : ℝ≥0 → Ω → E, Martingale Y ℱ μ ∧ IsStronglyPredictable ℱ Y ∧
      (∀ t, MemLp (Y t) p μ ∧
        Tendsto (fun n ↦ eLpNorm (M n t - Y t) p μ) atTop (𝓝 0)) ∧
      (∀ (T : ℝ≥0) (ε : ℝ≥0), 0 < ε →
        Tendsto (fun n ↦ μ {ω | ∃ t ≤ T, (ε : ℝ) < ‖M n t ω - Y t ω‖}) atTop (𝓝 0)) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂μ,
        Continuous (fun t ↦ Y t ω) ∧ ∀ T : ℝ≥0,
          TendstoUniformlyOn (fun n t ↦ M (φ n) t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
  -- First construct the fixed-time limit, then extract summably small path increments.
  obtain ⟨Z, hZ, hZlim⟩ := exists_martingale_of_cauchySeq_Lp hM hmem hcau
  have hL1 (t : ℝ≥0) : Tendsto (fun n ↦ eLpNorm (M n t - Z t) 1 μ) atTop (𝓝 0) :=
    TauCeti.MeasureTheory.tendsto_eLpNorm_one_of_tendsto_eLpNorm hp.out (hZlim t).2
  have hcau₁ (k : ℕ) : CauchySeq (fun n ↦ ((hM n).integrable (k : ℝ≥0)).toL1 (M n k)) := by
    apply Tendsto.cauchySeq (x := (hZ.integrable (k : ℝ≥0)).toL1 (Z k))
    exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
      (fun n ↦ memLp_one_iff_integrable.mpr ((hM n).integrable (k : ℝ≥0))) _
      (memLp_one_iff_integrable.mpr (hZ.integrable (k : ℝ≥0)))).2 (hL1 k)
  obtain ⟨φ, hφ, -, hsum⟩ := exists_strictMono_summable_uniform_errors hM
    (fun n ↦ (hc n).mono fun ω hω t ↦ hω.continuousAt.continuousWithinAt) hcau₁
  have hgeom : Summable (fun n : ℕ ↦ (2 : ℝ)⁻¹ ^ n) :=
    summable_geometric_of_abs_lt_one (by norm_num)
  have hmeasure (t : ℝ≥0) : TendstoInMeasure μ (fun n ↦ M (φ n) t) atTop (Z t) :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0)
      (hL1 t)).comp hφ.tendsto_atTop
  -- Select on the raw filtration before replacing the limit by a predictable version.
  obtain ⟨U, hU, hUZ, hUlim⟩ :=
    TauCeti.Probability.exists_continuous_stronglyAdapted_version_of_summable
      (fun n ↦ (hM (φ n)).stronglyAdapted) (fun n ↦ hc (φ n)) hgeom
      (fun T ↦ (hsum T).ne) hmeasure
  obtain ⟨Y, hY, hYU⟩ :=
    hU.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hUlim.mono fun ω hω ↦ hω.1.isLeftContinuous)
  have hYZ (t : ℝ≥0) : Y t =ᵐ[μ] Z t := (hYU.ae_eq_eval t).trans (hUZ t)
  have hYm : Martingale Y ℱ μ := hZ.congr hY.isStronglyProgressive.stronglyAdapted
    (fun t ↦ (hYZ t).symm)
  have hpath : ∀ᵐ ω ∂μ, Continuous (fun t ↦ Y t ω) ∧ ∀ T : ℝ≥0,
      TendstoUniformlyOn (fun n t ↦ M (φ n) t ω) (fun t ↦ Y t ω) atTop (Iic T) := by
    filter_upwards [hYU, hUlim] with ω hω hlim
    have heq : (fun t ↦ Y t ω) = fun t ↦ U t ω := funext hω
    simpa only [heq] using hlim
  refine ⟨Y, hYm, hY, fun t ↦ ?_, ?_, φ, hφ, hpath⟩
  · refine ⟨(hZlim t).1.ae_eq (hYZ t).symm, ?_⟩
    have heq (n : ℕ) : eLpNorm (M n t - Y t) p μ = eLpNorm (M n t - Z t) p μ :=
      eLpNorm_congr_ae (EventuallyEq.sub (EventuallyEq.rfl) (hYZ t))
    simpa only [heq] using (hZlim t).2
  · intro T ε hε
    apply hYm.tendsto_measure_exists_le_norm_sub_lt hM
      (hpath.mono fun ω hω t _ ↦ hω.1.continuousAt.continuousWithinAt)
      (fun n ↦ (hc n).mono fun ω hω t _ ↦ hω.continuousAt.continuousWithinAt) _ hε
    have heq (n : ℕ) : eLpNorm (M n T - Y T) 1 μ = eLpNorm (M n T - Z T) 1 μ :=
      eLpNorm_congr_ae (EventuallyEq.sub EventuallyEq.rfl (hYZ T))
    simpa only [heq] using hL1 T

end MeasureTheory
