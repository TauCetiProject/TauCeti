/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.Gamma.Cdf
public import TauCeti.Probability.Process.Poisson.Regularization
import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import TauCeti.Probability.Distributions.Poisson.Tail
import TauCeti.Probability.Process.HittingTime.Countable
import TauCeti.Probability.Process.LevelLocalizer

/-!
# Arrival times and gamma laws for filtered Poisson processes

For a natural-valued counting process `M : ℝ≥0 → Ω → ℕ` whose real cast is a homogeneous Poisson
process of rate `α` relative to `ℱ`:

* when every sample path of `M` is right-continuous (for instance, when every path is a simple
  counting path), the arrival time `hittingAfter M (Set.Ici c) 0` is a stopping time on the raw
  filtration `ℱ` (`isStoppingTime_hittingAfter_Ici`);
* assuming only almost-sure right-continuity `∀ᵐ ω ∂P, IsRightContinuous (M · ω)`,
  `hittingAfter M (Set.Ici c) 0` is `P`-almost everywhere measurable
  (`aemeasurable_hittingAfter_Ici`) and for `c ≠ 0` satisfies the Poisson–gamma duality
  `P.real {ω | hittingAfter M (Set.Ici c) 0 ω ≤ t} = regularizedGamma c (α * t)`
  (`measureReal_hittingAfter_Ici_le`);
* for `0 < α` every arrival time `hittingAfter M (Set.Ici c) 0` is almost surely finite without any
  pathwise hypothesis (`hittingAfter_Ici_ae_ne_top`), whereas at rate `α = 0` under almost-sure
  right-continuity every positive arrival time (`c ≠ 0`) is almost surely `⊤`
  (`hittingAfter_Ici_ae_eq_top`);
* when `0 < α`, `c ≠ 0`, and `M` is almost surely right-continuous,
  `((hittingAfter M (Set.Ici c) 0 ω).untopA : ℝ)` has law `gammaMeasure c α`
  (`hasLaw_untopA_hittingAfter_Ici_gammaMeasure`), and in particular `expMeasure α` at `c = 1`
  (`hasLaw_untopA_hittingAfter_Ici_one_expMeasure`).

## References

* P. E. Protter, *Stochastic Integration and Differential Equations*, second edition, Springer,
  2005, Chapter I, §3.
* J. F. C. Kingman, *Poisson Processes*, Oxford University Press, 1993, §4.1.
-/

public section

open Filter MeasureTheory ProbabilityTheory Real Set
open scoped NNReal ENNReal Topology

namespace TauCeti.Probability.IsFilteredPoissonProcess

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {α : ℝ≥0} {M : ℝ≥0 → Ω → ℕ} {P : Measure Ω}

/-- When every sample path of `M` is right-continuous, the `c`-th arrival time is a stopping time
on the raw filtration `ℱ`. Monotonicity is not needed because `Ici c` is clopen in `ℕ` and `ℝ≥0` is
densely ordered and separable. -/
theorem isStoppingTime_hittingAfter_Ici
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ ω, IsRightContinuous (M · ω)) (c : ℕ) :
    IsStoppingTime ℱ (hittingAfter M (Ici c) 0) :=
  h.adapted_nat.isStoppingTime_hittingAfter_of_isClopen_of_isRightContinuous hrc
    (isClopen_discrete (Ici c)) 0

/-- Under almost-sure right-continuity of `M`, the arrival time `hittingAfter M (Set.Ici c) 0` is
`P`-almost everywhere measurable. -/
theorem aemeasurable_hittingAfter_Ici
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (c : ℕ) :
    AEMeasurable (hittingAfter M (Ici c) 0) P :=
  aemeasurable_hittingAfter_of_isOpen_of_isRightContinuous
    (fun t ↦ (h.measurable_eval_nat t).aemeasurable) hrc (isOpen_discrete (Ici c)) 0

/-- **Poisson–gamma arrival-time duality.** For an almost-surely right-continuous natural-valued
filtered Poisson process of rate `α`, the `c`-th arrival (`c ≠ 0`) occurs by time `t` with
probability `regularizedGamma c (α * t)`. -/
theorem measureReal_hittingAfter_Ici_le
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) {c : ℕ} (hc : c ≠ 0) (t : ℝ≥0) :
    P.real {ω | hittingAfter M (Ici c) 0 ω ≤ t} = regularizedGamma c (α * t) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hc
  rw [Nat.succ_eq_add_one]
  have hae : ({ω | hittingAfter M (Ici (k + 1)) 0 ω ≤ t} : Set Ω) =ᵐ[P] {ω | k < M t ω} := by
    filter_upwards [h.ae_monotone_of_isRightContinuous hrc, hrc] with ω hmonoω hrcω
    simp only [hmonoω.hittingAfter_Ici_le_iff
      (isRightContinuous_iff_continuousWithinAt_Ici.mp hrcω), zero_le, true_and]
    omega
  rw [measureReal_congr hae]
  simpa only [Nat.cast_add, Nat.cast_one, NNReal.coe_mul] using
    measureReal_lt_of_hasLaw_poissonMeasure (h.hasLaw_eval_nat t) k

/-- For an almost-surely right-continuous natural-valued filtered Poisson process of rate `0`,
every positive arrival time (`c ≠ 0`) is almost surely `⊤`. -/
theorem hittingAfter_Ici_ae_eq_top
    (h : IsFilteredPoissonProcess ℱ 0 (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) {c : ℕ} (hc : c ≠ 0) :
    ∀ᵐ ω ∂P, hittingAfter M (Ici c) 0 ω = ⊤ := by
  have hall : ∀ᵐ ω ∂P, ∀ n : ℕ, (M n ω : ℝ) = 0 :=
    ae_all_iff.mpr fun n ↦ h.eval_ae_eq_zero n
  filter_upwards [h.ae_monotone_of_isRightContinuous hrc, hall] with ω hmono hzero
  rw [hittingAfter_eq_top_iff]
  intro t _ ht
  obtain ⟨n, htn⟩ := exists_nat_gt t
  have hn0 : M n ω = 0 := Nat.cast_eq_zero.mp (hzero n)
  have ht0 : M t ω = 0 := Nat.eq_zero_of_le_zero ((hmono htn.le).trans_eq hn0)
  exact hc (Nat.eq_zero_of_le_zero (ht0 ▸ ht))

/-- At positive rate `0 < α`, every arrival time `hittingAfter M (Set.Ici c) 0` is almost surely
finite, without any pathwise regularity assumption. For `c ≠ 0`, this fails at `α = 0` by
`hittingAfter_Ici_ae_eq_top`. -/
theorem hittingAfter_Ici_ae_ne_top
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hα : 0 < α) (c : ℕ) :
    ∀ᵐ ω ∂P, hittingAfter M (Ici c) 0 ω ≠ ⊤ := by
  have := h.isProbabilityMeasure
  let B : ℕ → Set Ω := fun n ↦ {ω | M n ω ≤ c}
  have hlim : Tendsto (fun n : ℕ ↦ P.real (B n)) atTop (𝓝 0) := by
    have hBn (n : ℕ) : P.real (B n) = 1 - regularizedGamma (c + 1) ((α : ℝ) * n) := by
      simpa only [B, NNReal.coe_mul, NNReal.coe_natCast] using
        measureReal_le_of_hasLaw_poissonMeasure (h.hasLaw_eval_nat n) c
    simp_rw [hBn]
    have hscale : Tendsto (fun n : ℕ ↦ (α : ℝ) * n) atTop atTop :=
      Tendsto.const_mul_atTop (NNReal.coe_pos.mpr hα) tendsto_natCast_atTop_atTop
    have hsub := (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_regularizedGamma_atTop (by positivity : (0 : ℝ) < c + 1)).comp hscale)
    simpa only [Function.comp_def, sub_self] using hsub
  have hnull : P (⋂ n : ℕ, B n) = 0 := by
    rw [← measureReal_eq_zero_iff]
    refine le_antisymm (ge_of_tendsto hlim (Eventually.of_forall fun n ↦ ?_)) measureReal_nonneg
    exact measureReal_mono (iInter_subset B n)
  have hae : ∀ᵐ ω ∂P, ω ∉ ⋂ n : ℕ, B n := by
    rw [ae_iff]
    simpa only [Classical.not_not, ofPred_mem_eq] using hnull
  filter_upwards [hae] with ω hnot htop
  exact hnot (mem_iInter.mpr fun n ↦ not_lt.mp fun hlt : c < M n ω ↦
    WithTop.coe_ne_top
      (top_unique (htop ▸ hittingAfter_le_of_mem (zero_le : (0 : ℝ≥0) ≤ n) hlt.le)))

/-- **Gamma law of the `c`-th arrival time.** For an almost-surely right-continuous natural-valued
filtered Poisson process of positive rate `0 < α` and any nonzero level `c ≠ 0`, the real-valued
arrival time `((hittingAfter M (Set.Ici c) 0 ω).untopA : ℝ)` has law `gammaMeasure c α`. -/
theorem hasLaw_untopA_hittingAfter_Ici_gammaMeasure
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (hα : 0 < α) {c : ℕ} (hc : c ≠ 0) :
    HasLaw (fun ω ↦ ((hittingAfter M (Ici c) 0 ω).untopA : ℝ))
      (gammaMeasure c α) P := by
  have := h.isProbabilityMeasure
  let Y : Ω → ℝ := fun ω ↦ ((hittingAfter M (Ici c) 0 ω).untopA : ℝ)
  have hY : AEMeasurable Y P :=
    (NNReal.continuous_coe.measurable.comp WithTop.measurable_untopA).comp_aemeasurable
      (h.aemeasurable_hittingAfter_Ici hrc c)
  have hshape : (0 : ℝ) < (c : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hc)
  have hrate : (0 : ℝ) < (α : ℝ) := NNReal.coe_pos.mpr hα
  have : IsProbabilityMeasure (gammaMeasure c α) :=
    isProbabilityMeasure_gammaMeasure hshape hrate
  refine ⟨hY, Measure.eq_of_cdf (P.map Y) (gammaMeasure c α)
    (StieltjesFunction.ext fun x ↦ ?_)⟩
  rw [Measure.cdf_map P Y hY x, cdf_gammaMeasure_eq hshape hrate x]
  rcases lt_or_ge x 0 with hx | hx
  · have hemp : Y ⁻¹' Iic x = ∅ :=
      eq_empty_of_forall_notMem fun ω hω ↦ hx.not_ge ((NNReal.coe_nonneg _).trans hω)
    rw [hemp, measureReal_empty, regularizedGamma_eq_zero_of_nonpos_right _
      (mul_nonpos_of_nonneg_of_nonpos α.coe_nonneg hx.le)]
  · lift x to ℝ≥0 using hx
    have hae : (Y ⁻¹' Iic (x : ℝ) : Set Ω) =ᵐ[P] {ω | hittingAfter M (Ici c) 0 ω ≤ x} := by
      filter_upwards [h.hittingAfter_Ici_ae_ne_top hα c] with ω hfin
      simp only [mem_preimage, mem_Iic, Y, NNReal.coe_le_coe, WithTop.untopA_le_iff hfin]
    rw [measureReal_congr hae, h.measureReal_hittingAfter_Ici_le hrc hc x]

/-- **Exponential law of the first arrival time.** For an almost-surely right-continuous
natural-valued filtered Poisson process of positive rate `0 < α`, the first arrival time
`((hittingAfter M (Set.Ici 1) 0 ω).untopA : ℝ)` has law `expMeasure α`. -/
theorem hasLaw_untopA_hittingAfter_Ici_one_expMeasure
    (h : IsFilteredPoissonProcess ℱ α (fun t ω ↦ (M t ω : ℝ)) P)
    (hrc : ∀ᵐ ω ∂P, IsRightContinuous (M · ω)) (hα : 0 < α) :
    HasLaw (fun ω ↦ ((hittingAfter M (Ici 1) 0 ω).untopA : ℝ)) (expMeasure α) P := by
  simpa [expMeasure] using h.hasLaw_untopA_hittingAfter_Ici_gammaMeasure hrc hα one_ne_zero

end TauCeti.Probability.IsFilteredPoissonProcess
