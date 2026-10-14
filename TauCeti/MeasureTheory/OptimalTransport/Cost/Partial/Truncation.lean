/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Cost.Partial.Integrable

/-!
# Cost truncation and the relaxed transport value

For a measurable nonnegative cost and finite equal-mass marginals, the ordinary transport
values for `min c n` increase to the relaxed transport value. Infinite costs and infinite
relaxed values are allowed. No topology on either carrier is needed.

The quantitative bridge discards the part of a coupling where `c ≥ C`. Markov's inequality
for `min c C` bounds the discarded mass, while the retained plan has its original `c`-cost
bounded by the truncated cost of the full plan. In the other direction, bounded-cost
completion already shows that each truncated ordinary value is at most the relaxed value.

This characterization reduces relaxed extended-cost duality to bounded-cost duality.
It does not identify the limit with the ordinary value for an arbitrary measurable cost:
truncation and minimization need not commute without relaxation.

## References

* M. Beiglböck, C. Léonard and W. Schachermayer, *A general duality theorem for the
  Monge--Kantorovich transport problem*, Studia Math. 209 (2012), 151--167,
  Theorem 3.5, the constant-truncation case. The argument here uses restriction and
  Markov's inequality directly, and also permits finite equal-mass marginals and an
  infinite relaxed value.
-/

public section

noncomputable section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace TauCeti

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  {μ : Measure X} {ν : Measure Y} {π : Measure (X × Y)}
  {c : X × Y → ℝ≥0∞} {ε : ℝ≥0∞} {C : ℝ≥0}

/-- If the truncated cost of a coupling is at most `C * ε`, discarding the region
`c ≥ C` produces a partial plan of deficit at most `ε`, whose original cost is at most
the truncated cost of the coupling. This estimate needs no finiteness of the marginals. -/
theorem IsCoupling.partialTransportCost_le_lintegral_min (hπ : IsCoupling π μ ν)
    (hc : Measurable c) (hC : 0 < C)
    (hint : ∫⁻ z, min (c z) C ∂π ≤ C * ε) :
    partialTransportCost c μ ν ε ≤ ∫⁻ z, min (c z) C ∂π := by
  let s := {z | c z < C}
  have hs : MeasurableSet s := measurableSet_lt hc measurable_const
  have hC0 : (C : ℝ≥0∞) ≠ 0 := (ENNReal.coe_pos.2 hC).ne'
  have hdiscard : π sᶜ ≤ ε := by
    have hmarkov := meas_ge_le_lintegral_div (μ := π)
      (f := fun z ↦ min (c z) C) (hc.min measurable_const).aemeasurable
      hC0 ENNReal.coe_ne_top
    have hdiv : (∫⁻ z, min (c z) C ∂π) / C ≤ ε :=
      (ENNReal.div_le_iff hC0 ENNReal.coe_ne_top).2 (by simpa [mul_comm] using hint)
    simpa only [s, compl_ofPred, not_lt, le_min_iff, le_refl, and_true] using
      hmarkov.trans hdiv
  have hmass : μ univ ≤ (π.restrict s) univ + ε := by
    calc
      μ univ = π univ := hπ.measure_univ_left
      _ = π s + π sᶜ := (measure_add_measure_compl hs).symm
      _ ≤ (π.restrict s) univ + ε := by
        rw [Measure.restrict_apply_univ]
        exact add_le_add le_rfl hdiscard
  refine (partialTransportCost_le_lintegral
    ((Measure.fst_mono Measure.restrict_le_self).trans_eq hπ.fst_eq)
    ((Measure.snd_mono Measure.restrict_le_self).trans_eq hπ.snd_eq) hmass).trans ?_
  calc
    ∫⁻ z in s, c z ∂π = ∫⁻ z in s, min (c z) C ∂π :=
      setLIntegral_congr_fun hs fun _ hz ↦ (min_eq_left hz.le).symm
    _ ≤ ∫⁻ z, min (c z) C ∂π := setLIntegral_le_lintegral _ _

/-- A truncated ordinary value strictly below `C * ε` bounds the original partial value
with deficit `ε`. No attainment of the truncated infimum is assumed. -/
theorem partialTransportCost_le_transportCost_min (hc : Measurable c) (hC : 0 < C)
    (hcost : transportCost (fun z ↦ min (c z) C) μ ν < C * ε) :
    partialTransportCost c μ ν ε ≤ transportCost (fun z ↦ min (c z) C) μ ν := by
  refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
  obtain ⟨π, hπ, hint⟩ := transportCost_lt_iff.1 (lt_min ha hcost)
  exact (hπ.partialTransportCost_le_lintegral_min hc hC
    (hint.le.trans (min_le_right _ _))).trans (hint.le.trans (min_le_left _ _))

variable [IsFiniteMeasure μ]

/-- **The relaxed transport value is the supremum of the truncated ordinary values.**
For finite equal-mass marginals and a measurable cost, constant truncation converges to
the relaxed value, including when that value is infinite. -/
theorem relaxedTransportCost_eq_iSup_transportCost_min (hmass : μ univ = ν univ)
    (hc : Measurable c) :
    relaxedTransportCost c μ ν =
      ⨆ n : ℕ, transportCost (fun z ↦ min (c z) n) μ ν := by
  refine le_antisymm (relaxedTransportCost_le fun ε hε ↦ ?_)
    (iSup_le fun n ↦ ?_)
  · refine le_of_forall_gt_imp_ge_of_dense fun a ha ↦ ?_
    by_cases hatop : a = ∞
    · simp [hatop]
    have hlimit : Tendsto (fun n : ℕ ↦ (n : ℝ≥0∞) * ε) atTop (𝓝 ∞) := by
      simpa [ENNReal.top_mul hε.ne'] using
        ENNReal.Tendsto.mul_const ENNReal.tendsto_nat_nhds_top
          (b := ε) (Or.inl ENNReal.top_ne_zero)
    obtain ⟨n, hn, han⟩ := (eventually_gt_atTop 0).and
      (hlimit.eventually (Ioi_mem_nhds (lt_top_iff_ne_top.2 hatop))) |>.exists
    have hCn : 0 < (n : ℝ≥0) := by exact_mod_cast hn
    have hcost : transportCost (fun z ↦ min (c z) n) μ ν < (n : ℝ≥0∞) * ε :=
      (le_iSup (fun n : ℕ ↦ transportCost (fun z ↦ min (c z) n) μ ν) n).trans_lt
        (ha.trans han)
    exact (partialTransportCost_le_transportCost_min hc hCn hcost).trans
      ((le_iSup (fun n : ℕ ↦ transportCost (fun z ↦ min (c z) n) μ ν) n).trans ha.le)
  · have hbounded := relaxedTransportCost_eq_transportCost_of_bounded
      (c := fun z ↦ min (c z) n) hmass (n : ℝ≥0) (fun _ ↦ min_le_right _ _)
    rw [← hbounded]
    exact relaxedTransportCost_mono fun _ ↦ min_le_left _ _

/-- Ordinary values for finite constant caps tending to infinity converge to the relaxed
value. The caps need not be monotone, and no finite-cost feasible plan is required. -/
theorem tendsto_transportCost_min (hmass : μ univ = ν univ) (hc : Measurable c)
    {ι : Type*} {l : Filter ι} {Cs : ι → ℝ≥0} (hCs : Tendsto Cs l atTop) :
    Tendsto (fun i ↦ transportCost (fun z ↦ min (c z) (Cs i)) μ ν)
      l (𝓝 (relaxedTransportCost c μ ν)) := by
  let f : ℝ≥0 → ℝ≥0∞ := fun C ↦ transportCost (fun z ↦ min (c z) C) μ ν
  have hf : Monotone f := fun _ _ h ↦
    transportCost_mono fun _ ↦ min_le_min_left _ (ENNReal.coe_le_coe.2 h)
  have hsup : relaxedTransportCost c μ ν = ⨆ C, f C := by
    rw [relaxedTransportCost_eq_iSup_transportCost_min hmass hc]
    simpa only [f, ENNReal.coe_natCast] using
      hf.iSup_comp_tendsto_atTop (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  rw [hsup]
  exact (tendsto_atTop_iSup hf).comp hCs

end TauCeti
