/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.HittingTime
public import Mathlib.MeasureTheory.Constructions.BorelSpace.WithTop
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Countable descriptions of continuous level hits

For a continuous real path on nonnegative time, the first hit of a closed upper level is the
supremum of the first strict hits of levels approaching it from below. Each strict hit can in
turn be computed using any dense family of sampling times. The resulting countable formula
makes closed level hits ambient-measurable for everywhere-continuous processes, and
almost-everywhere measurable for processes with almost-surely continuous paths.

This distinction matters on raw filtrations: almost-sure continuity alone does not make a
literal pathwise hitting time a stopping time. The measurable representative supplied here is
suitable for probability estimates comparing grid hits with continuous-path level hits; no
stopping-time property is asserted for it. Lower closed-level hitting times also converge to
the limiting closed-level hit, including when that hit is infinite.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, Chapter 1, §§2 and 5.
-/

public section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace MeasureTheory

/-- The native hitting time is the infimum, in the extended time order, of all actual hits.
The empty set of hits has infimum infinity. -/
theorem hittingAfter_eq_iInf {ι Ω E : Type*} [ConditionallyCompleteLinearOrderBot ι]
    (X : ι → Ω → E) (s : Set E) (a : ι) (ω : Ω) :
    hittingAfter X s a ω = ⨅ t, ⨅ (_ : a ≤ t ∧ X t ω ∈ s), (t : WithTop ι) := by
  classical
  simp only [hittingAfter_def]
  split_ifs with h
  · rw [WithTop.coe_sInf (s := {t | a ≤ t ∧ X t ω ∈ s})
      ⟨h.choose, h.choose_spec⟩ ⟨a, fun t ht ↦ ht.1⟩]
    simp only [mem_ofPred_eq]
  · symm
    exact iInf_eq_top.2 fun t ↦ iInf_eq_top.2 fun ht ↦ (h ⟨t, ht⟩).elim

end MeasureTheory

namespace Continuous

variable {Ω : Type*} {X : ℝ≥0 → Ω → ℝ} {ω : Ω} {c : ℝ} {θ : ℕ → ℝ}

/-- On every compact interval strictly before the hit of `c`, all sufficiently close lower
levels also remain unhit throughout that interval. -/
theorem eventually_lt_hittingAfter_Ici (hf : Continuous (fun t ↦ X t ω))
    (hθ : Tendsto θ atTop (𝓝 c)) {t : ℝ≥0}
    (ht : (t : WithTop ℝ≥0) < hittingAfter X (Ici c) 0 ω) :
    ∀ᶠ n in atTop, (t : WithTop ℝ≥0) < hittingAfter X (Ici (θ n)) 0 ω := by
  obtain ⟨b, htb, hb⟩ := exists_between ht
  lift b to ℝ≥0 using hb.ne_top with b
  obtain ⟨u, hu, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 (bot_le : 0 ≤ b))
    hf.continuousOn
  have huc : X u ω < c := lt_of_not_ge fun h ↦
    (hb.trans_le (hittingAfter_le_of_mem (bot_le : 0 ≤ u) h)).not_ge (by exact_mod_cast hu.2)
  filter_upwards [hθ.eventually (eventually_gt_nhds huc)] with n hn
  rw [hittingAfter_eq_iInf]
  refine htb.trans_le (le_iInf fun v ↦ le_iInf fun hv ↦ ?_)
  exact WithTop.coe_le_coe.2 (le_of_not_gt fun hvb ↦
    (hn.trans_le hv.2).not_ge (hmax ⟨bot_le, hvb.le⟩))

open scoped Classical in
/-- Hits of an open set by a continuous path can be computed from any dense family of
sampling times. In particular, a countable dense family suffices. -/
theorem hittingAfter_eq_iInf_of_isOpen {E κ : Type*} [TopologicalSpace E]
    {X : ℝ≥0 → Ω → E} (hf : Continuous (fun t ↦ X t ω)) {U : Set E} (hU : IsOpen U)
    {d : κ → ℝ≥0} (hd : DenseRange d) :
    hittingAfter X U 0 ω =
      ⨅ k, if X (d k) ω ∈ U then (d k : WithTop ℝ≥0) else ⊤ := by
  classical
  rw [hittingAfter_eq_iInf]
  apply le_antisymm
  · refine le_iInf fun k ↦ ?_
    split_ifs with hk
    · exact iInf₂_le (d k) ⟨bot_le, hk⟩
    · exact le_top
  · refine le_iInf fun t ↦ le_iInf fun ht ↦ ?_
    refine le_of_forall_gt fun b hb ↦ ?_
    obtain ⟨v, htv, hvb⟩ := WithTop.lt_iff_exists_coe_btwn.1 hb
    have htv' : t < v := WithTop.coe_lt_coe.1 htv
    obtain ⟨k, hk⟩ := hd.exists_mem_open
      ((isOpen_Iio (a := v)).inter (hU.preimage hf)) ⟨t, htv', ht.2⟩
    have hkv : (d k : WithTop ℝ≥0) ≤ (v : WithTop ℝ≥0) :=
      WithTop.coe_le_coe.2 hk.1.le
    have hsample : (⨅ j, if X (d j) ω ∈ U then (d j : WithTop ℝ≥0) else ⊤) ≤
        (d k : WithTop ℝ≥0) := by
      calc
        _ ≤ (if X (d k) ω ∈ U then (d k : WithTop ℝ≥0) else ⊤) := iInf_le _ k
        _ = (d k : WithTop ℝ≥0) := ite_eq_left hk.2
    exact hsample.trans_lt (hkv.trans_lt hvb)

/-- Closed upper-level hits are limits of hits of levels approaching from below. No
monotonicity of the levels and no finiteness of the limiting hitting time are required. -/
theorem tendsto_hittingAfter_Ici (hf : Continuous (fun t ↦ X t ω)) (hθc : ∀ n, θ n ≤ c)
    (hθ : Tendsto θ atTop (𝓝 c)) :
    Tendsto (fun n ↦ hittingAfter X (Ici (θ n)) 0 ω) atTop
      (𝓝 (hittingAfter X (Ici c) 0 ω)) := by
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · lift a to ℝ≥0 using ha.ne_top with t
    exact hf.eventually_lt_hittingAfter_Ici hθ ha
  · exact Eventually.of_forall fun n ↦ lt_of_le_of_lt
      (hittingAfter_apply_anti X 0 ω (Ici_subset_Ici.2 (hθc n))) hb

/-- A closed upper-level hit is a supremum of strict lower-level hits, each computed using a
dense family of sampling times. This is a countable formula when the family is countable. -/
theorem hittingAfter_Ici_eq_iSup_iInf {κ : Type*} (hf : Continuous (fun t ↦ X t ω))
    {d : κ → ℝ≥0} (hd : DenseRange d) (hθc : ∀ n, θ n < c) (hθ : Tendsto θ atTop (𝓝 c)) :
    hittingAfter X (Ici c) 0 ω =
      ⨆ n, ⨅ k, if θ n < X (d k) ω then (d k : WithTop ℝ≥0) else ⊤ := by
  classical
  have hsample (a : ℝ) : hittingAfter X (Ioi a) 0 ω =
      ⨅ k, if a < X (d k) ω then (d k : WithTop ℝ≥0) else ⊤ := by
    simpa only [mem_Ioi] using hf.hittingAfter_eq_iInf_of_isOpen (U := Ioi a) isOpen_Ioi hd
  simp_rw [← hsample]
  apply le_antisymm
  · refine le_of_tendsto (hf.tendsto_hittingAfter_Ici (fun n ↦ (hθc n).le) hθ) ?_
    exact Eventually.of_forall fun n ↦
      (hittingAfter_apply_anti X 0 ω (Ioi_subset_Ici_self (a := θ n))).trans
        (le_iSup (fun j ↦ hittingAfter X (Ioi (θ j)) 0 ω) n)
  · exact iSup_le fun n ↦ hittingAfter_apply_anti X 0 ω (fun x hx ↦ (hθc n).trans_le hx)

end Continuous

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

/-- There is an ambient-measurable representative of a closed level hit which agrees with the
native hitting time on every continuous path. No measure or filtration is needed. -/
theorem exists_measurable_eq_hittingAfter_Ici (hX : ∀ t, Measurable (X t)) (c : ℝ) :
    ∃ τ : Ω → WithTop ℝ≥0, Measurable τ ∧
      ∀ ω, Continuous (fun t ↦ X t ω) → τ ω = hittingAfter X (Ici c) 0 ω := by
  classical
  let d : ℕ → ℝ≥0 := TopologicalSpace.denseSeq ℝ≥0
  let θ : ℕ → ℝ := fun n ↦ c - 1 / (n + 1)
  have hθc : ∀ n, θ n < c := fun n ↦ sub_lt_self _ (by positivity)
  have hθ : Tendsto θ atTop (𝓝 c) := by
    simpa only [θ, sub_zero] using
      (tendsto_const_nhds (x := c)).sub tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨fun ω ↦ ⨆ n, ⨅ k, if θ n < X (d k) ω then (d k : WithTop ℝ≥0) else ⊤, ?_, ?_⟩
  · exact Measurable.iSup fun n ↦ Measurable.iInf fun k ↦
      measurable_const.ite (measurableSet_lt measurable_const (hX _)) measurable_const
  · intro ω hω
    exact (hω.hittingAfter_Ici_eq_iSup_iInf (TopologicalSpace.denseRange_denseSeq ℝ≥0) hθc hθ).symm

/-- Closed level hits of an everywhere-continuous process with measurable evaluations are
ambient-measurable. -/
theorem measurable_hittingAfter_Ici (hX : ∀ t, Measurable (X t))
    (hc : ∀ ω, Continuous (fun t ↦ X t ω)) (c : ℝ) :
    Measurable (hittingAfter X (Ici c) 0) := by
  obtain ⟨τ, hτ, heq⟩ := exists_measurable_eq_hittingAfter_Ici hX c
  have h : τ = hittingAfter X (Ici c) 0 := funext fun ω ↦ heq ω (hc ω)
  rwa [h] at hτ

/-- Closed level hits of a process with measurable evaluations and almost-surely continuous
paths are almost-everywhere measurable, even on an incomplete ambient space. This does not
assert the raw-filtration stopping-time property. -/
theorem aemeasurable_hittingAfter_Ici {P : Measure Ω} (hX : ∀ t, Measurable (X t))
    (hc : ∀ᵐ ω ∂P, Continuous (fun t ↦ X t ω)) (c : ℝ) :
    AEMeasurable (hittingAfter X (Ici c) 0) P := by
  obtain ⟨τ, hτ, heq⟩ := exists_measurable_eq_hittingAfter_Ici hX c
  exact hτ.aemeasurable.congr (hc.mono fun ω hω ↦ heq ω hω)

end TauCeti.Probability
