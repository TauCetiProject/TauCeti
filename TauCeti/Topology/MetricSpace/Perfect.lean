/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.EMetricSpace.Diam
public import Mathlib.Topology.MetricSpace.Perfect
public import TauCeti.Topology.Bases

/-!
# Perfect sets in metric spaces

A Polish space has at most continuum many points
(`TauCeti.mk_le_continuum_of_secondCountableTopology`). A nonempty perfect subset of a completely
metrizable space contains a copy of Cantor space, so it has at least continuum many points.
Together these give the cardinality of a nonempty perfect subset of a Polish space: exactly `𝔠`.

In a perfect extended metric space, a nonempty open set also splits into two disjoint nonempty
open sets of small diameter whose closures stay inside it: the open-set counterpart of Mathlib's
`Perfect.small_diam_splitting`, used to build Cantor schemes of open sets.

## Main results

* `Perfect.continuum_le_mk`: a nonempty perfect subset of a completely metrizable space has at
  least `𝔠` points.
* `Perfect.mk_eq_continuum`: a nonempty perfect subset of a Polish space has exactly `𝔠` points.
* `IsOpen.exists_disjoint_closure_subset`: in a perfect extended metric space, a nonempty open set
  contains two disjoint nonempty open sets of small diameter, with closures inside it.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Theorem 6.2 and Corollary 6.3.
-/

public section

open Set Function Cardinal TopologicalSpace Topology
open scoped ENNReal

universe u

variable {X : Type u} [TopologicalSpace X] {C : Set X}

/-- **A nonempty perfect set in a completely metrizable space has at least continuum many
points**: it contains the range of a continuous injection of Cantor space. -/
theorem Perfect.continuum_le_mk [IsCompletelyMetrizableSpace X] (hC : Perfect C)
    (hne : C.Nonempty) : 𝔠 ≤ #C := by
  let := upgradeIsCompletelyMetrizable X
  obtain ⟨f, hfC, -, hf⟩ := hC.exists_nat_bool_injection hne
  have hinj : Injective fun x => (⟨f x, hfC (mem_range_self x)⟩ : C) := fun x y hxy =>
    hf (congrArg Subtype.val hxy)
  simpa using lift_mk_le_lift_mk_of_injective hinj

/-- **A nonempty perfect set in a Polish space has cardinality continuum.** -/
theorem Perfect.mk_eq_continuum [PolishSpace X] (hC : Perfect C) (hne : C.Nonempty) :
    #C = 𝔠 :=
  le_antisymm (TauCeti.mk_le_continuum_of_secondCountableTopology C) (hC.continuum_le_mk hne)

section Split

variable {X : Type*} [EMetricSpace X]

/-- **Splitting a nonempty open set** in a perfect extended metric space: a nonempty open set `V`
contains two disjoint nonempty open sets of diameter at most `ε`, with closures inside `V`. -/
theorem IsOpen.exists_disjoint_closure_subset [PerfectSpace X] {V : Set X} (hV : IsOpen V)
    (hne : V.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ W : Bool → Set X, (∀ b, IsOpen (W b)) ∧ (∀ b, (W b).Nonempty) ∧
      (∀ b, closure (W b) ⊆ V) ∧ (∀ b, Metric.ediam (W b) ≤ ε) ∧ Disjoint (W false) (W true) := by
  -- an open neighbourhood of `z` inside the ball of radius `r`, with closure inside `V`
  have hsmall (z : X) (hz : z ∈ V) (r : ℝ≥0∞) (hr : 0 < r) : ∃ W, IsOpen W ∧ z ∈ W ∧
      closure W ⊆ V ∧ W ⊆ Metric.eball z r := by
    obtain ⟨t, ht, htc, htV⟩ := exists_mem_nhds_isClosed_subset (hV.mem_nhds hz)
    refine ⟨interior t ∩ Metric.eball z r, isOpen_interior.inter Metric.isOpen_eball,
      ⟨mem_interior_iff_mem_nhds.2 ht, Metric.mem_eball_self hr⟩, ?_, inter_subset_right⟩
    exact (htc.closure_subset_iff.2 (inter_subset_left.trans interior_subset)).trans htV
  -- two distinct points of `V`, at positive distance `d`
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hyV, hyx⟩ :=
    (𝓝[≠] x).nonempty_of_mem (sdiff_mem_nhdsWithin_compl (hV.mem_nhds hx) {x})
  have hd : 0 < edist x y := edist_pos.2 (Ne.symm hyx)
  set r := min (edist x y / 2) (ε / 2)
  have hr : 0 < r := lt_min (ENNReal.half_pos hd.ne') (ENNReal.half_pos hε.ne')
  obtain ⟨W₀, hW₀o, hxW₀, hW₀V, hW₀r⟩ := hsmall x hx r hr
  obtain ⟨W₁, hW₁o, hyW₁, hW₁V, hW₁r⟩ := hsmall y hyV r hr
  have h2r : 2 * r ≤ ε :=
    calc 2 * r ≤ 2 * (ε / 2) := by gcongr; exact min_le_right _ _
      _ = ε := ENNReal.mul_div_cancel two_ne_zero ENNReal.ofNat_ne_top
  have hdiam {z : X} {W : Set X} (hW : W ⊆ Metric.eball z r) : Metric.ediam W ≤ ε :=
    ((Metric.ediam_mono hW).trans Metric.ediam_eball_le).trans h2r
  refine ⟨fun b => cond b W₁ W₀, fun b => ?_, fun b => ?_, fun b => ?_, fun b => ?_, ?_⟩
  · cases b <;> assumption
  · cases b
    exacts [⟨x, hxW₀⟩, ⟨y, hyW₁⟩]
  · cases b <;> assumption
  · cases b
    exacts [hdiam hW₀r, hdiam hW₁r]
  · refine (Metric.eball_disjoint ?_).mono hW₀r hW₁r
    exact (add_le_add (min_le_left _ _) (min_le_left _ _)).trans (ENNReal.add_halves _).le
