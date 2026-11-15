/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Count
public import TauCeti.MeasureTheory.Group.Foelner.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import TauCeti.Data.ENNReal.NatCastDiv

/-!
# Counting-measure Følner bridges for finite sets

For a group `G` acting on a measurable space `X` with measurable singletons, a subset `F : Set X`
has finite nonzero counting measure if and only if `F` is finite and nonempty, and its counting
measure is `(F.ncard : ℝ≥0∞)`. Unlike the `Finset` formulation, phrasing Følner tests via
`Set.Finite` and `Set.ncard` needs no `[DecidableEq X]` instance. This file bridges `IsFoelner`
and `maxFoelner` for `Measure.count` with `Set.ncard` ratios and finite-test criteria (with
`@[to_additive]` counterparts throughout).

## Main results

* `MeasureTheory.Measure.smulInvariantMeasure_count`: counting measure on a space with measurable
  singletons is invariant under any group action.
* `MeasureTheory.Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard`: for a finite nonempty
  `F : Set X`, the counting-measure Følner ratio is below `ENNReal.ofReal ε` iff
  `(((m • F) ∆ F).ncard : ℝ) < ε * F.ncard`.
* `IsFoelner.tendsto_ncard_smul_symmDiff_div_ncard`: real `Set.ncard` ratios of a counting-measure
  Følner family tend to zero.
* `TauCeti.maxFoelner_count_neBot_iff_of_closure_eq_top`, `TauCeti.maxFoelner_count_neBot_iff`:
  finite-`Set` characterizations of `(maxFoelner G Measure.count).NeBot`.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Lemma 3.4.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal Pointwise symmDiff Topology

section Count

variable {G X : Type*} [Group G] [MulAction G X] [MeasurableSpace X]

/-- Counting measure on a space with measurable singletons is invariant under any group action. -/
@[to_additive vAddInvariantMeasure_count
/-- Counting measure on a space with measurable singletons is invariant under any additive group
action. -/]
theorem MeasureTheory.Measure.smulInvariantMeasure_count [MeasurableSingletonClass X] :
    SMulInvariantMeasure G X Measure.count :=
  ⟨fun g s _ ↦ by
    rw [preimage_smul]
    exact Measure.count_injective_image (MulAction.injective g⁻¹) s⟩

/-- Counting measure of any finite set `s : Set X` with measurable singletons equals `s.ncard`. -/
theorem MeasureTheory.Measure.count_apply_eq_ncard [MeasurableSingletonClass X] {s : Set X}
    (hs : s.Finite) : Measure.count s = s.ncard := by
  rw [Measure.count_apply_finite s hs, Set.ncard_eq_toFinset_card s hs]

/-- For a finite nonempty `F : Set X`, the counting-measure Følner ratio at `m` is below
`ENNReal.ofReal ε` iff `(((m • F) ∆ F).ncard : ℝ) < ε * F.ncard`. -/
@[to_additive
/-- For a finite nonempty `F : Set X`, the counting-measure additive Følner ratio at `m` is below
`ENNReal.ofReal ε` iff `(((m +ᵥ F) ∆ F).ncard : ℝ) < ε * F.ncard`. -/]
theorem MeasureTheory.Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard
    [MeasurableSingletonClass X] {M : Type*} [SMul M X] {F : Set X} (hfin : F.Finite)
    (hne : F.Nonempty) (m : M) {ε : ℝ} :
    Measure.count ((m • F) ∆ F) / Measure.count F < ENNReal.ofReal ε ↔
      (((m • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  have hsd : ((m • F) ∆ F).Finite := (hfin.smul_set).symmDiff hfin
  rw [Measure.count_apply_eq_ncard hsd, Measure.count_apply_eq_ncard hfin]
  exact ENNReal.natCast_div_natCast_lt_ofReal_iff ((Set.ncard_pos hfin).2 hne)

/-- Along any counting-measure Følner family, the real `Set.ncard` translation-boundary ratios tend
to zero without requiring `[MeasurableSingletonClass X]` or `[DecidableEq X]`. -/
@[to_additive
/-- Along any counting-measure additive Følner family, the real `Set.ncard` translation-boundary
ratios tend to zero without requiring `[MeasurableSingletonClass X]` or `[DecidableEq X]`. -/]
theorem IsFoelner.tendsto_ncard_smul_symmDiff_div_ncard {ι : Type*} {l : Filter ι} {F : ι → Set X}
    (hF : IsFoelner G Measure.count l F) (g : G) :
    Tendsto (fun i ↦ (((g • F i) ∆ F i).ncard : ℝ) / (F i).ncard) l (𝓝 0) := by
  have hlim := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp (hF.tendsto_meas_smul_symmDiff g)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (.of_forall fun _ ↦ by positivity) ?_
  filter_upwards [hF.eventually_measurableSet, hF.eventually_meas_ne_top,
    (hF.tendsto_meas_smul_symmDiff g).eventually (gt_mem_nhds zero_lt_one)] with i hFm hitop hlt
  have hfin : (F i).Finite := (Measure.count_apply_lt_top' hFm).1 (lt_top_iff_ne_top.2 hitop)
  have hsd : ((g • F i) ∆ F i).Finite := (hfin.smul_set).symmDiff hfin
  have hcountF : Measure.count (F i) = (F i).ncard := by
    rw [Measure.count_apply_finite' hfin hFm, Set.ncard_eq_toFinset_card _ hfin]
  have hle : (((g • F i) ∆ F i).ncard : ℝ≥0∞) / (F i).ncard ≤
      Measure.count ((g • F i) ∆ F i) / Measure.count (F i) := by
    rw [hcountF]
    refine ENNReal.div_le_div_right ?_ _
    calc
      (((g • F i) ∆ F i).ncard : ℝ≥0∞) = hsd.toFinset.card := by
        rw [Set.ncard_eq_toFinset_card _ hsd]
      _ = ∑' _ : (hsd.toFinset : Set X), (1 : ℝ≥0∞) := by simp
      _ ≤ Measure.count (hsd.toFinset : Set X) := Measure.le_count_apply
      _ = Measure.count ((g • F i) ∆ F i) := by rw [Finite.coe_toFinset]
  simpa [ENNReal.toReal_div, Function.comp_def] using ENNReal.toReal_mono hlt.ne_top hle

namespace TauCeti

/-- Generating-set finite-`Set` characterization of `(maxFoelner G Measure.count).NeBot` on any
space with measurable singletons, requiring no `[DecidableEq]` assumption. -/
@[to_additive maxAddFoelner_count_neBot_iff_of_closure_eq_top
/-- Generating-set finite-`Set` characterization of `(maxAddFoelner G Measure.count).NeBot` on any
space with measurable singletons, requiring no `[DecidableEq]` assumption. -/]
theorem maxFoelner_count_neBot_iff_of_closure_eq_top [MeasurableSingletonClass X] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    (maxFoelner G (Measure.count : Measure X)).NeBot ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ, 0 < ε →
        ∃ F : Set X, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  have := Measure.smulInvariantMeasure_count (G := G) (X := X)
  rw [maxFoelner_neBot_iff_of_closure_eq_top hS]
  constructor
  · intro h K hKS ε hε
    obtain ⟨F, hFm, h0, htop, hFK⟩ := h K hKS (ENNReal.ofReal ε)
      (ENNReal.ofReal_pos.2 hε).ne'
    have hfin : F.Finite := (Measure.count_apply_lt_top' hFm).1 (lt_top_iff_ne_top.2 htop)
    have hne : F.Nonempty := by
      simpa [Set.nonempty_iff_ne_empty] using mt Measure.count_eq_zero_iff.2 h0
    exact ⟨F, hfin, hne, fun g hg ↦
      (Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard hfin hne g).1 (hFK g hg)⟩
  · intro h K hKS ε hε
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ∞ with rfl | htop
      · exact ⟨1, zero_lt_one, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε htop, (ENNReal.ofReal_toReal htop).le⟩
    obtain ⟨F, hfin, hne, hFK⟩ := h K hKS δ hδ0
    refine ⟨F, hfin.measurableSet, ?_, ?_, fun g hg ↦ ?_⟩
    · simpa [Set.nonempty_iff_ne_empty] using hne
    · exact (Measure.count_apply_lt_top.2 hfin).ne
    · exact ((Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard hfin hne g).2
        (hFK g hg)).trans_le hδε

/-- Finite-`Set` characterization of `(maxFoelner G Measure.count).NeBot` on any space with
measurable singletons. -/
@[to_additive maxAddFoelner_count_neBot_iff
/-- Finite-`Set` characterization of `(maxAddFoelner G Measure.count).NeBot` on any space with
measurable singletons. -/]
theorem maxFoelner_count_neBot_iff [MeasurableSingletonClass X] :
    (maxFoelner G (Measure.count : Measure X)).NeBot ↔
      ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
        ∃ F : Set X, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  simpa using maxFoelner_count_neBot_iff_of_closure_eq_top (G := G) (X := X) Subgroup.closure_univ

end TauCeti

end Count
