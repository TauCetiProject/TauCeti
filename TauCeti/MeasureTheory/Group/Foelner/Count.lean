/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.MeasureTheory.Measure.Count
public import TauCeti.MeasureTheory.Group.Foelner.Basic
public import TauCeti.MeasureTheory.Measure.Count.Action
import TauCeti.Data.ENNReal.NatCastDiv
import TauCeti.MeasureTheory.Measure.Count.Basic

/-!
# Counting-measure Følner bridges for finite sets

For a group `G` acting on a measurable space `X` with measurable singletons, a subset `F : Set X`
has finite nonzero counting measure if and only if `F` is finite and nonempty, and its counting
measure is `(F.ncard : ℝ≥0∞)`. Unlike the `Finset` formulation, phrasing Følner tests via
`Set.Finite` and `Set.ncard` needs no `[DecidableEq X]` instance. This file bridges `IsFoelner`
and `maxFoelner` for `Measure.count` with `Set.ncard` ratios and finite-test criteria (with
`@[to_additive]` counterparts throughout).

## Main results

* `MeasureTheory.Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard`,
  `MeasureTheory.Measure.forall_exists_count_smul_symmDiff_div_lt_iff`: for finite nonempty
  `F : Set X`, counting-measure Følner tests agree with real `Set.ncard` tests.
* `MeasureTheory.Measure.ncard_smul_symmDiff_div_ncard_le_count_div_count`,
  `IsFoelner.tendsto_ncard_smul_symmDiff_div_ncard`: real `Set.ncard` ratios of a counting-measure
  Følner family are bounded by counting-measure ratios and tend to zero.
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

/-- For a finite nonempty `F : Set X`, the counting-measure Følner ratio at `m` is below
`ENNReal.ofReal ε` iff `(((m • F) ∆ F).ncard : ℝ) < ε * F.ncard`. -/
@[to_additive count_vadd_symmDiff_div_count_lt_ofReal_iff_ncard
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

/-- Passing the counting-measure Følner test on `K` for all nonzero tolerances `ε : ℝ≥0∞` is
equivalent to passing the real `Set.ncard` test on `K` for all `ε > 0`. -/
@[to_additive forall_exists_count_vadd_symmDiff_div_lt_iff
/-- Passing the counting-measure additive Følner test on `K` for all nonzero tolerances
`ε : ℝ≥0∞` is equivalent to passing the real `Set.ncard` test on `K` for all `ε > 0`. -/]
theorem MeasureTheory.Measure.forall_exists_count_smul_symmDiff_div_lt_iff
    [MeasurableSingletonClass X] {M : Type*} [SMul M X] (K : Finset M) :
    (∀ ε : ℝ≥0∞, ε ≠ 0 →
        ∃ F : Set X, MeasurableSet F ∧ Measure.count F ≠ 0 ∧ Measure.count F ≠ ∞ ∧
          ∀ m ∈ K, Measure.count ((m • F) ∆ F) / Measure.count F < ε) ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ F : Set X, F.Finite ∧ F.Nonempty ∧
          ∀ m ∈ K, (((m • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  constructor
  · intro h ε hε
    obtain ⟨F, hFm, h0, htop, hFK⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε).ne'
    have hfin : F.Finite := (Measure.count_apply_lt_top' hFm).1 (lt_top_iff_ne_top.2 htop)
    have hne : F.Nonempty := by
      simpa [← Set.ne_empty_iff_nonempty] using mt Measure.count_eq_zero_iff.2 h0
    exact ⟨F, hfin, hne, fun m hm ↦
      (Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard hfin hne m).1 (hFK m hm)⟩
  · intro h ε hε
    obtain ⟨δ, hδ0, hδε⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
      rcases eq_or_ne ε ∞ with rfl | htop
      · exact ⟨1, zero_lt_one, le_top⟩
      · exact ⟨ε.toReal, ENNReal.toReal_pos hε htop, (ENNReal.ofReal_toReal htop).le⟩
    obtain ⟨F, hfin, hne, hFK⟩ := h δ hδ0
    refine ⟨F, hfin.measurableSet, ?_, ?_, fun m hm ↦ ?_⟩
    · simpa [← Set.ne_empty_iff_nonempty] using hne
    · exact (Measure.count_apply_lt_top.2 hfin).ne
    · exact ((Measure.count_smul_symmDiff_div_count_lt_ofReal_iff_ncard hfin hne m).2
        (hFK m hm)).trans_le hδε

/-- The counting-measure Følner ratio of a finite measurable set bounds its `Set.ncard` ratio from
above, without requiring `[MeasurableSingletonClass X]` or `[DecidableEq X]`. -/
@[to_additive ncard_vadd_symmDiff_div_ncard_le_count_div_count
/-- The counting-measure additive Følner ratio of a finite measurable set bounds its `Set.ncard`
ratio from above, without requiring `[MeasurableSingletonClass X]` or `[DecidableEq X]`. -/]
theorem MeasureTheory.Measure.ncard_smul_symmDiff_div_ncard_le_count_div_count {M : Type*}
    [SMul M X] {F : Set X} (hfin : F.Finite) (hFm : MeasurableSet F) (m : M) :
    (((m • F) ∆ F).ncard : ℝ≥0∞) / F.ncard ≤
      Measure.count ((m • F) ∆ F) / Measure.count F := by
  have hsd : ((m • F) ∆ F).Finite := (hfin.smul_set).symmDiff hfin
  rw [Measure.count_apply_finite' hfin hFm, Set.ncard_eq_toFinset_card _ hfin]
  refine ENNReal.div_le_div_right ?_ _
  calc
    (((m • F) ∆ F).ncard : ℝ≥0∞) = hsd.toFinset.card := by
      rw [Set.ncard_eq_toFinset_card _ hsd]
    _ = ∑' _ : (hsd.toFinset : Set X), (1 : ℝ≥0∞) := by simp
    _ ≤ Measure.count (hsd.toFinset : Set X) := Measure.le_count_apply
    _ = Measure.count ((m • F) ∆ F) := by rw [Finite.coe_toFinset]

/-- Along any counting-measure Følner family, the real `Set.ncard` translation-boundary ratios tend
to zero without requiring `[MeasurableSingletonClass X]` or `[DecidableEq X]`. -/
@[to_additive tendsto_ncard_vadd_symmDiff_div_ncard
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
  simpa [ENNReal.toReal_div, Function.comp_def] using ENNReal.toReal_mono hlt.ne_top
    (Measure.ncard_smul_symmDiff_div_ncard_le_count_div_count hfin hFm g)

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
  rw [maxFoelner_neBot_iff_of_closure_eq_top hS]
  exact forall₂_congr fun K _ ↦ Measure.forall_exists_count_smul_symmDiff_div_lt_iff K

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
