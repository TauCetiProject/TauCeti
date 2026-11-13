/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Daniel Lyng, The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Constructions.Polish.Basic
public import Mathlib.MeasureTheory.Measure.NullMeasurable

import Mathlib.Tactic.Positivity
import TauCeti.Topology.Instances.NatNat

/-!
# Choquet's capacitability theorem

This file defines Choquet capacities taking values in `ℝ≥0∞` and proves Choquet's capacitability
theorem: on a Hausdorff space, the capacity of every analytic set is the supremum of the
capacities of its compact subsets.

A set function `I : Set X → ℝ≥0∞` is a Choquet capacity (`TauCeti.IsChoquetCapacity`) when it is
monotone, upward continuous along arbitrary increasing sequences of sets, and downward continuous
along decreasing sequences of closed sets. On a compact space, downward continuity along closed
sets reduces to downward continuity along compact sets
(`TauCeti.IsChoquetCapacity.of_compactSpace`).
On a non-compact Hausdorff space, downward continuity along closed sets is genuinely stronger and
is required for inner compact approximation: on Baire space `ℕ → ℕ`, the `{0, 1}`-valued indicator
of not being contained in a countable union of compact sets is monotone, upward continuous on all
increasing sequences, and zero on every compact set, yet assigns value `1` to `Set.univ`.

No finiteness or vanishing-on-empty hypothesis is imposed on `I`: the coordinate-bounding recursion
in Baire space works directly with strict `ℝ≥0` lower bounds below `I (Set.range f)` via density of
`ℝ≥0` in `ℝ≥0∞`, so capacities taking the value `∞` are covered uniformly. Neither metrizability
nor separability of `X` is needed, since `TauCeti.iInter_closure_image_subset_image_Iic` holds in
every Hausdorff space.

## Main definitions

* `TauCeti.IsChoquetCapacity`: monotone `ℝ≥0∞`-valued set functions continuous upward on arbitrary
  increasing sequences and downward on decreasing sequences of closed sets.

## Main results

* `TauCeti.IsChoquetCapacity.of_compactSpace`: on a compact space, downward continuity on
  decreasing sequences of compact sets suffices.
* `TauCeti.IsChoquetCapacity.measure`: every finite Borel-compatible measure is a Choquet capacity.
* `TauCeti.IsChoquetCapacity.exists_isCompact_subset_lt`: strict inner compact approximation of an
  analytic set in a Hausdorff space.
* `TauCeti.IsChoquetCapacity.analyticSet_eq_biSup_isCompact`: **Choquet's capacitability theorem**
  expressing `I S` as the supremum of `I K` over compact `K ⊆ S` for every analytic set `S`.

## Provenance

The coordinate-bounding recursion adapts the finite-measure universal-measurability argument from
Daniel Lyng's Apache-2.0 Econlib formalization
(`Econlib/Math/MeasureTheory/AnalyticNullMeasurable.lean`, commit
`003655ccf010cdf44c4f67d6675167b54ce0e9df`) to arbitrary `ℝ≥0∞`-valued Choquet capacities in
Hausdorff spaces, using the ultrafilter closure lemma
`TauCeti.iInter_closure_image_subset_image_Iic` from `TauCeti.Topology.Instances.NatNat`.

## References

* G. Choquet, *Theory of capacities*, Ann. Inst. Fourier 5 (1954), 131--295.
* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer-Verlag, 1995, §30.B.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

/-- A **Choquet capacity** on a topological space `X` is a monotone set function `I : Set X → ℝ≥0∞`
that is continuous upward along arbitrary increasing sequences of sets and continuous downward along
decreasing sequences of closed sets. -/
structure IsChoquetCapacity {X : Type*} [TopologicalSpace X] (I : Set X → ℝ≥0∞) : Prop where
  /-- Monotonicity with respect to set inclusion. -/
  mono : Monotone I
  /-- Upward continuity along arbitrary increasing sequences of subsets. -/
  iUnion_eq : ∀ A : ℕ → Set X, Monotone A → I (⋃ n, A n) = ⨆ n, I (A n)
  /-- Downward continuity along decreasing sequences of closed subsets. -/
  iInter_isClosed_eq :
    ∀ F : ℕ → Set X, (∀ n, IsClosed (F n)) → Antitone F → I (⋂ n, F n) = ⨅ n, I (F n)

section Basic

variable {X : Type*} [TopologicalSpace X] {I : Set X → ℝ≥0∞}

/-- Explicit characterization of `TauCeti.IsChoquetCapacity` without unfolding the structure. -/
theorem isChoquetCapacity_iff :
    IsChoquetCapacity I ↔
      Monotone I ∧
        (∀ A : ℕ → Set X, Monotone A → I (⋃ n, A n) = ⨆ n, I (A n)) ∧
        (∀ F : ℕ → Set X, (∀ n, IsClosed (F n)) → Antitone F → I (⋂ n, F n) = ⨅ n, I (F n)) :=
  ⟨fun h ↦ ⟨h.mono, h.iUnion_eq, h.iInter_isClosed_eq⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ⟨h₁, h₂, h₃⟩⟩

/-- On a compact space every closed set is compact, so downward continuity along decreasing
sequences of compact sets suffices for `TauCeti.IsChoquetCapacity`. -/
theorem IsChoquetCapacity.of_compactSpace [CompactSpace X] (hmono : Monotone I)
    (hiUnion : ∀ A : ℕ → Set X, Monotone A → I (⋃ n, A n) = ⨆ n, I (A n))
    (hiInter : ∀ K : ℕ → Set X, (∀ n, IsCompact (K n)) → Antitone K →
      I (⋂ n, K n) = ⨅ n, I (K n)) :
    IsChoquetCapacity I :=
  ⟨hmono, hiUnion, fun F hF hanti ↦ hiInter F (fun n ↦ (hF n).isCompact) hanti⟩

/-- In a Hausdorff space every compact set is closed, so a Choquet capacity is downward continuous
along decreasing sequences of compact sets. -/
theorem IsChoquetCapacity.iInter_isCompact_eq [T2Space X] (hI : IsChoquetCapacity I)
    {K : ℕ → Set X} (hK : ∀ n, IsCompact (K n)) (hanti : Antitone K) :
    I (⋂ n, K n) = ⨅ n, I (K n) :=
  hI.iInter_isClosed_eq K (fun n ↦ (hK n).isClosed) hanti

/-- Every constant set function is a Choquet capacity. -/
@[simp]
theorem isChoquetCapacity_const (c : ℝ≥0∞) : IsChoquetCapacity (fun _ : Set X ↦ c) :=
  ⟨monotone_const, fun _ _ ↦ (iSup_const (a := c)).symm, fun _ _ _ ↦ (iInf_const (a := c)).symm⟩

/-- Every finite measure on a measurable space containing the open sets is a Choquet capacity. -/
theorem IsChoquetCapacity.measure [MeasurableSpace X] [OpensMeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] : IsChoquetCapacity μ where
  mono _ _ h := measure_mono h
  iUnion_eq _ hA := hA.measure_iUnion
  iInter_isClosed_eq _ hF hanti :=
    Directed.measure_iInter (fun n ↦ (hF n).measurableSet.nullMeasurableSet) hanti.directed_ge
      ⟨0, measure_ne_top μ _⟩

end Basic

/-! ### Baire-space coordinate bounding and capacitability -/

section Hausdorff

variable {X : Type*} [TopologicalSpace X] [T2Space X] {I : Set X → ℝ≥0∞}

/-- Every strict lower bound on the capacity of a continuous image of Baire space into a Hausdorff
space is witnessed by a compact subset of that image. -/
theorem IsChoquetCapacity.exists_isCompact_subset_range_lt (hI : IsChoquetCapacity I)
    {f : (ℕ → ℕ) → X} (hf : Continuous f) {r : ℝ≥0∞} (hr : r < I (range f)) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ range f ∧ r < I K := by
  obtain ⟨p, hrp, hp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hr
  obtain ⟨q, hpq, hq⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1 hp
  set δ : ℝ≥0 := q - p
  have hδ : 0 < δ := tsub_pos_of_lt (ENNReal.coe_lt_coe.1 hpq)
  let a : ℕ → ℝ≥0 := fun n ↦ p + δ / 2 ^ n
  have ha_lt (n : ℕ) : ((a (n + 1) : ℝ≥0) : ℝ≥0∞) < (a n : ℝ≥0) := by
    refine ENNReal.coe_lt_coe.2 (add_lt_add_right ?_ p)
    exact div_lt_div_of_pos_left hδ (by positivity)
      (pow_lt_pow_right₀ one_lt_two (Nat.lt_succ_self n))
  -- At stage `n`, bound the `n`th coordinate while keeping the capacity above `a (n + 1)`.
  have hstep (n : ℕ) (T : Set (ℕ → ℕ)) :
      ∃ M : ℕ, ((a n : ℝ≥0) : ℝ≥0∞) ≤ I (f '' T) →
        ((a (n + 1) : ℝ≥0) : ℝ≥0∞) ≤ I (f '' (T ∩ {β | β n ≤ M})) := by
    by_cases hT : ((a n : ℝ≥0) : ℝ≥0∞) ≤ I (f '' T)
    · have hmono : Monotone fun M : ℕ ↦ f '' (T ∩ {β | β n ≤ M}) := fun M M' hMM' ↦
        image_mono (inter_subset_inter_right _ fun _ hβ ↦ hβ.trans hMM')
      have hunion : ⋃ M : ℕ, f '' (T ∩ {β | β n ≤ M}) = f '' T := by
        rw [← image_iUnion]
        congr 1
        ext β
        simp only [mem_iUnion, mem_inter_iff, mem_ofPred_eq]
        exact ⟨fun ⟨_, hβ, _⟩ ↦ hβ, fun hβ ↦ ⟨β n, hβ, le_rfl⟩⟩
      have hsup : ((a (n + 1) : ℝ≥0) : ℝ≥0∞) < ⨆ M, I (f '' (T ∩ {β | β n ≤ M})) := by
        rw [← hI.iUnion_eq _ hmono, hunion]
        exact (ha_lt n).trans_le hT
      obtain ⟨M, hM⟩ := lt_iSup_iff.1 hsup
      exact ⟨M, fun _ ↦ hM.le⟩
    · exact ⟨0, fun h ↦ (hT h).elim⟩
  choose Mof hMof using hstep
  let F : ℕ → Set (ℕ → ℕ) :=
    fun n ↦ Nat.rec univ (fun n Fn ↦ Fn ∩ {β | β n ≤ Mof n Fn}) n
  let N : ℕ → ℕ := fun n ↦ Mof n (F n)
  have hF_succ (n : ℕ) : F (n + 1) = F n ∩ {β | β n ≤ N n} := rfl
  have hF_eq : ∀ n, F n = {β | ∀ k < n, β k ≤ N k} := by
    intro n
    induction n with
    | zero => ext β; simp [F]
    | succ n ih =>
      rw [hF_succ, ih]
      ext β
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun ⟨hpre, hn⟩ k hk ↦ (Nat.lt_succ_iff_lt_or_eq.mp hk).elim (hpre k) (· ▸ hn),
        fun h ↦ ⟨fun k hk ↦ h k (hk.trans (Nat.lt_succ_self n)), h n (Nat.lt_succ_self n)⟩⟩
  have hinv : ∀ n, ((a n : ℝ≥0) : ℝ≥0∞) ≤ I (f '' F n) := by
    intro n
    induction n with
    | zero =>
      have ha0 : a 0 = q := by
        simp [a, δ, add_tsub_cancel_of_le (ENNReal.coe_lt_coe.1 hpq).le]
      simpa [F, ha0] using hq.le
    | succ n ih => exact hMof n (F n) ih
  have hC_compact : IsCompact (Iic N) := by
    have : Iic N = univ.pi fun k ↦ Iic (N k) := by
      ext β; simp [Pi.le_def]
    rw [this]
    exact isCompact_univ_pi fun k ↦ (finite_Iic (N k)).isCompact
  refine ⟨f '' Iic N, hC_compact.image hf, image_subset_range f _, ?_⟩
  have hD_anti : Antitone fun n ↦ closure (f '' F n) :=
    antitone_nat_of_succ_le fun n ↦
      closure_mono (image_mono (by rw [hF_succ]; exact inter_subset_left))
  have hsub : ⋂ n, closure (f '' F n) ⊆ f '' Iic N := by
    simpa only [← hF_eq] using iInter_closure_image_subset_image_Iic hf N
  have hp_le : (p : ℝ≥0∞) ≤ I (f '' Iic N) := by
    calc
      (p : ℝ≥0∞) ≤ ⨅ n, I (closure (f '' F n)) :=
        le_iInf fun n ↦ (ENNReal.coe_le_coe.2 le_self_add).trans <|
          (hinv n).trans (hI.mono subset_closure)
      _ = I (⋂ n, closure (f '' F n)) :=
        (hI.iInter_isClosed_eq _ (fun _ ↦ isClosed_closure) hD_anti).symm
      _ ≤ I (f '' Iic N) := hI.mono hsub
  exact hrp.trans_le hp_le

/-- **Strict inner compact approximation of analytic sets.** In a Hausdorff space, every value
strictly below the Choquet capacity of an analytic set is exceeded on a compact subset. -/
theorem IsChoquetCapacity.exists_isCompact_subset_lt (hI : IsChoquetCapacity I)
    {S : Set X} (hS : AnalyticSet S) {r : ℝ≥0∞} (hr : r < I S) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ S ∧ r < I K := by
  obtain ⟨Z, _, _, f, hf_cont, rfl⟩ := analyticSet_iff_exists_polishSpace_range.mp hS
  rcases isEmpty_or_nonempty Z with _ | _
  · rw [range_eq_empty] at hr ⊢
    exact ⟨∅, isCompact_empty, Subset.rfl, hr⟩
  · obtain ⟨g, hg, hsurj⟩ := PolishSpace.exists_nat_nat_continuous_surjective Z
    rw [← hsurj.range_comp f] at hr ⊢
    exact hI.exists_isCompact_subset_range_lt (hf_cont.comp hg) hr

/-- **Choquet's capacitability theorem.** On a Hausdorff space, the capacity of every analytic set
equals the supremum of the capacities of its compact subsets. -/
theorem IsChoquetCapacity.analyticSet_eq_biSup_isCompact (hI : IsChoquetCapacity I)
    {S : Set X} (hS : AnalyticSet S) :
    I S = ⨆ (K : Set X) (_ : IsCompact K) (_ : K ⊆ S), I K := by
  refine le_antisymm (le_of_forall_lt fun r hr ↦ ?_)
    (iSup₂_le fun K _ ↦ iSup_le fun hKS ↦ hI.mono hKS)
  obtain ⟨K, hKc, hKS, hrK⟩ := hI.exists_isCompact_subset_lt hS hr
  exact hrK.trans_le (le_iSup₂_of_le K hKc (le_iSup_of_le hKS le_rfl))

/-- Quantitative additive-slack inner compact approximation of an analytic set of finite Choquet
capacity in a Hausdorff space. -/
theorem IsChoquetCapacity.exists_isCompact_subset_le_add (hI : IsChoquetCapacity I)
    {S : Set X} (hS : AnalyticSet S) (hfin : I S ≠ ∞) {ε : ℝ≥0∞} (hε : ε ≠ 0) :
    ∃ K : Set X, IsCompact K ∧ K ⊆ S ∧ I S ≤ I K + ε := by
  rcases le_or_gt (I S) ε with hle | hgt
  · exact ⟨∅, isCompact_empty, empty_subset S, hle.trans le_add_self⟩
  have hS0 : I S ≠ 0 := (pos_of_gt hgt).ne'
  obtain ⟨K, hKc, hKS, hlt⟩ :=
    hI.exists_isCompact_subset_lt hS (ENNReal.sub_lt_self hfin hS0 hε)
  exact ⟨K, hKc, hKS, tsub_le_iff_right.mp hlt.le⟩

end Hausdorff

end TauCeti
