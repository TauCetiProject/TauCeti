/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Measure.WithDensityFinite

/-!
# Exhaustion arguments

This file contains two exhaustion arguments that reduce statements about an s-finite or σ-finite
measure space to statements about pieces of finite measure.

The first is an induction principle for measurable sets. Let `P` be a property of sets that holds
for every null set, is stable under countable disjoint unions of measurable sets, and is such that
every measurable set of positive measure contains a measurable subset of positive measure with
`P`. Then `P` holds for every measurable set (`MeasureTheory.Measure.induction_on_exhaustion`). On a
finite measure space, choose greedily disjoint measurable subsets of a given set `s` with `P`, each
of at least half the largest measure still available. Their measures are summable, so what remains
of `s` contains no subset of positive measure with `P` and is therefore null. For an s-finite
measure apply this to the equivalent finite measure `μ.toFinite`. The hypotheses mention only
null sets and positive sets, and these do not change.

The second exhausts a σ-finite space by sets on which a σ-finite measure `ν ≪ μ` is dominated by a
multiple of `μ` (`MeasureTheory.Measure.exists_monotone_restrict_le_smul_restrict`): there are
increasing measurable sets `S n` covering the space, of finite `μ`- and `ν`-measure, with
`ν ≤ n • μ` on `S n`. They are cut out by the sublevel sets of the Radon–Nikodym derivative
`dν/dμ`, which is finite almost everywhere.

Such exhaustions localize the Radon–Nikodým property and the representation of bounded operators
on `L¹` by vector-valued densities from finite to σ-finite measure spaces.

## Main results

* `MeasureTheory.Measure.induction_on_exhaustion`: a property of sets holding on null sets, stable
  under countable disjoint unions and found inside every set of positive measure holds for all
  measurable sets, for an s-finite measure.
* `MeasureTheory.Measure.exists_monotone_restrict_le_smul_restrict`: for σ-finite `ν ≪ μ`, an
  increasing measurable cover by sets `S n` of finite measure with `ν ≤ n • μ` on `S n`.

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces, Volume I*,
  Springer, 2016, §1.3: Lemmas 1.3.6–1.3.12 and the proof of Theorem 1.3.10.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] {P : Set α → Prop}

/-- On a finite measure space, every set `C` contains a measurable subset with `P` whose measure
is at least half the supremum of the measures of such subsets, provided the empty set has `P`. -/
private theorem exists_subset_two_mul_measure_ge (μ : Measure α) [IsFiniteMeasure μ] (hP : P ∅)
    (C : Set α) : ∃ t ⊆ C, MeasurableSet t ∧ P t ∧
      ⨆ (u : Set α) (_ : u ⊆ C ∧ MeasurableSet u ∧ P u), μ u ≤ 2 * μ t := by
  set δ := ⨆ (u : Set α) (_ : u ⊆ C ∧ MeasurableSet u ∧ P u), μ u
  rcases eq_or_ne δ 0 with h0 | h0
  · exact ⟨∅, empty_subset _, .empty, hP, by simp [h0]⟩
  have hδ : δ ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top μ univ)
    (iSup₂_le fun u _ ↦ measure_mono (subset_univ u))
  obtain ⟨t, ⟨htC, ht, hPt⟩, hlt⟩ : ∃ t, (t ⊆ C ∧ MeasurableSet t ∧ P t) ∧ δ / 2 < μ t := by
    have h := ENNReal.half_lt_self h0 hδ
    simp only [δ, lt_iSup_iff, exists_prop] at h
    exact h
  refine ⟨t, htC, ht, hPt, ?_⟩
  rw [ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_comm] at hlt
  exact hlt.le

/-- On a finite measure space, a measurable set `s` contains pairwise disjoint measurable sets
`A n` with `P` that exhaust it up to a null set, if `P` holds for the empty set and every
measurable set of positive measure contains a measurable subset of positive measure with `P`. -/
private theorem exists_disjoint_subsets_measure_diff_eq_zero (μ : Measure α) [IsFiniteMeasure μ]
    (hP : P ∅) (hpos : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ P t)
    {s : Set α} (hs : MeasurableSet s) :
    ∃ A : ℕ → Set α, (∀ n, MeasurableSet (A n)) ∧ (∀ n, A n ⊆ s) ∧
      Pairwise (Function.onFun Disjoint A) ∧ (∀ n, P (A n)) ∧ μ (s \ ⋃ n, A n) = 0 := by
  choose c hcC hcm hcP hcδ using exists_subset_two_mul_measure_ge μ hP
  -- Greedy choice: `A n` is a large subset with `P` of what remains of `s` after `A 0, …, A (n-1)`.
  let U : ℕ → Set α := fun n ↦ Nat.rec ∅ (fun _ V ↦ V ∪ c (s \ V)) n
  set A : ℕ → Set α := fun n ↦ c (s \ U n)
  have hU_succ (n : ℕ) : U (n + 1) = U n ∪ A n := rfl
  have hU_mono : Monotone U := monotone_nat_of_le_succ fun n ↦ by
    rw [hU_succ]
    exact subset_union_left
  have hA_meas (n : ℕ) : MeasurableSet (A n) := hcm _
  have hA_disj : Pairwise (Function.onFun Disjoint A) := by
    have key {k n : ℕ} (hkn : k < n) : Disjoint (A k) (A n) := by
      refine disjoint_left.2 fun x hxk hxn ↦ (hcC _ hxn).2 (hU_mono hkn ?_)
      rw [hU_succ]
      exact Or.inr hxk
    intro k n hkn
    rcases lt_or_gt_of_ne hkn with h | h
    · exact key h
    · exact (key h).symm
  refine ⟨A, hA_meas, fun n ↦ (hcC _).trans sdiff_subset, hA_disj, fun n ↦ hcP _, ?_⟩
  have hUA (n : ℕ) : U n ⊆ ⋃ k, A k := by
    induction n with
    | zero => exact empty_subset _
    | succ n ih => exact union_subset ih (subset_iUnion A n)
  -- The measures of the `A n` are summable, so they tend to `0`.
  have hA_tendsto : Filter.Tendsto (fun n ↦ 2 * μ (A n)) Filter.atTop (nhds 0) := by
    have h : Filter.Tendsto (fun n ↦ μ (A n)) Filter.atTop (nhds 0) := by
      refine ENNReal.tendsto_atTop_zero_of_tsum_ne_top ?_
      rw [← measure_iUnion hA_disj hA_meas]
      exact measure_ne_top μ _
    simpa using ENNReal.Tendsto.const_mul h (Or.inr ENNReal.ofNat_ne_top)
  -- What remains of `s` is null: otherwise it contains a set with `P` of positive measure,
  -- which was available at every step of the greedy choice.
  by_contra h
  obtain ⟨t, hts, ht, hμt, hPt⟩ := hpos _ (hs.diff (.iUnion hA_meas)) h
  have hle (n : ℕ) : μ t ≤ 2 * μ (A n) :=
    (le_iSup₂ (f := fun (u : Set α) (_ : u ⊆ s \ U n ∧ MeasurableSet u ∧ P u) ↦ μ u) t
      ⟨hts.trans (sdiff_subset_sdiff_right (hUA n)), ht, hPt⟩).trans (hcδ _)
  exact hμt (le_antisymm (ge_of_tendsto' hA_tendsto hle) bot_le)

/-- The finite measure case of `MeasureTheory.Measure.induction_on_exhaustion`. -/
private theorem induction_on_exhaustion_of_isFiniteMeasure (μ : Measure α) [IsFiniteMeasure μ]
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → P s)
    (hpos : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ P t)
    (hunion : ∀ f : ℕ → Set α, (∀ n, MeasurableSet (f n)) → Pairwise (Function.onFun Disjoint f) →
      (∀ n, P (f n)) → P (⋃ n, f n))
    {s : Set α} (hs : MeasurableSet s) : P s := by
  obtain ⟨A, hA_meas, hAs, hA_disj, hPA, hnull_rest⟩ :=
    exists_disjoint_subsets_measure_diff_eq_zero μ (hnull ∅ .empty measure_empty) hpos hs
  -- `s` is the disjoint union of the null set `s \ ⋃ n, A n` and the sets `A n`.
  let f : ℕ → Set α := fun n ↦ Nat.casesOn n (s \ ⋃ n, A n) A
  have hf : ⋃ n, f n = s := by
    rw [← union_iUnion_nat_succ]
    exact sdiff_union_of_subset (iUnion_subset hAs)
  rw [← hf]
  refine hunion f (fun n ↦ ?_) (fun m n hmn ↦ ?_) fun n ↦ ?_
  · cases n
    exacts [hs.diff (.iUnion hA_meas), hA_meas _]
  · cases m <;> cases n
    · exact absurd rfl hmn
    · exact disjoint_left.2 fun x hx hxA ↦ hx.2 (mem_iUnion_of_mem _ hxA)
    · exact disjoint_left.2 fun x hxA hx ↦ hx.2 (mem_iUnion_of_mem _ hxA)
    · exact hA_disj fun h ↦ hmn (congrArg _ h)
  · cases n
    exacts [hnull _ (hs.diff (.iUnion hA_meas)) hnull_rest, hPA _]

/-- **Exhaustion principle.** Let `μ` be an s-finite measure and `P` a property of sets that
holds for every measurable null set, holds for countable disjoint unions of measurable sets with
`P`, and such that every measurable set of positive measure contains a measurable subset of
positive measure with `P`. Then every measurable set has `P`. -/
theorem induction_on_exhaustion (μ : Measure α) [SFinite μ]
    (hnull : ∀ s, MeasurableSet s → μ s = 0 → P s)
    (hpos : ∀ s, MeasurableSet s → μ s ≠ 0 → ∃ t ⊆ s, MeasurableSet t ∧ μ t ≠ 0 ∧ P t)
    (hunion : ∀ f : ℕ → Set α, (∀ n, MeasurableSet (f n)) → Pairwise (Function.onFun Disjoint f) →
      (∀ n, P (f n)) → P (⋃ n, f n))
    {s : Set α} (hs : MeasurableSet s) : P s := by
  refine induction_on_exhaustion_of_isFiniteMeasure μ.toFinite
    (fun s hs h ↦ hnull s hs (toFinite_apply_eq_zero_iff.1 h)) (fun s hs h ↦ ?_) hunion hs
  obtain ⟨t, hts, ht, hμt, hPt⟩ := hpos s hs (mt toFinite_apply_eq_zero_iff.2 h)
  exact ⟨t, hts, ht, mt toFinite_apply_eq_zero_iff.1 hμt, hPt⟩

/-- **Exhaustion by sets of bounded density.** For σ-finite measures `ν ≪ μ` there are increasing
measurable sets `S n` covering the space, of finite `μ`- and `ν`-measure, on which `ν` is at most
`n • μ`. -/
theorem exists_monotone_restrict_le_smul_restrict {μ ν : Measure α} [SigmaFinite μ]
    [SigmaFinite ν] (hνμ : ν ≪ μ) :
    ∃ S : ℕ → Set α, Monotone S ∧ (∀ n, MeasurableSet (S n)) ∧ ⋃ n, S n = univ ∧
      (∀ n, μ (S n) < ∞) ∧ (∀ n, ν (S n) < ∞) ∧
      ∀ n : ℕ, ν.restrict (S n) ≤ (n : ℝ≥0∞) • μ.restrict (S n) := by
  -- A finite version `g` of `dν/dμ`; it agrees with `dν/dμ` `μ`-almost everywhere.
  set g : α → NNReal := fun x ↦ (ν.rnDeriv μ x).toNNReal
  have hg : Measurable g := (ν.measurable_rnDeriv μ).ennreal_toNNReal
  set S : ℕ → Set α := fun n ↦ spanningSets μ n ∩ spanningSets ν n ∩ {x | g x ≤ n}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    ((measurableSet_spanningSets μ n).inter (measurableSet_spanningSets ν n)).inter
      (measurableSet_le hg measurable_const)
  refine ⟨S, fun m n hmn ↦ ?_, hS, ?_, fun n ↦ ?_, fun n ↦ ?_, fun n ↦ ?_⟩
  · exact inter_subset_inter (inter_subset_inter (monotone_spanningSets μ hmn)
      (monotone_spanningSets ν hmn)) fun x (hx : g x ≤ m) ↦ hx.trans (Nat.cast_le.2 hmn)
  · refine eq_univ_of_forall fun x ↦ ?_
    obtain ⟨a, ha⟩ := mem_iUnion.1 (iUnion_spanningSets μ ▸ mem_univ x)
    obtain ⟨b, hb⟩ := mem_iUnion.1 (iUnion_spanningSets ν ▸ mem_univ x)
    obtain ⟨c, hc⟩ := exists_nat_ge (g x)
    refine mem_iUnion.2 ⟨max (max a b) c, ⟨⟨monotone_spanningSets μ ?_ ha,
      monotone_spanningSets ν ?_ hb⟩, hc.trans (Nat.cast_le.2 (le_max_right _ _))⟩⟩ <;> omega
  · exact (measure_mono inter_subset_left).trans_lt
      ((measure_mono inter_subset_left).trans_lt (measure_spanningSets_lt_top μ n))
  · exact (measure_mono inter_subset_left).trans_lt
      ((measure_mono inter_subset_right).trans_lt (measure_spanningSets_lt_top ν n))
  · -- On `S n` the density `dν/dμ` is `μ`-almost everywhere equal to `g ≤ n`.
    refine Measure.le_iff.2 fun t ht ↦ ?_
    have hle : ∀ᵐ x ∂μ.restrict (t ∩ S n), ν.rnDeriv μ x ≤ n := by
      filter_upwards [ae_restrict_mem (ht.inter (hS n)),
        ae_restrict_of_ae (rnDeriv_lt_top ν μ)] with x hx hfin
      rw [← ENNReal.coe_toNNReal hfin.ne]
      exact_mod_cast hx.2.2
    rw [restrict_apply ht, ← setLIntegral_rnDeriv' hνμ (ht.inter (hS n)), smul_apply,
      restrict_apply ht, smul_eq_mul, ← setLIntegral_const]
    exact lintegral_mono_ae hle

end MeasureTheory.Measure
