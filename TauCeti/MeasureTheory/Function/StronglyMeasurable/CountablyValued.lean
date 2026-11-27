/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import TauCeti.Topology.Algebra.InfiniteSum.Basic

/-!
# Uniform approximation by countably-valued functions

A finitely-valued simple function cannot approximate uniformly a bounded function whose
essential range is not totally bounded, so simple functions are not norm dense in Banach-valued
`L∞`. Countably many values suffice. Let `f` be almost everywhere finitely strongly
measurable, with values almost everywhere in a nonempty set `K`, and let `ε > 0`. Then there
are pairwise disjoint measurable sets `Aₙ` of finite measure and values `cₙ ∈ K` such that

`‖f(x) - ∑ₙ 𝟙_{Aₙ}(x) cₙ‖ < ε` for almost every `x`

(`MeasureTheory.AEFinStronglyMeasurable.exists_dist_tsum_indicator_const_lt`). The
`cₙ` are taken from a countable subset of `K` that is dense in the values of `f` in `K`, and
the pieces cut the finite-measure parts of a σ-finite support of `f` along the `ε`-balls around
these values. Taking `K` a closed ball centred at zero bounds the approximant by its radius.

On a set of finite measure only finitely many pieces matter up to small measure, which gives
uniform approximation by finitely-valued simple functions outside sets of arbitrarily small
measure (`MeasureTheory.AEStronglyMeasurable.exists_simpleFunc_measure_inter_dist_lt`). This is
the substitute for simple-function density at the exponent `∞`.

A countable sum `∑ₙ 𝟙_{Aₙ} cₙ` over disjoint measurable sets of finite measure is finitely
strongly measurable (`MeasureTheory.finStronglyMeasurable_tsum_indicator_const`).

## References

* T. Hytönen, J. van Neerven, M. Veraar and L. Weis, *Analysis in Banach Spaces*, Volume I,
  Lemma 1.2.19 and Remark 1.2.20.
-/

public section

open Filter Function Set TopologicalSpace
open scoped ENNReal Topology

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A countable sum `∑ₙ 𝟙_{Aₙ} cₙ` over pairwise disjoint measurable sets of finite measure is
finitely strongly measurable: its partial sums are simple functions of finite-measure support
converging pointwise. -/
theorem finStronglyMeasurable_tsum_indicator_const {M : Type*} [AddCommMonoid M]
    [TopologicalSpace M] [T2Space M] {A : ℕ → Set α}
    (hA : ∀ n, MeasurableSet (A n)) (hμA : ∀ n, μ (A n) < ∞) (hAd : Pairwise (Disjoint on A))
    (c : ℕ → M) : FinStronglyMeasurable (fun x ↦ ∑' n, (A n).indicator (fun _ ↦ c n) x) μ := by
  classical
  refine ⟨fun N ↦ ∑ n ∈ Finset.range N, (SimpleFunc.const α (c n)).restrict (A n),
    fun N ↦ ?_, fun x ↦ ?_⟩
  · refine (measure_mono fun x hx ↦ ?_).trans_lt ((measure_biUnion_finset_le
      (Finset.range N) A).trans_lt (ENNReal.sum_lt_top.2 fun n _ ↦ hμA n))
    obtain ⟨n, hn, hxn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by simpa using hx)
    rw [SimpleFunc.restrict_apply _ (hA n)] at hxn
    exact mem_biUnion hn (mem_of_indicator_ne_zero hxn)
  · have hsum : HasSum (fun n ↦ (A n).indicator (fun _ ↦ c n) x)
        (∑' n, (A n).indicator (fun _ ↦ c n) x) := by
      by_cases hx : ∃ n, x ∈ A n
      · obtain ⟨n, hn⟩ := hx
        rw [TauCeti.tsum_indicator_apply_of_mem hAd _ hn]
        exact TauCeti.hasSum_indicator_apply_of_mem hAd _ hn
      · simp only [not_exists] at hx
        simp [indicator_of_notMem (hx _)]
    simpa [SimpleFunc.restrict_apply _ (hA _), ← Function.const_def] using hsum.tendsto_sum_nat

variable {E : Type*} [NormedAddCommGroup E]

/-- **Uniform approximation by countably-valued functions.** An almost everywhere finitely
strongly measurable function `f`, with values almost everywhere in a nonempty set `K`, is
within `ε` almost everywhere of a countable sum `∑ₙ 𝟙_{Aₙ} cₙ` over pairwise disjoint
measurable sets `Aₙ` of finite measure, with all `cₙ ∈ K`. -/
theorem AEFinStronglyMeasurable.exists_dist_tsum_indicator_const_lt {f : α → E}
    (hf : AEFinStronglyMeasurable f μ) {K : Set E} (hK : K.Nonempty)
    (hfK : ∀ᵐ x ∂μ, f x ∈ K) {ε : ℝ} (hε : 0 < ε) :
    ∃ (A : ℕ → Set α) (c : ℕ → E), (∀ n, MeasurableSet (A n)) ∧ (∀ n, μ (A n) < ∞) ∧
      Pairwise (Disjoint on A) ∧ (∀ n, c n ∈ K) ∧
      ∀ᵐ x ∂μ, dist (f x) (∑' n, (A n).indicator (fun _ ↦ c n) x) < ε := by
  classical
  -- A finitely strongly measurable representative `g`, vanishing off a σ-finite set `t`.
  obtain ⟨g, hg, hfg⟩ := hf
  obtain ⟨t, ht, hgt, htσ⟩ := hg.exists_set_sigmaFinite
  -- Values `d j ∈ K`, dense in the values of `g` lying in `K`.
  obtain ⟨D, hDK, hDc, hD⟩ := (hg.stronglyMeasurable.isSeparable_range.mono
    (inter_subset_right : K ∩ range g ⊆ range g)).exists_countable_dense_subset
  obtain ⟨k₀, hk₀⟩ := hK
  obtain ⟨d, hd⟩ := (hDc.insert k₀).exists_eq_range (insert_nonempty _ _)
  have hdK (j : ℕ) : d j ∈ K := by
    rcases (hd ▸ mem_range_self j : d j ∈ insert k₀ D) with h | h
    · exact h ▸ hk₀
    · exact (hDK h).1
  -- Pieces `B (k, j)`: the `k`-th finite-measure part of `t` near the value `d j`.
  let B (n : ℕ) : Set α :=
    (spanningSets (μ.restrict t) n.unpair.1 ∩ t) ∩ {x | dist (g x) (d n.unpair.2) < ε}
  have hB (n : ℕ) : MeasurableSet (B n) :=
    ((measurableSet_spanningSets _ _).inter ht).inter <| measurableSet_lt
      (hg.stronglyMeasurable.dist stronglyMeasurable_const).measurable measurable_const
  have hμB (n : ℕ) : μ (B n) < ∞ := by
    refine (measure_mono inter_subset_left).trans_lt ?_
    rw [← Measure.restrict_apply' ht]
    exact measure_spanningSets_lt_top _ _
  refine ⟨disjointed B, fun n ↦ d n.unpair.2, MeasurableSet.disjointed hB,
    fun n ↦ (measure_mono (disjointed_subset B n)).trans_lt (hμB n), disjoint_disjointed B,
    fun n ↦ hdK _, ?_⟩
  filter_upwards [hfg, hfK] with x hfx hxK
  by_cases hx : ∃ n, x ∈ disjointed B n
  · obtain ⟨n, hn⟩ := hx
    rw [TauCeti.tsum_indicator_apply_of_mem (disjoint_disjointed B) _ hn, hfx]
    exact (disjointed_subset B n hn).2
  · simp only [not_exists] at hx
    -- A point of `t` with a value in `K` lies in some piece, so `x ∉ t` and `f x = g x = 0`.
    have hxt : x ∉ t := by
      intro hxt
      obtain ⟨y, hyD, hy⟩ := Metric.mem_closure_iff.1
        (hD ⟨by rwa [← hfx], mem_range_self x⟩) ε hε
      obtain ⟨j, rfl⟩ : y ∈ range d := hd ▸ mem_insert_of_mem k₀ hyD
      obtain ⟨k, hk⟩ := mem_iUnion.1 ((iUnion_spanningSets (μ.restrict t)).symm ▸ mem_univ x)
      have hxB : x ∈ ⋃ n, B n := mem_iUnion.2 ⟨Nat.pair k j, by simpa [B] using ⟨⟨hk, hxt⟩, hy⟩⟩
      rw [← iUnion_disjointed] at hxB
      obtain ⟨n, hn⟩ := mem_iUnion.1 hxB
      exact hx n hn
    simpa [indicator_of_notMem (hx _), hfx, hgt x hxt] using hε

/-- Truncating a countable sum `∑ₙ 𝟙_{Aₙ} cₙ` to `n < N` and to a measurable set `B` gives a
simple function with values among the `cₙ` and zero, supported in `B`, which agrees with the
countable sum at the points of `B` outside the tail `⋃ n ≥ N, Aₙ`. -/
private lemma exists_simpleFunc_eq_tsum_indicator_const {A : ℕ → Set α}
    (hA : ∀ n, MeasurableSet (A n)) (hAd : Pairwise (Disjoint on A)) (c : ℕ → E) {B : Set α}
    (hB : MeasurableSet B) (N : ℕ) :
    ∃ φ : SimpleFunc α E, range φ ⊆ insert 0 (range c) ∧ support φ ⊆ B ∧
      ∀ x ∈ B, (∀ n, N ≤ n → x ∉ A n) → φ x = ∑' n, (A n).indicator (fun _ ↦ c n) x := by
  classical
  let φ : SimpleFunc α E := ∑ n ∈ Finset.range N, (SimpleFunc.const α (c n)).restrict (A n ∩ B)
  have hφ (x : α) : φ x = ∑ n ∈ Finset.range N, (A n ∩ B).indicator (fun _ ↦ c n) x := by
    simp [φ, SimpleFunc.restrict_apply _ ((hA _).inter hB), ← Function.const_def]
  -- At a point of `B` in the `n`-th piece, `φ` takes the value `c n` if `n < N`, else `0`.
  have hφ_mem {x : α} {n : ℕ} (hxB : x ∈ B) (hxn : x ∈ A n) :
      φ x = if n < N then c n else 0 := by
    rw [hφ]
    split_ifs with hn
    · rw [Finset.sum_eq_single_of_mem n (Finset.mem_range.2 hn) fun m _ hmn ↦
        indicator_of_notMem (fun (hxm : x ∈ A m ∩ B) ↦ disjoint_left.1 (hAd hmn) hxm.1 hxn) _]
      exact indicator_of_mem (show x ∈ A n ∩ B from ⟨hxn, hxB⟩) _
    · refine Finset.sum_eq_zero fun m hm ↦ indicator_of_notMem (fun (hxm : x ∈ A m ∩ B) ↦ ?_) _
      have hmn : m ≠ n := fun h ↦ hn (h ▸ Finset.mem_range.1 hm)
      exact disjoint_left.1 (hAd hmn) hxm.1 hxn
  have hφ_notMem {x : α} (hx : ∀ n, x ∈ B → x ∉ A n) : φ x = 0 := by
    rw [hφ]
    exact Finset.sum_eq_zero fun m _ ↦
      indicator_of_notMem (fun (hxm : x ∈ A m ∩ B) ↦ hx m hxm.2 hxm.1) _
  refine ⟨φ, ?_, fun x hx ↦ by_contra fun hxB ↦ hx (hφ_notMem fun _ h ↦ (hxB h).elim), ?_⟩
  · rintro _ ⟨x, rfl⟩
    by_cases hx : ∃ n, x ∈ B ∧ x ∈ A n
    · obtain ⟨n, hxB, hxn⟩ := hx
      rw [hφ_mem hxB hxn]
      split_ifs
      exacts [mem_insert_of_mem _ (mem_range_self n), mem_insert _ _]
    · simp only [not_exists, not_and] at hx
      exact hφ_notMem hx ▸ mem_insert _ _
  intro x hxB hxN
  by_cases hxA : ∃ n, x ∈ A n
  · obtain ⟨n, hn⟩ := hxA
    have hnN : n < N := not_le.1 fun h ↦ hxN n h hn
    simp [hφ_mem hxB hn, hnN, TauCeti.tsum_indicator_apply_of_mem hAd (fun m _ ↦ c m) hn]
  · simp only [not_exists] at hxA
    simp [hφ_notMem fun n _ ↦ hxA n, indicator_of_notMem (hxA _)]

/-- **Local uniform approximation by simple functions.** Let `f` be almost everywhere strongly
measurable with values almost everywhere in a nonempty set `K`, and let `B` have finite measure.
For `ε > 0` and `δ > 0` there is a simple function `φ` of finite-measure support, with values in
`K` or zero, such that `‖f - φ‖ < ε` on `B` outside a set of measure less than `δ`. -/
theorem AEStronglyMeasurable.exists_simpleFunc_measure_inter_dist_lt {f : α → E}
    (hf : AEStronglyMeasurable f μ) {K : Set E} (hK : K.Nonempty) (hfK : ∀ᵐ x ∂μ, f x ∈ K)
    {B : Set α} (hB : μ B ≠ ∞) {ε : ℝ} (hε : 0 < ε) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ φ : SimpleFunc α E, range φ ⊆ insert 0 K ∧ μ (support φ) < ∞ ∧
      μ (B ∩ {x | ε ≤ dist (f x) (φ x)}) < δ := by
  set B' := toMeasurable μ B
  have hB' : MeasurableSet B' := measurableSet_toMeasurable μ B
  have hμB' : μ B' ≠ ∞ := by rwa [measure_toMeasurable]
  have : IsFiniteMeasure (μ.restrict B') := isFiniteMeasure_restrict.2 hμB'
  have hfB : AEStronglyMeasurable f (μ.restrict B') := hf.restrict
  -- A countably-valued approximant for the finite measure `μ.restrict B'`.
  obtain ⟨A, c, hA, -, hAd, hcK, hae⟩ := AEFinStronglyMeasurable.exists_dist_tsum_indicator_const_lt
    ⟨_, hfB.stronglyMeasurable_mk.finStronglyMeasurable _, hfB.ae_eq_mk⟩ hK
    (ae_restrict_of_ae hfK) hε
  -- Only finitely many pieces carry measure at least `δ` in `B'`.
  obtain ⟨N, hN⟩ := ((tendsto_measure_biUnion_Ici_zero_of_pairwise_disjoint
    (μ := μ.restrict B') (fun n ↦ (hA n).nullMeasurableSet) hAd).eventually
      (gt_mem_nhds (pos_iff_ne_zero.2 hδ))).exists
  obtain ⟨φ, hφK, hφB', hφ⟩ := exists_simpleFunc_eq_tsum_indicator_const hA hAd c hB' N
  refine ⟨φ, hφK.trans (insert_subset_insert (range_subset_iff.2 hcK)),
    (measure_mono hφB').trans_lt hμB'.lt_top, ?_⟩
  -- Off the tail `⋃ n ≥ N, A n`, `φ` agrees with the countable approximant on `B'`.
  refine (measure_mono (inter_subset_inter_left _ (subset_toMeasurable μ B))).trans_lt
    (lt_of_le_of_lt ?_ hN)
  rw [inter_comm, ← Measure.restrict_apply' hB']
  refine measure_mono_ae ?_
  filter_upwards [hae, ae_restrict_mem hB'] with x hx hxB hxε
  by_contra hxN
  simp only [mem_iUnion, not_exists] at hxN
  exact not_lt.2 hxε (hφ x hxB hxN ▸ hx)

end MeasureTheory
