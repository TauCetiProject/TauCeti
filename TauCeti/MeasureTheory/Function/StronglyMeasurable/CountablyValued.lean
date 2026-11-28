/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.SimpleFuncDense
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

On a set of finite measure, simple functions with values in `K` or zero approximate `f`
uniformly outside sets of arbitrarily small measure
(`MeasureTheory.AEStronglyMeasurable.exists_simpleFunc_measure_inter_dist_ge_lt`): Mathlib's
range-controlled approximants `SimpleFunc.approxOn` converge almost everywhere, hence in measure
on the set. This is the substitute for simple-function density at the exponent `∞`.

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
    [TopologicalSpace M] {A : ℕ → Set α}
    (hA : ∀ n, MeasurableSet (A n)) (hμA : ∀ n, μ (A n) < ∞) (hAd : Pairwise (Disjoint on A))
    (c : ℕ → M) : FinStronglyMeasurable (fun x ↦ ∑' n, (A n).indicator (fun _ ↦ c n) x) μ := by
  classical
  refine ⟨fun N ↦ ∑ n ∈ Finset.range N, (SimpleFunc.const α (c n)).restrict (A n),
    fun N ↦ ?_, fun x ↦ ?_⟩
  · refine (measure_mono fun x hx ↦ ?_).trans_lt
      (measure_biUnion_lt_top (Finset.range N).finite_toSet fun n _ ↦ hμA n)
    obtain ⟨n, hn, hxn⟩ := Finset.exists_ne_zero_of_sum_ne_zero (by simpa using hx)
    rw [SimpleFunc.restrict_apply _ (hA n)] at hxn
    exact mem_biUnion (Finset.mem_coe.2 hn) (mem_of_indicator_ne_zero hxn)
  · have hpart (N : ℕ) : (∑ n ∈ Finset.range N, (SimpleFunc.const α (c n)).restrict (A n)) x =
        ∑ n ∈ Finset.range N, (A n).indicator (fun _ ↦ c n) x := by
      rw [sum_apply]
      refine Finset.sum_congr rfl fun n _ ↦ ?_
      simp only [SimpleFunc.restrict_apply _ (hA n), indicator_apply, SimpleFunc.const_apply]
    simp only [hpart]
    exact (hAd.hasSum_indicator_apply _ x).tendsto_sum_nat

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
    rw [(disjoint_disjointed B).tsum_indicator_apply_of_mem _ hn, hfx]
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

/-- **Local uniform approximation by simple functions.** Let `f` be almost everywhere strongly
measurable with values almost everywhere in a set `K`, and let `B` have finite measure. For
`ε > 0` and `δ > 0` there is a simple function `φ` of finite-measure support, with values in `K`
or zero, such that `‖f - φ‖ < ε` on `B` outside a set of measure less than `δ`. -/
theorem AEStronglyMeasurable.exists_simpleFunc_measure_inter_dist_ge_lt {f : α → E}
    (hf : AEStronglyMeasurable f μ) {K : Set E} (hfK : ∀ᵐ x ∂μ, f x ∈ K)
    {B : Set α} (hB : μ B ≠ ∞) {ε : ℝ} (hε : 0 < ε) {δ : ℝ≥0∞} (hδ : δ ≠ 0) :
    ∃ φ : SimpleFunc α E, range φ ⊆ insert 0 K ∧ μ (support φ) < ∞ ∧
      μ (B ∩ {x | ε ≤ dist (f x) (φ x)}) < δ := by
  borelize E
  set B' := toMeasurable μ B
  have hB' : MeasurableSet B' := measurableSet_toMeasurable μ B
  have hμB' : μ B' ≠ ∞ := by rwa [measure_toMeasurable]
  have : IsFiniteMeasure (μ.restrict B') := isFiniteMeasure_restrict.2 hμB'
  -- Mathlib's simple approximants of a strongly measurable representative `g`, with values in
  -- `insert 0 (K ∩ range g)`, cut down to `B'`.
  obtain ⟨g, hg, hfg⟩ := hf
  let s : Set E := insert 0 (K ∩ range g)
  have : SeparableSpace s := by
    rw [show s = {0} ∪ (K ∩ range g) from insert_eq _ _]
    exact ((countable_singleton 0).isSeparable.union
      (hg.isSeparable_range.mono inter_subset_right)).separableSpace
  let F (n : ℕ) : SimpleFunc α E :=
    (SimpleFunc.approxOn g hg.measurable s 0 (mem_insert _ _) n).restrict B'
  have hF : TendstoInMeasure (μ.restrict B') (fun n ↦ F n) atTop f := by
    refine tendstoInMeasure_of_tendsto_ae (fun n ↦ (F n).aestronglyMeasurable) ?_
    filter_upwards [ae_restrict_mem hB', ae_restrict_of_ae hfK, ae_restrict_of_ae hfg]
      with x hxB hxK hfx
    simp only [F, SimpleFunc.restrict_apply _ hB', indicator_of_mem hxB, hfx]
    exact SimpleFunc.tendsto_approxOn _ _
      (subset_closure (mem_insert_of_mem _ ⟨hfx ▸ hxK, mem_range_self x⟩))
  obtain ⟨n, hn⟩ := ((tendstoInMeasure_iff_dist.1 hF ε hε).eventually
    (gt_mem_nhds (pos_iff_ne_zero.2 hδ))).exists
  refine ⟨F n, ?_, ?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    rw [SimpleFunc.restrict_apply _ hB']
    by_cases hx : x ∈ B'
    · rw [indicator_of_mem hx]
      exact insert_subset_insert inter_subset_left (SimpleFunc.approxOn_mem _ _ _ _)
    · rw [indicator_of_notMem hx (SimpleFunc.approxOn g hg.measurable s 0 (mem_insert _ _) n)]
      exact mem_insert _ _
  · refine (measure_mono ?_).trans_lt hμB'.lt_top
    rw [SimpleFunc.coe_restrict _ hB']
    exact support_indicator_subset
  · calc μ (B ∩ {x | ε ≤ dist (f x) (F n x)})
        ≤ μ ({x | ε ≤ dist (F n x) (f x)} ∩ B') := measure_mono fun x ⟨hxB, hx⟩ ↦
          ⟨by rwa [mem_ofPred_eq, dist_comm], subset_toMeasurable μ B hxB⟩
      _ = μ.restrict B' {x | ε ≤ dist (F n x) (f x)} := (Measure.restrict_apply' hB').symm
      _ < δ := hn

end MeasureTheory
