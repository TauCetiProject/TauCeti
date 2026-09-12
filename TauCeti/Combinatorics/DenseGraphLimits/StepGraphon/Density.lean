/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Approximating a graphon by a finite weighted graph

Frieze--Kannan weak regularity approximates a graphon in **cut norm** by the block averages of a
measurable finite partition.  This file turns that into an approximation in **cut distance** by a
finite object -- the block matrix of the approximating step graphon, read as a graphon on the
discrete probability space of its blocks -- and then pushes both weightings of that finite object
onto a grid, so that finitely many candidates remain.

The cut distance never increases along a measure-preserving pullback (`cutDist_comap_right`), and a
step graphon *is* the pullback of its block matrix along the part-index map, so a step graphon and
its finite matrix are at cut distance zero.  Step graphons are therefore dense in the cut metric,
and so are finite weighted graphs on a vertex set whose size depends only on the accuracy.

The two grids are handled quite differently.  **Edge weights** are rounded pointwise: the difference
of the two kernels is bounded by the mesh, and so is the cut norm.  **Vertex weights** cannot be
rounded pointwise -- they have to keep summing to one -- so all but one of them are rounded down and
the remaining vertex absorbs the slack.  Comparing the two weightings then needs a coupling of them,
and the one used here keeps the matched mass on the diagonal, where the overlaid difference
vanishes, and sends the slack to the absorbing vertex; the cost is twice the transferred mass.

## Main definitions

* `TauCeti.DenseGraphLimits.gridValue` / `TauCeti.DenseGraphLimits.gridIndex` -- the grid of
  multiples of `1 / (N + 1)` in `[0, 1]`, and rounding down onto it;
* `TauCeti.DenseGraphLimits.gridWeightMeasure` -- the probability measure on `Fin n` whose weights
  are multiples of `1 / N`.

## Main results

* `TauCeti.DenseGraphLimits.exists_stepGraphon_cutDist_le` -- every graphon is within `ε` in cut
  distance of a step graphon on a measurable finite partition with at most `4 ^ (⌈1/ε²⌉ + 1)` parts;
* `TauCeti.DenseGraphLimits.exists_ofMatrix_cutDist_le` -- every graphon is within `ε` in cut
  distance of a finite weighted graph on any vertex set of size at least `4 ^ (⌈1/ε²⌉ + 1)`;
* `TauCeti.DenseGraphLimits.exists_gridValue_cutDist_le` -- the edge weights can be taken on the
  grid of multiples of `1 / (N + 1)`, at a cost of `1 / (N + 1)`;
* `TauCeti.DenseGraphLimits.cutDist_ofMatrix_le_two_mul_sum_tsub` -- transferring vertex weight onto
  one designated vertex costs at most twice the transferred mass;
* `TauCeti.DenseGraphLimits.exists_gridWeightMeasure_cutDist_le` -- the vertex weights can be taken
  on the grid of multiples of `1 / N`, at a cost of `2 n / N`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2 --
  weighted graphs are dense in the space of graphons.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- **Step graphons are dense in the cut metric**, with the Frieze--Kannan part count: every
graphon is within `ε` in cut distance of a step graphon on a measurable finite partition with at
most `4 ^ (⌈1 / ε²⌉ + 1)` parts. -/
theorem exists_stepGraphon_cutDist_le (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p)
      (val : P.parts → P.parts → Set.Icc (0 : ℝ) 1) (hsymm : ∀ p q, val p q = val q p),
      P.parts.card ≤ 4 ^ (Nat.ceil (1 / ε ^ 2) + 1) ∧
        cutDist W (stepGraphon (μ := μ) P hP val hsymm) ≤ ε := by
  obtain ⟨P, hP, hcard, happrox⟩ := weak_regularity_frieze_kannan μ W hε
  refine ⟨P, hP, blockAverage P W, blockAverage_comm P W, hcard, ?_⟩
  rw [← stepGraphonAvg_eq_stepGraphon]
  exact (cutDist_le_cutNorm_sub W _).trans happrox

/-- **Every graphon is within `ε` in cut distance of a finite weighted graph**, on any vertex set
of size at least the Frieze--Kannan bound `4 ^ (⌈1 / ε²⌉ + 1)`: the block matrix of a Frieze--Kannan
approximation, carrying the block measures as vertex weights.

The vertex weights are the pushforward of `μ` along the block-index map `g`, so they are the
measures of the blocks; vertices beyond the blocks carry weight zero.  Allowing any large enough
vertex set, rather than exactly the number of blocks, keeps the carrier of the approximation
independent of the graphon. -/
theorem exists_ofMatrix_cutDist_le (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) {n : ℕ}
    (hn : 4 ^ (Nat.ceil (1 / ε ^ 2) + 1) ≤ n) :
    ∃ (g : Ω → Fin n) (_hg : Measurable g) (b : Fin n → Fin n → Set.Icc (0 : ℝ) 1)
      (hb : ∀ i j, b i j = b j i), cutDist W (Graphon.ofMatrix (μ.map g) b hb) ≤ ε := by
  obtain ⟨P, hP, hcard, happrox⟩ := weak_regularity_frieze_kannan μ W hε
  let _ : MeasurableSpace P.parts := ⊤
  obtain ⟨e⟩ : Nonempty (P.parts ↪ Fin n) :=
    Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe, Fintype.card_fin] using hcard.trans hn)
  have hg : Measurable fun x => e (P.indexedPartition.index x) :=
    Measurable.of_discrete.comp (Finpartition.measurable_indexedPartition_index P hP)
  have hmp : MeasurePreserving (fun x => e (P.indexedPartition.index x)) μ
      (μ.map fun x => e (P.indexedPartition.index x)) := ⟨hg, rfl⟩
  -- The block averages only depend on the two block indices, so the approximating step graphon
  -- factors through the finitely many blocks.
  have hfac : ∀ x y x' y', e (P.indexedPartition.index x) = e (P.indexedPartition.index x') →
      e (P.indexedPartition.index y) = e (P.indexedPartition.index y') →
      stepGraphonAvg (μ := μ) P hP W x y = stepGraphonAvg (μ := μ) P hP W x' y' := by
    intro x y x' y' hx hy
    rw [stepGraphonAvg_apply P hP W (P.indexedPartition.mem_index x)
        (P.indexedPartition.mem_index y),
      stepGraphonAvg_apply P hP W (P.indexedPartition.mem_index x')
        (P.indexedPartition.mem_index y'), e.injective hx, e.injective hy]
  obtain ⟨b, hb, hmodel⟩ :=
    exists_ofMatrix_eq_comap_of_factorsThrough (ν := μ.map fun x => e (P.indexedPartition.index x))
      (stepGraphonAvg (μ := μ) P hP W) hmp.measurable hfac
  refine ⟨_, hg, b, hb, ?_⟩
  rw [← cutDist_comap_right W (Graphon.ofMatrix _ b hb) hmp, ← hmodel]
  exact (cutDist_le_cutNorm_sub W _).trans happrox


section Grid

variable {κ : Type*} [MeasurableSpace κ] [Countable κ] [MeasurableSingletonClass κ]

/-- The point `k / (N + 1)` of `[0, 1]`.  As `k` runs over `Fin (N + 2)` these are the `N + 2`
multiples of `1 / (N + 1)` in `[0, 1]`, a grid of mesh `1 / (N + 1)`. -/
def gridValue (N : ℕ) (k : Fin (N + 2)) : Set.Icc (0 : ℝ) 1 :=
  ⟨(k : ℕ) / ((N : ℝ) + 1), by
    refine ⟨by positivity, ?_⟩
    rw [div_le_one (by positivity)]
    exact_mod_cast Nat.lt_succ_iff.mp k.isLt⟩

@[simp]
theorem gridValue_coe (N : ℕ) (k : Fin (N + 2)) :
    (gridValue N k : ℝ) = (k : ℕ) / ((N : ℝ) + 1) := (rfl)

/-- The grid point just below a `[0, 1]` value: the index of `⌊t (N + 1)⌋ / (N + 1)`. -/
def gridIndex (N : ℕ) (t : Set.Icc (0 : ℝ) 1) : Fin (N + 2) :=
  ⟨⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊, by
    have h : (t : ℝ) * ((N : ℝ) + 1) ≤ ((N + 1 : ℕ) : ℝ) := by
      push_cast
      nlinarith [t.2.1, t.2.2, Nat.cast_nonneg (α := ℝ) N]
    exact Nat.lt_succ_of_le ((Nat.floor_mono h).trans_eq (Nat.floor_natCast _))⟩

@[simp]
theorem gridIndex_val (N : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    (gridIndex N t : ℕ) = ⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊ := (rfl)

/-- Rounding to the grid moves a value by at most the mesh `1 / (N + 1)`. -/
theorem abs_sub_gridValue_gridIndex_le (N : ℕ) (t : Set.Icc (0 : ℝ) 1) :
    |(t : ℝ) - gridValue N (gridIndex N t)| ≤ 1 / ((N : ℝ) + 1) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hx : (0 : ℝ) ≤ (t : ℝ) * ((N : ℝ) + 1) := mul_nonneg t.2.1 hN.le
  have hfloor : ((⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊ : ℕ) : ℝ) ≤ (t : ℝ) * ((N : ℝ) + 1) := Nat.floor_le hx
  have hfloor' : (t : ℝ) * ((N : ℝ) + 1) < ((⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊ : ℕ) : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  rw [gridValue_coe, gridIndex_val, abs_le]
  have hlow : ((⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊ : ℕ) : ℝ) / ((N : ℝ) + 1) ≤ (t : ℝ) :=
    (div_le_iff₀ hN).2 hfloor
  have hhigh : (t : ℝ) - ((⌊(t : ℝ) * ((N : ℝ) + 1)⌋₊ : ℕ) : ℝ) / ((N : ℝ) + 1)
      ≤ 1 / ((N : ℝ) + 1) := by
    rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN]
    linarith
  exact ⟨by linarith [one_div_pos.2 hN], hhigh⟩

/-- **Every finite weighted graph is within `1 / (N + 1)` in cut distance of one whose block values
lie on the grid of multiples of `1 / (N + 1)`.**  Only the edge weights move; the vertex weights
`ν` are untouched. -/
theorem exists_gridValue_cutDist_le (ν : Measure κ) [IsProbabilityMeasure ν] (N : ℕ)
    (b : κ → κ → Set.Icc (0 : ℝ) 1) (hb : ∀ i j, b i j = b j i) :
    ∃ (c : κ → κ → Fin (N + 2)) (hc : ∀ i j, c i j = c j i),
      cutDist (Graphon.ofMatrix ν b hb)
          (Graphon.ofMatrix ν (fun i j => gridValue N (c i j))
            (fun i j => congrArg (gridValue N) (hc i j))) ≤ 1 / ((N : ℝ) + 1) := by
  refine ⟨fun i j => gridIndex N (b i j), fun i j => congrArg (gridIndex N) (hb i j), ?_⟩
  refine (cutDist_le_cutNorm_sub _ _).trans (cutNorm_le_of_forall_abs_le _ _ fun i j => ?_)
  simp only [SymmKernel.coe_sub, Pi.sub_apply, Graphon.coe_toSymmKernel, Graphon.ofMatrix_apply]
  exact abs_sub_gridValue_gridIndex_le N (b i j)

end Grid

section WeightShift

section Weights

variable {κ : Type*} [Fintype κ] {f g : κ → ℝ≥0∞} {k₀ : κ}

private theorem sum_min_add_sum_tsub (hf : ∑ k, f k = 1) :
    ∑ k, min (f k) (g k) + ∑ k, (f k - g k) = 1 := by
  rw [← Finset.sum_add_distrib]
  exact (Finset.sum_congr rfl fun k _ => (add_comm _ _).trans tsub_add_min).trans hf

/-- Away from `k₀` the smaller weight is `g`, so the designated atom can only gain weight. -/
private theorem weight_le_of_dom (hf : ∑ k, f k = 1) (hg : ∑ k, g k = 1)
    (hdom : ∀ k, k ≠ k₀ → g k ≤ f k) : f k₀ ≤ g k₀ := by
  by_contra hlt
  push Not at hlt
  have hmin : ∀ k, min (f k) (g k) = g k := fun k => by
    rcases eq_or_ne k k₀ with rfl | hk
    · exact min_eq_right hlt.le
    · exact min_eq_right (hdom k hk)
  have hsum : ∑ k, g k + ∑ k, (f k - g k) = 1 := by
    simpa only [hmin] using sum_min_add_sum_tsub (g := g) hf
  have key : ∑ k, g k + ∑ k, (f k - g k) = ∑ k, g k + 0 := by rw [add_zero, hsum, hg]
  have hzero : ∑ k, (f k - g k) = 0 :=
    (ENNReal.add_right_inj (by rw [hg]; exact ENNReal.one_ne_top)).1 key
  exact absurd (tsub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hzero k₀ (Finset.mem_univ _)))
    (not_le.2 hlt)

open scoped Classical in
/-- The designated atom absorbs exactly the total transferred weight. -/
private theorem weight_add_sum_tsub (hf : ∑ k, f k = 1) (hg : ∑ k, g k = 1)
    (hdom : ∀ k, k ≠ k₀ → g k ≤ f k) : f k₀ + ∑ k, (f k - g k) = g k₀ := by
  have hk₀ := weight_le_of_dom hf hg hdom
  have hsplit : ∀ k, min (f k) (g k) + (if k = k₀ then g k₀ - f k₀ else 0) = g k := by
    intro k
    split_ifs with hk
    · subst hk
      rw [min_eq_left hk₀, add_tsub_cancel_of_le hk₀]
    · rw [add_zero]
      exact min_eq_right (hdom k hk)
  have hsum : ∑ k, min (f k) (g k) + (g k₀ - f k₀) = 1 := by
    have h1 : ∑ k, (min (f k) (g k) + (if k = k₀ then g k₀ - f k₀ else 0)) = 1 := by
      simpa only [hsplit] using hg
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ k₀ fun _ => g k₀ - f k₀] at h1
    simpa using h1
  have hfin : ∑ k, min (f k) (g k) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑ k, min (f k) (g k) ≤ ∑ k, f k := Finset.sum_le_sum fun k _ => min_le_left _ _
      _ = 1 := hf
  have hdiff : ∑ k, (f k - g k) = g k₀ - f k₀ :=
    (ENNReal.add_right_inj hfin).1 ((sum_min_add_sum_tsub hf).trans hsum.symm)
  rw [hdiff, add_tsub_cancel_of_le hk₀]

end Weights

variable {κ : Type*} [Fintype κ] [MeasurableSpace κ] [MeasurableSingletonClass κ]

private theorem sum_measure_singleton_eq_one (ν : Measure κ) [IsProbabilityMeasure ν] :
    ∑ k, ν {k} = 1 := by
  rw [MeasureTheory.sum_measure_singleton, Finset.coe_univ, measure_univ]

variable (ν ν' : Measure κ) (k₀ : κ)

/-- The coupling of two weight vectors on a finite carrier that keeps as much mass as possible on
the diagonal and transfers the excess of every other atom to the designated atom `k₀`.

It couples `ν` and `ν'` exactly when `ν'` is dominated by `ν` away from `k₀`, and the mass it puts
off the diagonal is then the total transferred weight. -/
private def shiftCoupling : Measure (κ × κ) :=
  ∑ k, min (ν {k}) (ν' {k}) • Measure.dirac (k, k) +
    ∑ k, (ν {k} - ν' {k}) • Measure.dirac (k, k₀)

private theorem shiftCoupling_apply (S : Set (κ × κ)) :
    shiftCoupling ν ν' k₀ S =
      ∑ k, min (ν {k}) (ν' {k}) * S.indicator 1 (k, k) +
        ∑ k, (ν {k} - ν' {k}) * S.indicator 1 (k, k₀) := by
  simp only [shiftCoupling, Measure.coe_add, Pi.add_apply, Measure.finsetSum_apply,
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ MeasurableSet.of_discrete]

variable {ν ν' k₀}

private theorem isCoupling_shiftCoupling [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hdom : ∀ k, k ≠ k₀ → ν' {k} ≤ ν {k}) :
    TauCeti.MeasureTheory.IsCoupling ν ν' (shiftCoupling ν ν' k₀) := by
  have hf := sum_measure_singleton_eq_one ν
  have hg := sum_measure_singleton_eq_one ν'
  have hk₀ := weight_le_of_dom hf hg hdom
  refine TauCeti.MeasureTheory.isCoupling_iff.2 ⟨?_, ?_⟩
  · refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.fst_apply (MeasurableSet.singleton i), shiftCoupling_apply]
    have h1 : ∑ k, min (ν {k}) (ν' {k}) * (Prod.fst ⁻¹' ({i} : Set κ)).indicator 1 (k, k)
        = min (ν {i}) (ν' {i}) := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.fst ⁻¹' ({i} : Set κ)).indicator 1 (k, k₀)
        = ν {i} - ν' {i} := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    rw [h1, h2]
    exact (add_comm _ _).trans tsub_add_min
  · refine Measure.ext_of_singleton fun i => ?_
    rw [Measure.snd_apply (MeasurableSet.singleton i), shiftCoupling_apply]
    have h1 : ∑ k, min (ν {k}) (ν' {k}) * (Prod.snd ⁻¹' ({i} : Set κ)).indicator 1 (k, k)
        = min (ν {i}) (ν' {i}) := by
      refine (Finset.sum_eq_single_of_mem i (Finset.mem_univ _) ?_).trans ?_
      · intro k _ hk
        rw [Set.indicator_of_notMem (by simpa using hk), mul_zero]
      · rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
    rcases eq_or_ne k₀ i with rfl | hne
    · have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.snd ⁻¹' ({k₀} : Set κ)).indicator 1 (k, k₀)
          = ∑ k, (ν {k} - ν' {k}) :=
        Finset.sum_congr rfl fun k _ => by
          rw [Set.indicator_of_mem (by simp), Pi.one_apply, mul_one]
      rw [h1, h2, min_eq_left hk₀]
      exact weight_add_sum_tsub hf hg hdom
    · have h2 : ∑ k, (ν {k} - ν' {k}) * (Prod.snd ⁻¹' ({i} : Set κ)).indicator 1 (k, k₀)
          = 0 :=
        Finset.sum_eq_zero fun k _ => by
          rw [Set.indicator_of_notMem (by simpa using hne), mul_zero]
      rw [h1, h2, add_zero]
      exact min_eq_right (hdom i fun e => hne e.symm)

/-- **Moving vertex weights costs at most twice the moved mass.**  If `ν'` is dominated by `ν` away
from one designated vertex `k₀` -- so that `ν'` arises from `ν` by transferring weight onto `k₀` --
then the two finite weighted graphs with the same edge weights `b` are at cut distance at most twice
the transferred mass.

The witnessing coupling keeps the matched mass on the diagonal, where the overlaid difference
vanishes, and sends the rest to `k₀`; the overlaid difference is bounded by one and supported on the
pairs with a mismatched coordinate. -/
theorem cutDist_ofMatrix_le_two_mul_sum_tsub [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (hdom : ∀ k, k ≠ k₀ → ν' {k} ≤ ν {k}) (b : κ → κ → Set.Icc (0 : ℝ) 1)
    (hb : ∀ i j, b i j = b j i) :
    cutDist (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix ν' b hb)
      ≤ 2 * (∑ k, (ν {k} - ν' {k})).toReal := by
  have hπ := isCoupling_shiftCoupling (ν := ν) (ν' := ν') (k₀ := k₀) hdom
  have : IsProbabilityMeasure (shiftCoupling ν ν' k₀) := hπ.isProbabilityMeasure
  have hrne : ∑ k, (ν {k} - ν' {k}) ≠ ⊤ := by
    refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    calc ∑ k, (ν {k} - ν' {k}) ≤ ∑ k, ν {k} := Finset.sum_le_sum fun k _ => tsub_le_self
      _ = 1 := sum_measure_singleton_eq_one ν
  -- The coupling puts at most the transferred mass off the diagonal.
  have hoff : shiftCoupling ν ν' k₀ (Set.diagonal κ)ᶜ ≤ ∑ k, (ν {k} - ν' {k}) := by
    rw [shiftCoupling_apply]
    have h1 : ∑ k, min (ν {k}) (ν' {k}) * ((Set.diagonal κ)ᶜ).indicator 1 (k, k) = 0 :=
      Finset.sum_eq_zero fun k _ => by
        rw [Set.indicator_of_notMem (by simp [Set.mem_diagonal_iff]), mul_zero]
    rw [h1, zero_add]
    refine Finset.sum_le_sum fun k _ => ?_
    by_cases hk : ((k, k₀) : κ × κ) ∈ ((Set.diagonal κ)ᶜ : Set (κ × κ))
    · rw [Set.indicator_of_mem hk, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hk, mul_zero]
      simp
  -- The overlaid difference vanishes unless one of the two coordinates is mismatched.
  set B : Set ((κ × κ) × (κ × κ)) :=
    ((Set.diagonal κ)ᶜ ×ˢ (Set.univ : Set (κ × κ))) ∪
      ((Set.univ : Set (κ × κ)) ×ˢ (Set.diagonal κ)ᶜ) with hB
  have hBmeas : MeasurableSet B := MeasurableSet.of_discrete
  have hle : ∀ z : (κ × κ) × (κ × κ),
      |overlayDiff (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix ν' b hb)
          (shiftCoupling ν ν' k₀) z.1 z.2| ≤ B.indicator (1 : ((κ × κ) × (κ × κ)) → ℝ) z := by
    intro z
    by_cases hz : z ∈ B
    · rw [Set.indicator_of_mem hz, Pi.one_apply]
      exact abs_overlayDiff_apply_le_one _ _ _ _ _
    · rw [Set.indicator_of_notMem hz]
      simp only [hB, Set.mem_union, Set.mem_prod, Set.mem_univ, and_true, true_and, not_or,
        Set.mem_compl_iff, not_not, Set.mem_diagonal_iff] at hz
      rw [overlayDiff_apply, Graphon.ofMatrix_apply, Graphon.ofMatrix_apply, hz.1, hz.2, sub_self,
        abs_zero]
  refine (cutDist_le _ _ hπ).trans ?_
  refine (cutNorm_le_integral_abs _ _).trans ?_
  have hint : Integrable (fun z : (κ × κ) × (κ × κ) =>
      |overlayDiff (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix ν' b hb)
        (shiftCoupling ν ν' k₀) z.1 z.2|)
      ((shiftCoupling ν ν' k₀).prod (shiftCoupling ν ν' k₀)) :=
    (SymmKernel.integrable_uncurry _ _).abs
  calc ∫ z, |overlayDiff (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix ν' b hb)
          (shiftCoupling ν ν' k₀) z.1 z.2| ∂_
      ≤ ∫ z, B.indicator (1 : ((κ × κ) × (κ × κ)) → ℝ) z ∂_ :=
        integral_mono hint ((integrable_const (1 : ℝ)).indicator hBmeas) hle
    _ = ((shiftCoupling ν ν' k₀).prod (shiftCoupling ν ν' k₀)).real B :=
        integral_indicator_one hBmeas
    _ ≤ 2 * (∑ k, (ν {k} - ν' {k})).toReal := by
        have htwo : (2 : ℝ) * (∑ k, (ν {k} - ν' {k})).toReal
            = ((2 : ℝ≥0∞) * ∑ k, (ν {k} - ν' {k})).toReal := by
          rw [ENNReal.toReal_mul]
          norm_num
        rw [measureReal_def, htwo]
        refine ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp) hrne) ?_
        calc ((shiftCoupling ν ν' k₀).prod (shiftCoupling ν ν' k₀)) B
            ≤ ((shiftCoupling ν ν' k₀).prod (shiftCoupling ν ν' k₀))
                ((Set.diagonal κ)ᶜ ×ˢ (Set.univ : Set (κ × κ))) +
              ((shiftCoupling ν ν' k₀).prod (shiftCoupling ν ν' k₀))
                ((Set.univ : Set (κ × κ)) ×ˢ (Set.diagonal κ)ᶜ) := measure_union_le _ _
          _ = shiftCoupling ν ν' k₀ (Set.diagonal κ)ᶜ +
              shiftCoupling ν ν' k₀ (Set.diagonal κ)ᶜ := by
              rw [Measure.prod_prod, Measure.prod_prod, measure_univ, mul_one, one_mul]
          _ ≤ ∑ k, (ν {k} - ν' {k}) + ∑ k, (ν {k} - ν' {k}) := add_le_add hoff hoff
          _ = 2 * ∑ k, (ν {k} - ν' {k}) := (two_mul _).symm

end WeightShift

section GridWeight

/-- The probability measure on `Fin n` whose weights are the multiples `w i / N` of `1 / N`. -/
def gridWeightMeasure {n N : ℕ} (hN : 0 < N) (w : Fin n → ℕ) (hw : ∑ i, w i = N) :
    Measure (Fin n) :=
  (PMF.ofFintype (fun i => (w i : ℝ≥0∞) / (N : ℝ≥0∞)) (by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, ← Nat.cast_sum, hw]
    rw [← div_eq_mul_inv]
    exact ENNReal.div_self (by exact_mod_cast hN.ne') (by simp))).toMeasure

instance {n N : ℕ} (hN : 0 < N) (w : Fin n → ℕ) (hw : ∑ i, w i = N) :
    IsProbabilityMeasure (gridWeightMeasure hN w hw) :=
  PMF.toMeasure.isProbabilityMeasure _

@[simp]
theorem gridWeightMeasure_apply_singleton {n N : ℕ} (hN : 0 < N) (w : Fin n → ℕ)
    (hw : ∑ i, w i = N) (i : Fin n) :
    gridWeightMeasure hN w hw {i} = (w i : ℝ≥0∞) / (N : ℝ≥0∞) :=
  PMF.toMeasure_apply_singleton _ _ (MeasurableSet.singleton i)

private theorem natCast_div_natCast_eq_ofReal {N : ℕ} (hN : 0 < N) (m : ℕ) :
    (m : ℝ≥0∞) / (N : ℝ≥0∞) = ENNReal.ofReal ((m : ℝ) / (N : ℝ)) := by
  rw [ENNReal.ofReal_div_of_pos (by exact_mod_cast hN), ENNReal.ofReal_natCast,
    ENNReal.ofReal_natCast]

/-- **Every finite weighted graph is close in cut distance to one whose vertex weights are
multiples of `1 / N`.**  Rounding every weight but one down to the grid and letting the remaining
vertex absorb the slack moves at most `n / N` of the mass, and each unit of moved mass costs at most
two in cut distance. -/
theorem exists_gridWeightMeasure_cutDist_le {n N : ℕ} [NeZero n] (hN : 0 < N)
    (ν : Measure (Fin n)) [IsProbabilityMeasure ν] (b : Fin n → Fin n → Set.Icc (0 : ℝ) 1)
    (hb : ∀ i j, b i j = b j i) :
    ∃ (w : Fin n → ℕ) (hw : ∑ i, w i = N),
      cutDist (Graphon.ofMatrix ν b hb) (Graphon.ofMatrix (gridWeightMeasure hN w hw) b hb)
        ≤ 2 * (n : ℝ) / (N : ℝ) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  set v : Fin n → ℕ := fun i => ⌊(ν {i}).toReal * (N : ℝ)⌋₊ with hv
  have hvle : ∀ i, (v i : ℝ) ≤ (ν {i}).toReal * (N : ℝ) := fun i =>
    Nat.floor_le (mul_nonneg ENNReal.toReal_nonneg hNR.le)
  have hvlt : ∀ i, (ν {i}).toReal * (N : ℝ) < (v i : ℝ) + 1 := fun i => Nat.lt_floor_add_one _
  have htoReal_le_one : ∀ i, (ν {i}).toReal ≤ 1 := fun i => by
    simpa using ENNReal.toReal_mono (by simp) (prob_le_one (μ := ν) (s := {i}))
  have hvN : ∀ i, v i ≤ N := fun i => by
    have : (v i : ℝ) ≤ (N : ℝ) := (hvle i).trans (by nlinarith [htoReal_le_one i, hNR])
    exact_mod_cast this
  -- the slack, concentrated on the vertex `0`
  set S : ℕ := ∑ j ∈ Finset.univ.erase (0 : Fin n), v j with hS
  have hSN : S ≤ N := by
    have hreal : (S : ℝ) ≤ (N : ℝ) := by
      have h1 : (S : ℝ) ≤ ∑ j ∈ Finset.univ.erase (0 : Fin n), (ν {j}).toReal * (N : ℝ) := by
        rw [hS, Nat.cast_sum]
        exact Finset.sum_le_sum fun j _ => hvle j
      have h2 : ∑ j ∈ Finset.univ.erase (0 : Fin n), (ν {j}).toReal * (N : ℝ)
          = (∑ j ∈ Finset.univ.erase (0 : Fin n), (ν {j}).toReal) * (N : ℝ) :=
        (Finset.sum_mul _ _ _).symm
      have h3 : ∑ j ∈ Finset.univ.erase (0 : Fin n), (ν {j}).toReal ≤ 1 := by
        have hall : ∑ j, (ν {j}).toReal = 1 := by
          rw [← ENNReal.toReal_sum fun j _ => measure_ne_top ν {j},
            sum_measure_singleton_eq_one ν, ENNReal.toReal_one]
        have hsub := Finset.sum_le_sum_of_subset_of_nonneg
          (f := fun j : Fin n => (ν {j}).toReal)
          (Finset.erase_subset (0 : Fin n) Finset.univ) fun j _ _ => ENNReal.toReal_nonneg
        rw [hall] at hsub
        exact hsub
      nlinarith
    exact_mod_cast hreal
  set w : Fin n → ℕ := fun i => if i = 0 then N - S else v i with hw
  have hwsum : ∑ i, w i = N := by
    rw [← Finset.add_sum_erase _ w (Finset.mem_univ (0 : Fin n))]
    have : ∑ j ∈ Finset.univ.erase (0 : Fin n), w j = S := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hw]
      simp [Finset.ne_of_mem_erase hj]
    rw [this, hw]
    simp only [↓reduceIte]
    omega
  refine ⟨w, hwsum, ?_⟩
  set ν' := gridWeightMeasure hN w hwsum with hν'
  have hweight : ∀ i, ν' {i} = (w i : ℝ≥0∞) / (N : ℝ≥0∞) := fun i => by
    rw [hν', gridWeightMeasure_apply_singleton]
  -- the rounded weights are dominated away from the absorbing vertex
  have hdom : ∀ i, i ≠ (0 : Fin n) → ν' {i} ≤ ν {i} := by
    intro i hi
    rw [hweight i, hw]
    simp only [ite_eq_right hi]
    rw [natCast_div_natCast_eq_ofReal hN, ← ENNReal.ofReal_toReal (measure_ne_top ν {i})]
    exact ENNReal.ofReal_le_ofReal ((div_le_iff₀ hNR).2 (hvle i))
  -- every vertex loses at most one grid step of weight
  have hstep : ∀ i, ν {i} - ν' {i} ≤ (1 : ℝ≥0∞) / (N : ℝ≥0∞) := by
    intro i
    rcases eq_or_ne i (0 : Fin n) with rfl | hi
    · rw [tsub_eq_zero_of_le (weight_le_of_dom (sum_measure_singleton_eq_one ν)
        (sum_measure_singleton_eq_one ν') hdom)]
      simp
    · rw [tsub_le_iff_right, hweight i, hw]
      simp only [ite_eq_right hi]
      rw [natCast_div_natCast_eq_ofReal hN, ← Nat.cast_one (R := ℝ≥0∞),
        natCast_div_natCast_eq_ofReal hN, ← ENNReal.ofReal_add (by positivity) (by positivity),
        ← ENNReal.ofReal_toReal (measure_ne_top ν {i})]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [← add_div, le_div_iff₀ hNR]
      push_cast
      linarith [hvlt i]
  have hsum : ∑ i, (ν {i} - ν' {i}) ≤ (n : ℝ≥0∞) / (N : ℝ≥0∞) := by
    calc ∑ i, (ν {i} - ν' {i}) ≤ ∑ _i : Fin n, (1 : ℝ≥0∞) / (N : ℝ≥0∞) :=
          Finset.sum_le_sum fun i _ => hstep i
      _ = (n : ℝ≥0∞) / (N : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div]
  refine (cutDist_ofMatrix_le_two_mul_sum_tsub hdom b hb).trans ?_
  have htor : (∑ i, (ν {i} - ν' {i})).toReal ≤ (n : ℝ) / (N : ℝ) := by
    refine (ENNReal.toReal_mono
      (ENNReal.div_ne_top (by simp) (by simpa using hN.ne')) hsum).trans ?_
    rw [ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  rw [mul_div_assoc]
  exact mul_le_mul_of_nonneg_left htor (by norm_num)

end GridWeight

end DenseGraphLimits

end TauCeti
