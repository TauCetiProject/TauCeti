/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.CutMetric.Triangle
public import TauCeti.Combinatorics.DenseGraphLimits.Graphon.OfMatrix
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Approximating a graphon by a finite weighted graph

Frieze--Kannan weak regularity approximates a graphon in **cut norm** by the block averages of a
measurable finite partition.  This file turns that into an approximation in **cut distance** by a
finite object: the block matrix of the approximating step graphon, read as a graphon on the
discrete probability space of its blocks.

The cut distance never increases along a measure-preserving pullback (`cutDist_comap_right`), and a
step graphon *is* the pullback of its block matrix along the part-index map, so a step graphon and
its finite matrix are at cut distance zero.  Step graphons are therefore dense in the cut metric,
and so are finite weighted graphs on a vertex set whose size depends only on the accuracy.  Rounding
the two weightings of such a finite weighted graph onto a grid, so that finitely many candidates
remain, is `TauCeti.Combinatorics.DenseGraphLimits.CutMetric.OfMatrixGrid`.

## Main results

* `TauCeti.DenseGraphLimits.exists_stepGraphon_cutDist_le` -- every graphon is within `ε` in cut
  distance of a step graphon on a measurable finite partition with at most `4 ^ (⌈1/ε²⌉ + 1)` parts;
* `TauCeti.DenseGraphLimits.exists_ofMatrix_cutDist_le` -- every graphon is within `ε` in cut
  distance of a finite weighted graph on any vertex set of size at least `4 ^ (⌈1/ε²⌉ + 1)`.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2 --
  weighted graphs are dense in the space of graphons.
-/

public section

noncomputable section

open MeasureTheory

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

end DenseGraphLimits

end TauCeti
