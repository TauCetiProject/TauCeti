/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.GraphonSpace.Density
import TauCeti.MeasureTheory.Measure.UnitIntervalMap

/-!
# Graphon space is totally bounded

On the canonical carrier `(I, volume)` the space of graphons is **totally bounded**: for every `ε`
there are finitely many graphons within `ε` in cut distance of every graphon.

The net is finite because a Frieze--Kannan approximation is a finite weighted graph on a vertex set
whose size depends only on `ε`, and both of its weightings can be pushed onto a grid at a controlled
cost: the block values by rounding down (`exists_gridValue_cutDist_le`) and the vertex weights by
rounding all but one of them down and letting the remaining vertex absorb the slack
(`exists_gridWeightMeasure_cutDist_le`).  Finitely many grid weightings of a fixed finite vertex set
remain, each read onto `(I, volume)` along a measure-preserving map out of the unit interval
(Janson, Theorem A.9).

Total boundedness is one of the two halves of the Lovász--Szegedy compactness theorem, the other
being completeness.

## Main results

* `TauCeti.DenseGraphLimits.totallyBounded_graphonSpaceI` -- `GraphonSpaceI` is totally bounded.

## References

* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.3.
* S. Janson, *Graphons, cut norm and distance, couplings and rearrangements*, NYJM Monographs 4
  (2013), Theorem A.9.
-/

public section

noncomputable section

open MeasureTheory

open scoped unitInterval ENNReal

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Net

/-- The canonical `(I, volume)` representative of a graphon on a standard Borel probability
carrier: its pullback along a measure-preserving map out of the unit interval (Janson A.9). -/
private def unitIntervalModel {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (V : Graphon α ν) :
    Graphon I (volume : Measure I) :=
  V.comap (Measure.exists_measurePreserving_from_unitInterval ν).choose
    (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec.measurable volume

private theorem cutDist_unitIntervalModel {α : Type*} [MeasurableSpace α] [StandardBorelSpace α]
    (ν : Measure α) [IsProbabilityMeasure ν] (U : Graphon Ω μ) (V : Graphon α ν) :
    cutDist U (unitIntervalModel ν V) = cutDist U V :=
  cutDist_comap_right U V (Measure.exists_measurePreserving_from_unitInterval ν).choose_spec

/-- A point of the finite net: the finite weighted graph on `Fin n` whose vertex weights are the
multiples `w i / N` of `1 / N` and whose block values are the multiples of `1 / (N + 1)` named by
`c`, read onto the canonical carrier. -/
private def netPoint {n N : ℕ} (hN : 0 < N)
    (p : {w : Fin n → Fin (N + 1) // ∑ i, (w i : ℕ) = N} ×
      {c : Fin n → Fin n → Fin (N + 2) // ∀ i j, c i j = c j i}) : GraphonSpaceI :=
  SeparationQuotient.mk
    (unitIntervalModel (gridWeightMeasure hN (fun i => (p.1.1 i : ℕ)) p.1.2)
      (Graphon.ofMatrix (gridWeightMeasure hN (fun i => (p.1.1 i : ℕ)) p.1.2)
        (fun i j => gridValue N (p.2.1 i j))
        (fun i j => congrArg (gridValue N) (p.2.2 i j))))

/-- **Graphon space over the unit interval is totally bounded.** -/
theorem totallyBounded_graphonSpaceI : TotallyBounded (Set.univ : Set GraphonSpaceI) := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  set δ : ℝ := ε / 4 with hδdef
  have hδ : 0 < δ := by positivity
  set n : ℕ := 4 ^ (Nat.ceil (1 / δ ^ 2) + 1) with hndef
  have hn0 : 0 < n := pow_pos (by norm_num) _
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn0
  have : NeZero n := ⟨hn0.ne'⟩
  set N : ℕ := Nat.ceil (8 * (n : ℝ) / ε) + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hNR : 8 * (n : ℝ) / ε ≤ (N : ℝ) := by
    rw [hNdef]
    push_cast
    linarith [Nat.le_ceil (8 * (n : ℝ) / ε)]
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hεN : 8 * (n : ℝ) ≤ ε * N := by
    rw [div_le_iff₀ hε] at hNR
    linarith
  -- the two rounding errors are each at most `ε / 4`
  have hgrid : 1 / ((N : ℝ) + 1) ≤ ε / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hweight : 2 * (n : ℝ) / (N : ℝ) ≤ ε / 4 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    nlinarith
  refine ⟨Set.range (netPoint (n := n) hN), Set.finite_range _, ?_⟩
  rintro x -
  obtain ⟨W, rfl⟩ := SeparationQuotient.surjective_mk x
  obtain ⟨g, _hg, b₀, hb₀, h1⟩ := exists_ofMatrix_cutDist_le W hδ hndef.ge
  obtain ⟨c, hc, h2⟩ := exists_gridValue_cutDist_le (volume.map g) N b₀ hb₀
  obtain ⟨w, hw, h3⟩ := exists_gridWeightMeasure_cutDist_le hN (volume.map g)
    (fun i j => gridValue N (c i j)) (fun i j => congrArg (gridValue N) (hc i j))
  have hwlt : ∀ i, w i < N + 1 := by
    intro i
    have hle : w i ≤ ∑ j, w j :=
      Finset.single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hw] at hle
    exact Nat.lt_succ_of_le hle
  have key : cutDist W (Graphon.ofMatrix (gridWeightMeasure hN w hw)
      (fun i j => gridValue N (c i j)) (fun i j => congrArg (gridValue N) (hc i j))) < ε := by
    set A₀ := Graphon.ofMatrix (volume.map g) b₀ hb₀
    set A₁ := Graphon.ofMatrix (volume.map g) (fun i j => gridValue N (c i j))
      (fun i j => congrArg (gridValue N) (hc i j))
    set A₂ := Graphon.ofMatrix (gridWeightMeasure hN w hw) (fun i j => gridValue N (c i j))
      (fun i j => congrArg (gridValue N) (hc i j))
    calc cutDist W A₂ ≤ cutDist W A₀ + cutDist A₀ A₂ := cutDist_triangle _ _ _
      _ ≤ cutDist W A₀ + (cutDist A₀ A₁ + cutDist A₁ A₂) :=
          add_le_add le_rfl (cutDist_triangle _ _ _)
      _ < ε := by
          have hW := h1.trans_eq hδdef
          linarith [h2.trans hgrid, h3.trans hweight]
  refine Set.mem_iUnion₂.2 ⟨netPoint hN ⟨⟨fun i => ⟨w i, hwlt i⟩, hw⟩, ⟨c, hc⟩⟩,
    Set.mem_range_self _, ?_⟩
  rw [Metric.mem_ball, netPoint, dist_graphonSpace_mk_mk, cutDist_unitIntervalModel]
  exact key

end Net

end DenseGraphLimits

end TauCeti
