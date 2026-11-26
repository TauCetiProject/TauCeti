/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.LatticeGraph
public import TauCeti.Combinatorics.SimpleGraph.Measurable.Basic
public import TauCeti.Probability.Distributions.SetBernoulli
import TauCeti.Combinatorics.SimpleGraph.Finite

/-!
# Bernoulli bond percolation on `ℤ^d`

In Bernoulli bond percolation with parameter `p ∈ [0, 1]` each edge of the lattice
`TauCeti.latticeGraph d` is open with probability `p`, independently of the others. A
configuration is the graph of its open edges, so the model is a probability measure
`TauCeti.bondPercolation d p` on `SimpleGraph (Fin d → ℤ)`: the image of Mathlib's Bernoulli
random set `setBer((latticeGraph d).edgeSet, p)` under `SimpleGraph.fromEdgeSet`.

The open cluster of a point `x` in a configuration `G` is the support of the connected component
of `x`. The percolation probability `θ(p)`, `TauCeti.percolationProb d p`, is the probability that
the open cluster of the origin is infinite, and the critical probability `p_c(d)`,
`TauCeti.criticalProb d`, is the supremum of the parameters `p` with `θ(p) = 0`.

## Main definitions

* `TauCeti.bondPercolation d p` — the law of the open edges of bond percolation on `ℤ^d`;
* `TauCeti.percolationProb d p` — the percolation probability `θ(p)`;
* `TauCeti.criticalProb d` — the critical probability `p_c(d)`.

## Main results

* `TauCeti.bondPercolation_ae_le` — almost every configuration is a subgraph of the lattice;
* `TauCeti.bondPercolation_setOf_subset_edgeSet`, `TauCeti.bondPercolation_setOf_disjoint_edgeSet`
  — `k` distinct lattice edges are all open with probability `p ^ k` and all closed with
  probability `(1 - p) ^ k`;
* `TauCeti.bondPercolation_zero`, `TauCeti.bondPercolation_one` — at `p = 0` and `p = 1` the
  measure is the point mass at the empty graph and at the full lattice;
* `TauCeti.percolationProb_zero_right`, `TauCeti.percolationProb_one_right` — `θ(0) = 0`, and
  `θ(1) = 1` in every positive dimension;
* `TauCeti.le_criticalProb`, `TauCeti.criticalProb_le` — the characterisation of `p_c(d)` as a
  supremum;
* `TauCeti.criticalProb_nonneg`, `TauCeti.criticalProb_le_one` — `0 ≤ p_c(d) ≤ 1`;
* `TauCeti.percolationProb_zero_left`, `TauCeti.criticalProb_zero` — on the single point `ℤ^0`
  the cluster of the origin is never infinite, so `θ` vanishes and `p_c(0) = 1`.

## References

* G. Grimmett, *Probability on Graphs*, 2nd ed., Cambridge University Press, 2018, Section 3.1;
  the critical probability is display (3.1).
* H. Duminil-Copin, *Introduction to Bernoulli percolation*, lecture notes, IHÉS, 2018, Section 1.
-/

public section

open MeasureTheory Measure ProbabilityTheory unitInterval SimpleGraph
open scoped ENNReal Finset

namespace TauCeti

variable {d : ℕ}

/-- Bernoulli bond percolation on `ℤ^d` with parameter `p`: the law of the graph of open edges
when each edge of `latticeGraph d` is open with probability `p`, independently of the others. -/
noncomputable def bondPercolation (d : ℕ) (p : I) : Measure (SimpleGraph (Fin d → ℤ)) :=
  setBer((latticeGraph d).edgeSet, p).map fromEdgeSet

theorem bondPercolation_def (d : ℕ) (p : I) :
    bondPercolation d p = setBer((latticeGraph d).edgeSet, p).map fromEdgeSet :=
  (rfl)

instance (d : ℕ) (p : I) : IsProbabilityMeasure (bondPercolation d p) :=
  inferInstanceAs (IsProbabilityMeasure (setBer((latticeGraph d).edgeSet, p).map fromEdgeSet))

theorem bondPercolation_apply (p : I) {S : Set (SimpleGraph (Fin d → ℤ))}
    (hS : MeasurableSet S) :
    bondPercolation d p S = setBer((latticeGraph d).edgeSet, p) (fromEdgeSet ⁻¹' S) :=
  map_apply measurable_fromEdgeSet hS

/-- At `p = 0` every edge is closed. -/
@[simp]
theorem bondPercolation_zero (d : ℕ) : bondPercolation d 0 = dirac ⊥ := by
  rw [bondPercolation, setBernoulli_zero, map_dirac' measurable_fromEdgeSet, fromEdgeSet_empty]

/-- At `p = 1` every edge of the lattice is open. -/
@[simp]
theorem bondPercolation_one (d : ℕ) : bondPercolation d 1 = dirac (latticeGraph d) := by
  rw [bondPercolation, setBernoulli_one, map_dirac' measurable_fromEdgeSet, fromEdgeSet_edgeSet]

/-- Almost every configuration of bond percolation is a subgraph of the lattice. -/
theorem bondPercolation_ae_le (p : I) : ∀ᵐ G ∂bondPercolation d p, G ≤ latticeGraph d := by
  rw [bondPercolation, ae_map_iff measurable_fromEdgeSet.aemeasurable (measurableSet_Iic _)]
  filter_upwards [setBernoulli_ae_subset] with s hs
  exact (fromEdgeSet_mono hs).trans_eq (fromEdgeSet_edgeSet _)

/-- An event read off the open edges, which does not change when an edge set is replaced by the
edge set of the graph it spans, has the probability of the same event for the Bernoulli random set
of lattice edges. -/
private theorem bondPercolation_setOf_edgeSet (p : I) {P : Set (Sym2 (Fin d → ℤ)) → Prop}
    (hS : MeasurableSet {s | P s}) (hP : ∀ s, P (fromEdgeSet s).edgeSet ↔ P s) :
    bondPercolation d p {G | P G.edgeSet} = setBer((latticeGraph d).edgeSet, p) {s | P s} := by
  have hS' := measurable_edgeSet hS
  rw [Set.preimage_ofPred_eq] at hS'
  rw [bondPercolation_apply p hS']
  congr 1
  ext s
  exact hP s

/-- Finitely many distinct lattice edges are all open with probability `p ^ k`, where `k` is
their number. -/
theorem bondPercolation_setOf_subset_edgeSet (p : I) {F : Finset (Sym2 (Fin d → ℤ))}
    (hF : (F : Set (Sym2 (Fin d → ℤ))) ⊆ (latticeGraph d).edgeSet) :
    bondPercolation d p {G | (F : Set (Sym2 (Fin d → ℤ))) ⊆ G.edgeSet} =
      (toNNReal p : ℝ≥0∞) ^ #F := by
  rw [bondPercolation_setOf_edgeSet p ?_ fun s => ?_, setBernoulli_setOf_subset p hF]
  · simp only [Set.subset_def]
    exact measurableSet_setOfPred.2 <| Measurable.forall fun e =>
      .imp measurable_const (measurable_set_mem e)
  -- `fromEdgeSet F` has edge set `F`, as lattice edges are not loops.
  · rw [← edgeSet_fromEdgeSet_of_subset hF, edgeSet_subset_edgeSet, le_fromEdgeSet_iff]

/-- Finitely many distinct lattice edges are all open with probability `p ^ k`, where `k` is
their number. -/
theorem bondPercolation_real_setOf_subset_edgeSet (p : I) {F : Finset (Sym2 (Fin d → ℤ))}
    (hF : (F : Set (Sym2 (Fin d → ℤ))) ⊆ (latticeGraph d).edgeSet) :
    (bondPercolation d p).real {G | (F : Set (Sym2 (Fin d → ℤ))) ⊆ G.edgeSet} =
      (p : ℝ) ^ #F := by
  simp [measureReal_def, bondPercolation_setOf_subset_edgeSet p hF]

/-- Finitely many distinct lattice edges are all closed with probability `(1 - p) ^ k`, where `k`
is their number. -/
theorem bondPercolation_setOf_disjoint_edgeSet (p : I) {F : Finset (Sym2 (Fin d → ℤ))}
    (hF : (F : Set (Sym2 (Fin d → ℤ))) ⊆ (latticeGraph d).edgeSet) :
    bondPercolation d p {G | Disjoint (F : Set (Sym2 (Fin d → ℤ))) G.edgeSet} =
      (toNNReal (σ p) : ℝ≥0∞) ^ #F := by
  rw [bondPercolation_setOf_edgeSet p ?_ fun s => ?_, setBernoulli_setOf_disjoint p hF]
  · simp only [Set.disjoint_left]
    exact measurableSet_setOfPred.2 <| Measurable.forall fun e =>
      .imp measurable_const (measurable_set_mem e).not
  -- `fromEdgeSet F` has edge set `F`, as lattice edges are not loops.
  · rw [← edgeSet_fromEdgeSet_of_subset hF, disjoint_edgeSet, disjoint_fromEdgeSet]

/-- Finitely many distinct lattice edges are all closed with probability `(1 - p) ^ k`, where `k`
is their number. -/
theorem bondPercolation_real_setOf_disjoint_edgeSet (p : I) {F : Finset (Sym2 (Fin d → ℤ))}
    (hF : (F : Set (Sym2 (Fin d → ℤ))) ⊆ (latticeGraph d).edgeSet) :
    (bondPercolation d p).real {G | Disjoint (F : Set (Sym2 (Fin d → ℤ))) G.edgeSet} =
      (1 - p : ℝ) ^ #F := by
  simp [measureReal_def, bondPercolation_setOf_disjoint_edgeSet p hF]

/-- An edge of the lattice is open with probability `p`. -/
theorem bondPercolation_setOf_adj (p : I) {x y : Fin d → ℤ}
    (h : (latticeGraph d).Adj x y) :
    bondPercolation d p {G | G.Adj x y} = toNNReal p := by
  simpa using bondPercolation_setOf_subset_edgeSet p (F := {s(x, y)}) (by simpa using h)

/-- An edge of the lattice is open with probability `p`. -/
theorem bondPercolation_real_setOf_adj (p : I) {x y : Fin d → ℤ}
    (h : (latticeGraph d).Adj x y) :
    (bondPercolation d p).real {G | G.Adj x y} = p := by
  simp [measureReal_def, bondPercolation_setOf_adj p h]

/-- A pair of points that is not an edge of the lattice is almost never an open edge. -/
theorem bondPercolation_setOf_adj_of_not_adj (p : I) {x y : Fin d → ℤ}
    (h : ¬(latticeGraph d).Adj x y) :
    bondPercolation d p {G | G.Adj x y} = 0 := by
  refine measure_mono_null ?_ (ae_iff.1 (bondPercolation_ae_le p))
  intro G hG hle
  exact h (hle hG)

/-- A pair of points that is not an edge of the lattice is almost never an open edge. -/
theorem bondPercolation_real_setOf_adj_of_not_adj (p : I) {x y : Fin d → ℤ}
    (h : ¬(latticeGraph d).Adj x y) :
    (bondPercolation d p).real {G | G.Adj x y} = 0 := by
  simp [measureReal_def, bondPercolation_setOf_adj_of_not_adj p h]

/-- The percolation probability `θ(p)`: the probability that the open cluster of the origin is
infinite. -/
noncomputable def percolationProb (d : ℕ) (p : I) : ℝ :=
  (bondPercolation d p).real {G | (G.connectedComponentMk 0).supp.Infinite}

theorem percolationProb_def (d : ℕ) (p : I) :
    percolationProb d p =
      (bondPercolation d p).real {G | (G.connectedComponentMk 0).supp.Infinite} :=
  (rfl)

/-- The percolation probability is nonnegative: `0 ≤ θ(p)`. -/
theorem percolationProb_nonneg (d : ℕ) (p : I) : 0 ≤ percolationProb d p :=
  measureReal_nonneg

/-- The percolation probability is at most one: `θ(p) ≤ 1`. -/
theorem percolationProb_le_one (d : ℕ) (p : I) : percolationProb d p ≤ 1 :=
  measureReal_le_one

/-- At `p = 0` the open cluster of the origin is the origin alone, so `θ(0) = 0`. -/
@[simp]
theorem percolationProb_zero_right (d : ℕ) : percolationProb d 0 = 0 := by
  have : ((⊥ : SimpleGraph (Fin d → ℤ)).connectedComponentMk 0).supp = {0} := by
    ext x
    simp [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq]
  simp [percolationProb, this]

/-- In positive dimension, at `p = 1` the open cluster of the origin is all of `ℤ^d`, so
`θ(1) = 1`. -/
theorem percolationProb_one_right (hd : d ≠ 0) : percolationProb d 1 = 1 := by
  have : Nonempty (Fin d) := ⟨⟨0, Nat.pos_of_ne_zero hd⟩⟩
  have hsupp : ((latticeGraph d).connectedComponentMk 0).supp = Set.univ := by
    ext x
    simp [ConnectedComponent.mem_supp_iff, ConnectedComponent.eq,
      connected_latticeGraph.preconnected x 0]
  simp [percolationProb, hsupp, Set.infinite_univ]

/-- `ℤ^0` is a single point, so no cluster is infinite and `θ` vanishes identically. -/
@[simp]
theorem percolationProb_zero_left (p : I) : percolationProb 0 p = 0 := by
  have : {G : SimpleGraph (Fin 0 → ℤ) | (G.connectedComponentMk 0).supp.Infinite} = ∅ :=
    Set.eq_empty_of_forall_notMem fun _ h => h (Set.toFinite _)
  rw [percolationProb, this, measureReal_empty]

/-- The critical probability `p_c(d)`: the supremum of the parameters `p ∈ [0, 1]` with
`θ(p) = 0`. -/
noncomputable def criticalProb (d : ℕ) : ℝ :=
  sSup (Subtype.val '' {p : I | percolationProb d p = 0})

theorem criticalProb_def (d : ℕ) :
    criticalProb d = sSup (Subtype.val '' {p : I | percolationProb d p = 0}) :=
  (rfl)

/-- Every parameter with `θ(p) = 0` is at most `p_c(d)`. -/
theorem le_criticalProb {p : I} (hp : percolationProb d p = 0) : (p : ℝ) ≤ criticalProb d :=
  le_csSup ⟨1, by rintro _ ⟨q, -, rfl⟩; exact unitInterval.le_one q⟩ ⟨p, hp, rfl⟩

/-- `p_c(d)` is at most every bound on the parameters with `θ(p) = 0`. -/
theorem criticalProb_le {a : ℝ} (h : ∀ p : I, percolationProb d p = 0 → (p : ℝ) ≤ a) :
    criticalProb d ≤ a :=
  csSup_le ⟨0, 0, percolationProb_zero_right d, rfl⟩ (by rintro _ ⟨p, hp, rfl⟩; exact h p hp)

/-- The critical probability is nonnegative: `0 ≤ p_c(d)`. -/
theorem criticalProb_nonneg (d : ℕ) : 0 ≤ criticalProb d :=
  le_criticalProb (p := 0) (percolationProb_zero_right d)

/-- The critical probability is at most one: `p_c(d) ≤ 1`. -/
theorem criticalProb_le_one (d : ℕ) : criticalProb d ≤ 1 :=
  criticalProb_le fun p _ => unitInterval.le_one p

/-- `θ` vanishes identically on the single point `ℤ^0`, so `p_c(0) = 1`. -/
@[simp]
theorem criticalProb_zero : criticalProb 0 = 1 :=
  (criticalProb_le_one 0).antisymm <| by simpa using le_criticalProb (percolationProb_zero_left 1)

end TauCeti
