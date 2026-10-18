/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
import TauCeti.Combinatorics.SimpleGraph.Regularity.Uniform
import Mathlib.Tactic.Linarith

/-!
# Simple graphs as pair-color systems

A simple graph `G` colors each ordered distinct vertex pair by whether it is an edge. This
symmetric two-color system `PairColorSystem.ofGraph G` is the arity-two specialization of the
lower skeleton. Between disjoint vertex sets its two color densities are the edge densities of
`G` and of its complement `Gᶜ`, and pair regularity is sandwiched between Mathlib's
`SimpleGraph.IsUniform` at the same and at any larger parameter. Hence a pair-color regular
skeleton of a graph gives a uniform partition in the sense of Szemerédi's regularity lemma.

Within a single vertex cell the densities are taken among distinct pairs, whereas Mathlib's
`SimpleGraph.edgeDensity s s` divides by `#s ^ 2`; pair-color regularity also controls these
diagonal blocks, which `Finpartition.IsUniform` ignores.

## Main declarations

* `TauCeti.PairColorSystem.ofGraph`: the edge/non-edge coloring of a simple graph.
* `TauCeti.PairColorSystem.pairColorDensity_ofGraph_true`: the edge color has the edge density
  between disjoint sets.
* `SimpleGraph.IsUniform.isRegularPair_ofGraph`, `TauCeti.PairColorSystem.IsRegularPair.isUniform`:
  uniform and regular pairs of disjoint sets agree up to the strictness of the bound.
* `TauCeti.PairSkeleton3.IsPairColorRegular.isUniform`: a pair-color regular skeleton of
  a graph has a uniform vertex partition.
-/

public section

open Finset

namespace TauCeti

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

namespace PairColorSystem

/-- The pair-color system of a simple graph: an ordered distinct pair has color `true` exactly
when it is an edge. The palette reversal is the identity, since adjacency is symmetric. -/
def ofGraph : PairColorSystem Bool V where
  color p := decide (G.Adj p.1.1 p.1.2)
  rev := id
  rev_involutive _ := rfl
  color_rev p := by simp [G.adj_comm]

@[simp]
theorem ofGraph_color (p : {p : V × V // p.1 ≠ p.2}) :
    (ofGraph G).color p = decide (G.Adj p.1.1 p.1.2) :=
  (rfl)

@[simp]
theorem ofGraph_rev (c : Bool) : (ofGraph G).rev c = c :=
  (rfl)

/-- The edge color marks exactly the edges of `G`. -/
@[simp]
theorem colorOfPair_ofGraph_eq_some_true (u v : V) :
    (ofGraph G).colorOfPair u v = some true ↔ G.Adj u v := by
  rw [colorOfPair_eq_some_iff]
  exact ⟨fun ⟨_, h⟩ => by simpa using h, fun h => ⟨h.ne, by simpa using h⟩⟩

/-- The non-edge color marks exactly the edges of the complement `Gᶜ`. -/
@[simp]
theorem colorOfPair_ofGraph_eq_some_false (u v : V) :
    (ofGraph G).colorOfPair u v = some false ↔ Gᶜ.Adj u v := by
  rw [colorOfPair_eq_some_iff, SimpleGraph.compl_adj]
  exact ⟨fun ⟨hne, h⟩ => ⟨hne, by simpa using h⟩, fun ⟨hne, h⟩ => ⟨hne, by simpa using h⟩⟩

variable {s t : Finset V}

/-- Between disjoint sets, every ordered pair is distinct. -/
private theorem filter_ne_product_of_disjoint [DecidableEq V] (hst : Disjoint s t) :
    (s ×ˢ t).filter (fun p => p.1 ≠ p.2) = s ×ˢ t :=
  filter_true_of_mem fun _ hp =>
    hst.forall_ne_finset (mem_product.mp hp).1 (mem_product.mp hp).2

/-- Between disjoint sets, the edge color has the edge density of `G`. -/
theorem pairColorDensity_ofGraph_true (hst : Disjoint s t) :
    pairColorDensity (ofGraph G) true s t = G.edgeDensity s t := by
  classical
  rw [pairColorDensity_def, filter_ne_product_of_disjoint hst, SimpleGraph.edgeDensity_def,
    SimpleGraph.interedges_def, card_product, Nat.cast_mul]
  simp

/-- Between disjoint sets, the non-edge color has the edge density of the complement `Gᶜ`. -/
theorem pairColorDensity_ofGraph_false [DecidableEq V] (hst : Disjoint s t) :
    pairColorDensity (ofGraph G) false s t = Gᶜ.edgeDensity s t := by
  rw [pairColorDensity_def, filter_ne_product_of_disjoint hst, SimpleGraph.edgeDensity_def,
    SimpleGraph.interedges_def, card_product, Nat.cast_mul]
  simp

variable {G} {ε ε' : ℝ}

/-- A regular pair of disjoint sets for the graph coloring is uniform in Mathlib's sense at every
strictly larger parameter. -/
theorem IsRegularPair.isUniform (h : (ofGraph G).IsRegularPair ε s t) (hst : Disjoint s t)
    (hε : ε < ε') : G.IsUniform ε' s t := by
  intro s' hs' t' ht' hs ht
  have hs₀ : ε * #s ≤ #s' := (mul_le_mul_of_nonneg_right hε.le (Nat.cast_nonneg _)).trans
    (by rwa [mul_comm])
  have ht₀ : ε * #t ≤ #t' := (mul_le_mul_of_nonneg_right hε.le (Nat.cast_nonneg _)).trans
    (by rwa [mul_comm])
  have hd := isRegularPair_iff.mp h true s' hs' t' ht' hs₀ ht₀
  rw [pairColorDensity_ofGraph_true G (hst.mono hs' ht'),
    pairColorDensity_ofGraph_true G hst] at hd
  exact hd.trans_lt hε

end PairColorSystem

end TauCeti

open TauCeti

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ} {s t : Finset V}

/-- An `ε`-uniform pair of disjoint sets is `ε`-regular for the graph coloring: both the edge
and the non-edge color densities are `ε`-stable. -/
theorem IsUniform.isRegularPair_ofGraph (h : G.IsUniform ε s t) (hst : Disjoint s t) :
    (PairColorSystem.ofGraph G).IsRegularPair ε s t := by
  classical
  refine PairColorSystem.isRegularPair_iff.mpr fun c s' hs' t' ht' hs ht => ?_
  rw [mul_comm] at hs ht
  cases c
  · rw [PairColorSystem.pairColorDensity_ofGraph_false G (hst.mono hs' ht'),
      PairColorSystem.pairColorDensity_ofGraph_false G hst]
    exact ((h.compl hst) hs' ht' hs ht).le
  · rw [PairColorSystem.pairColorDensity_ofGraph_true G (hst.mono hs' ht'),
      PairColorSystem.pairColorDensity_ofGraph_true G hst]
    exact (h hs' ht' hs ht).le

end SimpleGraph

namespace TauCeti.PairSkeleton3

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)} {ε ε' : ℝ}

/-- If the lower skeleton of a graph with vertex cells `P` is pair-color regular, then any two
distinct cells form a uniform pair at every strictly larger parameter. -/
theorem IsPairColorRegular.isUniform_of_ne
    (h : (⟨P, PairColorSystem.ofGraph G⟩ : PairSkeleton3 Bool V).IsPairColorRegular ε)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) (hε : ε < ε') :
    G.IsUniform ε' A B :=
  (h.isRegularPair hA hB).isUniform (P.disjoint hA hB hAB) hε

/-- If the lower skeleton of a graph with vertex cells `P` is pair-color regular, then `P` is a
uniform partition of `G` at every strictly larger parameter, in the sense of Szemerédi's
regularity lemma: in fact no pair of distinct cells is non-uniform. -/
theorem IsPairColorRegular.isUniform
    (h : (⟨P, PairColorSystem.ofGraph G⟩ : PairSkeleton3 Bool V).IsPairColorRegular ε)
    (hε : ε < ε') : P.IsUniform G ε' := by
  have hnu : P.nonUniforms G ε' = ∅ := by
    refine eq_empty_iff_forall_notMem.mpr fun ⟨A, B⟩ hAB => ?_
    obtain ⟨hA, hB, hne, hnu⟩ := (P.mk_mem_nonUniforms G).mp hAB
    exact hnu (h.isUniform_of_ne hA hB hne hε)
  rw [Finpartition.IsUniform, hnu, card_empty, Nat.cast_zero]
  rcases isEmpty_or_nonempty V with hV | hV
  · have hP : P.parts = ∅ := Finpartition.parts_eq_empty_iff.mpr (by simp [univ_eq_empty])
    simp [hP]
  · exact mul_nonneg (Nat.cast_nonneg _) (h.nonneg.trans hε.le)

end TauCeti.PairSkeleton3
