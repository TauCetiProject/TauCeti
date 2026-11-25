/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Uniform
public import TauCeti.Combinatorics.SimpleGraph.Density
import Mathlib.Data.Rat.BigOperators
import TauCeti.Algebra.Order.BigOperators.Group.Finset
import TauCeti.Combinatorics.SimpleGraph.Regularity.Uniform
import TauCeti.Data.Finset.Basic

/-!
# Simple graphs and pair-color systems

A reversal-invariant finite set `K` of colors in a coherent pair coloring selects a simple
graph. Between disjoint vertex sets its edge density is the sum of the selected color densities.
Coordinatewise pair regularity gives graph uniformity at every tolerance strictly exceeding
`#K * ε`, where `ε` is the pair-regularity parameter.

In the other direction, a simple graph colors each ordered distinct vertex pair by whether it
is an edge. Selecting the edge or nonedge color recovers the graph or its complement.

Within a single vertex cell the color densities are taken among distinct pairs, whereas
`SimpleGraph.edgeDensity s s` divides by `#s ^ 2`. Pair-color regularity also controls these
diagonal blocks, which `Finpartition.IsUniform` ignores.

## Main declarations

* `TauCeti.PairColorSystem.colorGraph`: the graph selected by a reversal-invariant palette subset.
* `TauCeti.PairColorSystem.edgeDensity_colorGraph`: its density on disjoint sets.
* `TauCeti.PairSkeleton3.IsPairColorRegular.isUniform_colorGraph`: a regular lower skeleton
  gives a uniform vertex partition of the selected graph.
* `SimpleGraph.toPairColorSystem`: the edge/nonedge coloring of a simple graph.
* `SimpleGraph.pairColorDensity_toPairColorSystem_true`: the edge color has the edge density
  between disjoint sets.
* `SimpleGraph.pairColorDensity_toPairColorSystem_decide`: between disjoint nonempty sets, the
  two colors have the edge and nonedge densities `SimpleGraph.patternDensity`.
* `SimpleGraph.IsUniform.isRegularPair_ofGraph`, `TauCeti.PairColorSystem.IsRegularPair.isUniform`:
  uniform and regular pairs of disjoint sets agree up to the strictness of the bound.
-/

public section

open Finset TauCeti

namespace TauCeti.PairColorSystem

variable {κ V : Type*} (S : PairColorSystem κ V) (K : Finset κ)
  (hK : ∀ c ∈ K, S.rev c ∈ K)

/-- The simple graph selecting the colors in a reversal-invariant finite set `K`. -/
def colorGraph : SimpleGraph V where
  Adj u v := ∃ h : u ≠ v, S.color ⟨(u, v), h⟩ ∈ K
  symm := ⟨by
    rintro u v ⟨hne, hc⟩
    exact ⟨hne.symm, (S.color_rev ⟨(u, v), hne⟩).symm ▸ hK _ hc⟩⟩
  loopless := ⟨fun _ ⟨hne, _⟩ ↦ hne rfl⟩

/-- Adjacency means that the ordered pair has one of the selected colors. -/
@[simp, grind =]
theorem colorGraph_adj (u v : V) :
    (S.colorGraph K hK).Adj u v ↔ ∃ c ∈ K, S.colorOfPair u v = some c := by
  simp only [colorGraph, colorOfPair_eq_some_iff]
  exact ⟨fun ⟨h, hc⟩ ↦ ⟨_, hc, h, rfl⟩, fun ⟨_, hc, h, he⟩ ↦ ⟨h, he ▸ hc⟩⟩

/-- For distinct vertices, adjacency is membership of their color in the selected set. -/
theorem colorGraph_adj_of_ne {u v : V} (h : u ≠ v) :
    (S.colorGraph K hK).Adj u v ↔ S.color ⟨(u, v), h⟩ ∈ K :=
  ⟨fun ⟨_, hc⟩ ↦ hc, fun hc ↦ ⟨h, hc⟩⟩

/-- With decidable equality on vertices and colors, color graph adjacency is computable. -/
instance [DecidableEq V] [DecidableEq κ] : DecidableRel (S.colorGraph K hK).Adj :=
  fun u v ↦ if h : u ≠ v then decidable_of_iff _ (S.colorGraph_adj_of_ne K hK h).symm
    else isFalse (by rintro ⟨hne, _⟩; exact h hne)

/-- Selecting no colors gives the empty graph. -/
@[simp, grind =]
theorem colorGraph_empty (h : ∀ c ∈ (∅ : Finset κ), S.rev c ∈ (∅ : Finset κ)) :
    S.colorGraph ∅ h = ⊥ := by
  ext u v
  simp

/-- Selecting the whole palette gives the complete graph. -/
@[simp, grind =]
theorem colorGraph_univ [Fintype κ] (h : ∀ c ∈ (univ : Finset κ), S.rev c ∈ univ) :
    S.colorGraph univ h = ⊤ := by
  ext u v
  simp [colorGraph]

variable {K hK} {L : Finset κ} {hL : ∀ c ∈ L, S.rev c ∈ L}

/-- Enlarging the set of selected colors enlarges the selected graph. -/
theorem colorGraph_mono (h : K ⊆ L) : S.colorGraph K hK ≤ S.colorGraph L hL :=
  fun _ _ ⟨hne, hc⟩ ↦ ⟨hne, h hc⟩

/-- Selecting the union of two color sets gives the union of the selected graphs. -/
theorem colorGraph_union [DecidableEq κ] (h : ∀ c ∈ K ∪ L, S.rev c ∈ K ∪ L) :
    S.colorGraph (K ∪ L) h = S.colorGraph K hK ⊔ S.colorGraph L hL := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  simp only [SimpleGraph.sup_adj, S.colorGraph_adj_of_ne _ _ huv, mem_union]

/-- Selecting the other colors of a finite palette gives the graph complement. -/
theorem colorGraph_compl [Fintype κ] [DecidableEq κ] (h : ∀ c ∈ Kᶜ, S.rev c ∈ Kᶜ) :
    S.colorGraph Kᶜ h = (S.colorGraph K hK)ᶜ := by
  ext u v
  by_cases huv : u = v
  · subst v
    simp
  simp only [SimpleGraph.compl_adj, S.colorGraph_adj_of_ne _ _ huv, mem_compl,
    and_iff_right huv]

/-- Disjoint color selections produce edge-disjoint graphs. -/
theorem disjoint_colorGraph (h : Disjoint K L) :
    Disjoint (S.colorGraph K hK) (S.colorGraph L hL) := by
  rw [disjoint_iff_inf_le]
  rintro u v ⟨⟨hne, hc⟩, ⟨_, hc'⟩⟩
  exact (Finset.disjoint_left.1 h hc hc').elim

variable (K hK) [DecidableRel (S.colorGraph K hK).Adj]

/-- The edge count of a color graph is the sum of the selected color counts. This identity
also holds for overlapping vertex sets: it counts edges, without normalizing. -/
theorem card_interedges_colorGraph [DecidableEq κ] (s t : Finset V) :
    #((S.colorGraph K hK).interedges s t) =
      ∑ c ∈ K, #{p ∈ s ×ˢ t | S.colorOfPair p.1 p.2 = some c} := by
  classical
  simpa [SimpleGraph.interedges_def, colorGraph_adj, eq_comm] using
    (S.sum_card_colorOfPair_fibers K s t).symm

/-- On disjoint sets, the graph density is the sum of the selected pair-color densities,
including when either vertex set or the selected palette is empty. -/
theorem edgeDensity_colorGraph {s t : Finset V} (hst : Disjoint s t) :
    (S.colorGraph K hK).edgeDensity s t = ∑ c ∈ K, pairColorDensity S c s t := by
  classical
  simp_rw [pairColorDensity_def, filter_ne_product_of_disjoint hst, card_product, Nat.cast_mul]
  rw [← sum_div, ← Nat.cast_sum, SimpleGraph.edgeDensity_def, card_interedges_colorGraph]

variable {S K hK} {ε ε' : ℝ} {s t : Finset V}

/-- For a regular pair of disjoint sets, the edge density of the color graph on any large
subrectangle is within `#K * ε` of its edge density on the original pair. -/
theorem IsRegularPair.abs_edgeDensity_colorGraph_sub_le (h : S.IsRegularPair ε s t)
    (hst : Disjoint s t) (K : Finset κ) (hK : ∀ c ∈ K, S.rev c ∈ K)
    [DecidableRel (S.colorGraph K hK).Adj]
    {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t)
    (hs : ε * #s ≤ #s') (ht : ε * #t ≤ #t') :
    |((S.colorGraph K hK).edgeDensity s' t' : ℝ) -
      (S.colorGraph K hK).edgeDensity s t| ≤ #K * ε := by
  rw [S.edgeDensity_colorGraph K hK (hst.mono hs' ht'), S.edgeDensity_colorGraph K hK hst]
  push_cast
  rw [← sum_sub_distrib]
  simpa only [nsmul_eq_mul] using
    abs_sum_le_card_nsmul (s := K) fun c _ ↦ (isRegularPair_iff.1 h) c s' hs' t' ht' hs ht

/-- A regular pair of disjoint sets is uniform for the color graph at any tolerance strictly
exceeding the accumulated color error `#K * ε`. The empty selection needs only `0 < ε'`. -/
theorem IsRegularPair.isUniform_colorGraph (h : S.IsRegularPair ε s t)
    (hst : Disjoint s t) (K : Finset κ) (hK : ∀ c ∈ K, S.rev c ∈ K)
    [DecidableRel (S.colorGraph K hK).Adj] (hbound : (#K : ℝ) * ε < ε') :
    (S.colorGraph K hK).IsUniform ε' s t := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · intro s' hs' t' ht' _ _
    rw [S.edgeDensity_colorGraph ∅ hK (hst.mono hs' ht'), S.edgeDensity_colorGraph ∅ hK hst]
    simpa using hbound
  have : Nonempty κ := ⟨hne.choose⟩
  have hcard : (1 : ℝ) ≤ #K := by exact_mod_cast one_le_card.2 hne
  have hε : ε ≤ ε' := (le_mul_of_one_le_left h.nonneg hcard).trans hbound.le
  intro s' hs' t' ht' hs ht
  apply (h.abs_edgeDensity_colorGraph_sub_le hst K hK hs' ht' ?_ ?_).trans_lt hbound
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans (by rwa [mul_comm])
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans (by rwa [mul_comm])

end TauCeti.PairColorSystem

namespace TauCeti.PairSkeleton3

variable {κ V : Type*} [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {ε ε' : ℝ}
  {K : Finset κ} {hK : ∀ c ∈ K, S.pairColors.rev c ∈ K}
  [DecidableRel (S.pairColors.colorGraph K hK).Adj]

/-- Distinct cells of a regular skeleton are uniform for the selected graph at any tolerance
strictly exceeding `#K * ε`. -/
theorem IsPairColorRegular.isUniform_colorGraph_of_ne (h : S.IsPairColorRegular ε)
    {A B : Finset V} (hA : A ∈ S.vertexPart.parts) (hB : B ∈ S.vertexPart.parts) (hAB : A ≠ B)
    (hbound : (#K : ℝ) * ε < ε') : (S.pairColors.colorGraph K hK).IsUniform ε' A B :=
  (h.isRegularPair hA hB).isUniform_colorGraph (S.vertexPart.disjoint hA hB hAB) K hK hbound

/-- No distinct pair of cells is nonuniform for the selected graph at a tolerance strictly
exceeding `#K * ε`. -/
theorem IsPairColorRegular.nonUniforms_colorGraph_eq_empty (h : S.IsPairColorRegular ε)
    (hbound : (#K : ℝ) * ε < ε') :
    S.vertexPart.nonUniforms (S.pairColors.colorGraph K hK) ε' = ∅ :=
  Finpartition.nonUniforms_eq_empty_iff.2 fun _ hA _ hB hAB ↦
    h.isUniform_colorGraph_of_ne hA hB hAB hbound

/-- The vertex partition of a regular lower skeleton is uniform for the selected graph at any
tolerance strictly exceeding the accumulated color error `#K * ε`. -/
theorem IsPairColorRegular.isUniform_colorGraph (h : S.IsPairColorRegular ε)
    (hbound : (#K : ℝ) * ε < ε') : S.vertexPart.IsUniform (S.pairColors.colorGraph K hK) ε' :=
  Finpartition.isUniform_of_nonUniforms_eq_empty (h.nonUniforms_colorGraph_eq_empty hbound)

end TauCeti.PairSkeleton3

variable {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]

namespace SimpleGraph

/-- The pair-color system of a simple graph: an ordered distinct pair has color `true` exactly
when it is an edge. The palette reversal is the identity, since adjacency is symmetric. -/
def toPairColorSystem : PairColorSystem Bool V where
  color p := decide (G.Adj p.val.1 p.val.2)
  rev := id
  rev_involutive _ := rfl
  color_rev p := by simp [G.adj_comm]

@[simp]
theorem toPairColorSystem_color (p : {p : V × V // p.1 ≠ p.2}) :
    G.toPairColorSystem.color p = decide (G.Adj p.val.1 p.val.2) :=
  (rfl)

@[simp]
theorem toPairColorSystem_rev (c : Bool) : G.toPairColorSystem.rev c = c :=
  (rfl)

/-- The edge color marks exactly the edges of `G`. -/
@[simp]
theorem colorOfPair_toPairColorSystem_eq_some_true (u v : V) :
    G.toPairColorSystem.colorOfPair u v = some true ↔ G.Adj u v := by
  rw [PairColorSystem.colorOfPair_eq_some_iff]
  exact ⟨fun ⟨_, h⟩ => by simpa using h, fun h => ⟨h.ne, by simpa using h⟩⟩

/-- The non-edge color marks exactly the edges of the complement `Gᶜ`. -/
@[simp]
theorem colorOfPair_toPairColorSystem_eq_some_false (u v : V) :
    G.toPairColorSystem.colorOfPair u v = some false ↔ Gᶜ.Adj u v := by
  rw [PairColorSystem.colorOfPair_eq_some_iff, SimpleGraph.compl_adj]
  exact ⟨fun ⟨hne, h⟩ => ⟨hne, by simpa using h⟩, fun ⟨hne, h⟩ => ⟨hne, by simpa using h⟩⟩

/-- Selecting the edge color in the pair coloring of a graph recovers the graph. -/
@[simp, grind =]
theorem colorGraph_toPairColorSystem_true :
    G.toPairColorSystem.colorGraph {true} (by simp) = G := by
  ext u v
  simp

/-- Selecting the nonedge color in the pair coloring of a graph recovers its loopless complement. -/
@[simp, grind =]
theorem colorGraph_toPairColorSystem_false :
    G.toPairColorSystem.colorGraph {false} (by simp) = Gᶜ := by
  ext u v
  simp

variable {s t : Finset V}

/-- Between disjoint sets, the edge color has the edge density of `G`. -/
theorem pairColorDensity_toPairColorSystem_true (hst : Disjoint s t) :
    pairColorDensity G.toPairColorSystem true s t = G.edgeDensity s t := by
  classical
  simpa using (G.toPairColorSystem.edgeDensity_colorGraph {true} (by simp) hst).symm

/-- Between disjoint sets, the non-edge color has the edge density of the complement `Gᶜ`. -/
theorem pairColorDensity_toPairColorSystem_false [DecidableEq V] (hst : Disjoint s t) :
    pairColorDensity G.toPairColorSystem false s t = Gᶜ.edgeDensity s t := by
  simpa using (G.toPairColorSystem.edgeDensity_colorGraph {false} (by simp) hst).symm

/-- Between disjoint nonempty sets, the color `decide e` has the pattern density of `G`: the edge
density if `e` holds and the nonedge density otherwise. -/
theorem pairColorDensity_toPairColorSystem_decide {𝕜 : Type*} [DivisionRing 𝕜] [CharZero 𝕜]
    (e : Prop) [Decidable e] (hs : s.Nonempty) (ht : t.Nonempty) (hst : Disjoint s t) :
    (pairColorDensity G.toPairColorSystem (decide e) s t : 𝕜) = G.patternDensity e s t := by
  classical
  by_cases he : e
  · rw [decide_eq_true he, G.pairColorDensity_toPairColorSystem_true hst,
      G.patternDensity_of_pos he]
  · rw [decide_eq_false he, G.pairColorDensity_toPairColorSystem_false hst,
      G.patternDensity_of_neg he,
      eq_sub_of_add_eq' (G.edgeDensity_add_edgeDensity_compl hs ht hst)]
    norm_cast

end SimpleGraph

namespace TauCeti.PairColorSystem

variable {G} {ε ε' : ℝ} {s t : Finset V}

/-- A regular pair of disjoint sets for the graph coloring is uniform in Mathlib's sense at every
strictly larger parameter. -/
theorem IsRegularPair.isUniform (h : G.toPairColorSystem.IsRegularPair ε s t) (hst : Disjoint s t)
    (hε : ε < ε') : G.IsUniform ε' s t := by
  classical
  simpa using h.isUniform_colorGraph hst {true} (by simp) (by simpa using hε)

end TauCeti.PairColorSystem

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {ε : ℝ} {s t : Finset V}

/-- An `ε`-uniform pair of disjoint sets is `ε`-regular for the graph coloring: both the edge
and the non-edge color densities are `ε`-stable. -/
theorem IsUniform.isRegularPair_ofGraph (h : G.IsUniform ε s t) (hst : Disjoint s t) :
    G.toPairColorSystem.IsRegularPair ε s t := by
  classical
  refine PairColorSystem.isRegularPair_iff.mpr fun c s' hs' t' ht' hs ht => ?_
  rw [mul_comm] at hs ht
  cases c
  · rw [G.pairColorDensity_toPairColorSystem_false (hst.mono hs' ht'),
      G.pairColorDensity_toPairColorSystem_false hst]
    exact ((h.compl hst) hs' ht' hs ht).le
  · rw [G.pairColorDensity_toPairColorSystem_true (hst.mono hs' ht'),
      G.pairColorDensity_toPairColorSystem_true hst]
    exact (h hs' ht' hs ht).le

end SimpleGraph

namespace TauCeti.PairSkeleton3

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {P : Finpartition (univ : Finset V)} {ε ε' : ℝ}

/-- If the lower skeleton of a graph with vertex cells `P` is pair-color regular, then any two
distinct cells form a uniform pair at every strictly larger parameter. -/
theorem IsPairColorRegular.isUniform_of_ne
    (h : (⟨P, G.toPairColorSystem⟩ : PairSkeleton3 Bool V).IsPairColorRegular ε)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) (hε : ε < ε') :
    G.IsUniform ε' A B :=
  (h.isRegularPair hA hB).isUniform (P.disjoint hA hB hAB) hε

/-- If the lower skeleton of a graph with vertex cells `P` is pair-color regular, then `P` is a
uniform partition of `G` at every strictly larger parameter, in the sense of Szemerédi's
regularity lemma: in fact no pair of distinct cells is non-uniform. -/
theorem IsPairColorRegular.isUniform
    (h : (⟨P, G.toPairColorSystem⟩ : PairSkeleton3 Bool V).IsPairColorRegular ε)
    (hε : ε < ε') : P.IsUniform G ε' := by
  simpa using h.isUniform_colorGraph (K := {true}) (hK := by simp) (by simpa using hε)

end TauCeti.PairSkeleton3
