/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import TauCeti.Data.Finset.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Vertex-box regularity of pair colors

`PairColorSystem.IsVertexBoxRegularPair S ε s t` is the arity-two form of the vertex-box
condition `Colored3Graph.IsVertexBoxRegularOverPolyad`: at arity two a polyad is just a pair of
vertex sets `(s, t)`, its support is the set of ordered distinct pairs in `s ×ˢ t`, and the
relative density of a color is `pairColorDensity`. The condition asks that every color has density
within `ε` of its density on `(s, t)` over every vertex box `s' ×ˢ t'`, with `s' ⊆ s` and
`t' ⊆ t`, carrying at least an `ε`-fraction of the support.

Pair regularity `PairColorSystem.IsRegularPair` instead thresholds the two sides separately, by
`ε * #s ≤ #s'` and `ε * #t ≤ #t'`. This file compares the two conditions for the pairs of cells of
a partition, which are either equal or disjoint.

* A regular pair is vertex-box regular with the same parameter.
* For disjoint sets and `0 ≤ ε`, vertex-box regularity at `δ ≤ ε ^ 2` gives pair regularity at
  `ε`, since a box of two sides of relative sizes at least `ε` has relative size at least `ε ^ 2`.
* For a set paired with itself, the converse needs large sets: once `ε * #s ≤ 1`, the box
  `{u} ×ˢ {u}` passes the thresholds of pair regularity at `ε`, where every color has density
  zero, but it carries no distinct pair, so the vertex-box condition at a positive parameter
  never tests it. If `2 ≤ ε * #s`, vertex-box regularity at `δ` with
  `2 * δ ≤ ε ^ 2` gives pair regularity at `ε`.

For lower skeletons this says that pair-color regularity implies vertex-box regularity of every
pair of cells, and conversely when all cells are large.

## Main definitions

* `TauCeti.PairColorSystem.IsVertexBoxRegularPair`: the vertex-box condition for a pair of sets.

## Main results

* `TauCeti.PairColorSystem.IsRegularPair.isVertexBoxRegularPair`: regular pairs of equal or
  disjoint sets are vertex-box regular.
* `TauCeti.PairColorSystem.IsVertexBoxRegularPair.isRegularPair_of_disjoint`: the converse for
  disjoint sets, at the squared parameter.
* `TauCeti.PairColorSystem.IsVertexBoxRegularPair.isRegularPair_self`: the converse for a large
  set paired with itself.
* `TauCeti.PairSkeleton3.IsPairColorRegular.isVertexBoxRegularPair` and
  `TauCeti.PairSkeleton3.isPairColorRegular_of_forall_isVertexBoxRegularPair`: the comparison for
  the cells of a lower skeleton.

## References

* V. Rödl, M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* B. Nagle, V. Rödl and M. Schacht, *The counting lemma for regular k-uniform hypergraphs*,
  Random Structures Algorithms 28 (2006).
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*}

namespace PairColorSystem

variable [DecidableEq V] {S : PairColorSystem κ V} {ε ε' δ : ℝ} {s t : Finset V}

variable (S) in
/-- The pair `(s, t)` is `ε`-vertex-box-regular for the pair-color system `S` when, for every color
and all `s' ⊆ s` and `t' ⊆ t` such that the ordered distinct pairs in `s' ×ˢ t'` are at least an
`ε`-fraction of those in `s ×ˢ t`, the density of the color on `(s', t')` is within `ε` of its
density on `(s, t)`. -/
def IsVertexBoxRegularPair (ε : ℝ) (s t : Finset V) : Prop :=
  ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
    ε * #{p ∈ s ×ˢ t | p.1 ≠ p.2} ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} →
      |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε

/-- Unfolded form of `PairColorSystem.IsVertexBoxRegularPair`. -/
theorem isVertexBoxRegularPair_iff : S.IsVertexBoxRegularPair ε s t ↔
    ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
      ε * #{p ∈ s ×ˢ t | p.1 ≠ p.2} ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} →
        |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε :=
  Iff.rfl

/-- Vertex-box regularity is monotone in its parameter. -/
theorem IsVertexBoxRegularPair.mono (h : S.IsVertexBoxRegularPair ε s t) (hε : ε ≤ ε') :
    S.IsVertexBoxRegularPair ε' s t :=
  fun c s' hs' t' ht' hN ↦
    (h c s' hs' t' ht' ((mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans hN)).trans hε

/-- Exchanging the two sets preserves vertex-box regularity. -/
theorem IsVertexBoxRegularPair.symm (h : S.IsVertexBoxRegularPair ε s t) :
    S.IsVertexBoxRegularPair ε t s := by
  intro c t' ht' s' hs' hN
  rw [card_filter_ne_product_comm, card_filter_ne_product_comm s'] at hN
  have hc := h (S.rev c) s' hs' t' ht' hN
  rwa [← pairColorDensity_swap S (S.rev c) s' t', ← pairColorDensity_swap S (S.rev c) s t,
    rev_rev] at hc

/-- Vertex-box regularity is symmetric in the two sets. -/
theorem isVertexBoxRegularPair_comm :
    S.IsVertexBoxRegularPair ε s t ↔ S.IsVertexBoxRegularPair ε t s :=
  ⟨IsVertexBoxRegularPair.symm, IsVertexBoxRegularPair.symm⟩

/-- A vertex-box regular pair for a nonempty palette has a nonnegative parameter: for a negative
parameter, the empty box passes the size threshold. -/
theorem IsVertexBoxRegularPair.nonneg [Nonempty κ] (h : S.IsVertexBoxRegularPair ε s t) :
    0 ≤ ε := by
  by_contra! hε
  refine (abs_nonneg _).not_gt ((h (Classical.arbitrary κ) ∅ (empty_subset _) ∅ (empty_subset _)
    ?_).trans_lt hε)
  simpa using mul_nonpos_of_nonpos_of_nonneg hε.le (Nat.cast_nonneg _)

/-- **Pair regularity implies vertex-box regularity.** A regular pair of sets that are equal or
disjoint, such as two cells of a partition, is vertex-box regular with the same parameter: a box
carrying an `ε`-fraction of the distinct pairs has sides of relative sizes at least `ε`. -/
theorem IsRegularPair.isVertexBoxRegularPair (h : S.IsRegularPair ε s t)
    (hst : s = t ∨ Disjoint s t) : S.IsVertexBoxRegularPair ε s t := by
  intro c s' hs' t' ht' hN
  have hε : 0 ≤ ε := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  obtain h₀ | h₀ := Nat.eq_zero_or_pos #{p ∈ s ×ˢ t | p.1 ≠ p.2}
  · -- Without distinct pairs, both densities vanish.
    have h₀' : #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} = 0 :=
      Nat.eq_zero_of_le_zero
        (h₀ ▸ card_le_card (filter_subset_filter _ (product_subset_product hs' ht')))
    rw [pairColorDensity_eq_zero_of_support_eq_empty S c s t (card_eq_zero.1 h₀),
      pairColorDensity_eq_zero_of_support_eq_empty S c s' t' (card_eq_zero.1 h₀')]
    simpa using hε
  -- A box passing the vertex-box threshold has its first side passing the threshold of pair
  -- regularity; applied to `(s, t)` and to `(t, s)`.
  have key {s t s' t' : Finset V} (hst : s = t ∨ Disjoint s t) (hs' : s' ⊆ s) (ht' : t' ⊆ t)
      (h₀ : 0 < #{p ∈ s ×ˢ t | p.1 ≠ p.2})
      (hN : ε * #{p ∈ s ×ˢ t | p.1 ≠ p.2} ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2}) : ε * #s ≤ #s' := by
    have hle : (#{p ∈ s' ×ˢ t' | p.1 ≠ p.2} * #s : ℝ) ≤ #s' * #{p ∈ s ×ˢ t | p.1 ≠ p.2} := by
      exact_mod_cast card_filter_ne_product_mul_card_le hst hs' ht'
    refine le_of_mul_le_mul_right ?_ (show (0 : ℝ) < #{p ∈ s ×ˢ t | p.1 ≠ p.2} by
      exact_mod_cast h₀)
    calc ε * #s * #{p ∈ s ×ˢ t | p.1 ≠ p.2}
        = ε * #{p ∈ s ×ˢ t | p.1 ≠ p.2} * #s := by ring
      _ ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} * #s := by gcongr
      _ ≤ #s' * #{p ∈ s ×ˢ t | p.1 ≠ p.2} := hle
  refine isRegularPair_iff.1 h c s' hs' t' ht' (key hst hs' ht' h₀ hN) ?_
  rw [← card_filter_ne_product_comm s] at h₀ hN
  rw [← card_filter_ne_product_comm s'] at hN
  exact key (hst.imp Eq.symm fun h ↦ h.symm) ht' hs' h₀ hN

/-- **Vertex-box regularity implies pair regularity for disjoint sets.** If `(s, t)` is a
`δ`-vertex-box-regular pair of disjoint sets and `δ ≤ ε ^ 2`, then it is `ε`-regular: sides of
relative sizes at least `ε` span a box of relative size at least `ε ^ 2`. -/
theorem IsVertexBoxRegularPair.isRegularPair_of_disjoint (h : S.IsVertexBoxRegularPair δ s t)
    (hst : Disjoint s t) (hε : 0 ≤ ε) (hδ : δ ≤ ε ^ 2) : S.IsRegularPair ε s t := by
  obtain hε₁ | hε₁ := le_or_gt 1 ε
  · exact isRegularPair_of_one_le hε₁
  refine isRegularPair_iff.2 fun c s' hs' t' ht' hs ht ↦ ?_
  refine (h c s' hs' t' ht' ?_).trans (hδ.trans (by nlinarith))
  rw [filter_ne_product_of_disjoint hst, filter_ne_product_of_disjoint (hst.mono hs' ht'),
    card_product, card_product, Nat.cast_mul, Nat.cast_mul]
  have hδ' : δ * (#s * #t) ≤ ε ^ 2 * (#s * #t) := by gcongr
  nlinarith [mul_le_mul hs ht (by positivity) (Nat.cast_nonneg _)]

/-- **Vertex-box regularity implies pair regularity for a large set paired with itself.** If
`(s, s)` is `δ`-vertex-box-regular, `2 * δ ≤ ε ^ 2` and `2 ≤ ε * #s`, then `(s, s)` is
`ε`-regular. Some size condition is needed: once `ε * #s ≤ 1`, the box `{u} ×ˢ {u}` passes
the thresholds of pair regularity but carries no distinct pair. -/
theorem IsVertexBoxRegularPair.isRegularPair_self (h : S.IsVertexBoxRegularPair δ s s)
    (hδ : 2 * δ ≤ ε ^ 2) (hs : 2 ≤ ε * #s) : S.IsRegularPair ε s s := by
  have hε : 0 ≤ ε := by nlinarith [(Nat.cast_nonneg (α := ℝ) #s)]
  obtain hε₁ | hε₁ := le_or_gt 1 ε
  · exact isRegularPair_of_one_le hε₁
  refine isRegularPair_iff.2 fun c s' hs' t' ht' ha hb ↦ ?_
  have hδ₀ : 0 ≤ δ := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  refine (h c s' hs' t' ht' ?_).trans (by nlinarith)
  -- Each `u ∈ s'` is paired with at least `#t' - 1 ≥ #t' / 2` elements of `t'`.
  have hlow : #s' * (#t' - 1) ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} := by
    rw [card_filter_ne_product, ← smul_eq_mul, ← sum_const]
    exact sum_le_sum fun u _ ↦ pred_card_le_card_erase
  have ht'₂ : (2 : ℝ) ≤ #t' := hs.trans hb
  have hlow' : (#s' : ℝ) * (#t' - 1) ≤ #{p ∈ s' ×ˢ t' | p.1 ≠ p.2} := by
    have ht'₁ : 1 ≤ #t' := by exact_mod_cast (show (1 : ℝ) ≤ #t' by linarith)
    have := (Nat.cast_le (α := ℝ)).2 hlow
    rwa [Nat.cast_mul, Nat.cast_sub ht'₁, Nat.cast_one] at this
  have hN : (#{p ∈ s ×ˢ s | p.1 ≠ p.2} : ℝ) ≤ #s * #s := by
    exact_mod_cast (card_filter_le _ _).trans_eq (card_product s s)
  have hab : ε * #s * (ε * #s) ≤ #s' * #t' := mul_le_mul ha hb (by positivity) (Nat.cast_nonneg _)
  calc δ * #{p ∈ s ×ˢ s | p.1 ≠ p.2} ≤ δ * (#s * #s) := by gcongr
    _ ≤ ε ^ 2 / 2 * (#s * #s) := by gcongr; linarith
    _ = ε * #s * (ε * #s) / 2 := by ring
    _ ≤ #s' * #t' / 2 := by gcongr
    _ ≤ #s' * (#t' - 1) := by nlinarith [(Nat.cast_nonneg (α := ℝ) #s')]
    _ ≤ _ := hlow'

end PairColorSystem

namespace PairSkeleton3

variable [Fintype V] [DecidableEq V] {S : PairSkeleton3 κ V} {ε δ : ℝ}

/-- In a pair-color regular lower skeleton, every ordered pair of vertex cells is vertex-box
regular with the same parameter. -/
theorem IsPairColorRegular.isVertexBoxRegularPair (h : S.IsPairColorRegular ε) {A B : Finset V}
    (hA : A ∈ S.vertexPart.parts) (hB : B ∈ S.vertexPart.parts) :
    S.pairColors.IsVertexBoxRegularPair ε A B :=
  (h.isRegularPair hA hB).isVertexBoxRegularPair <| (eq_or_ne A B).imp_right
    (S.vertexPart.disjoint hA hB)

/-- A lower skeleton whose vertex cells are pairwise vertex-box regular at `δ` is pair-color
regular at `ε`, provided `2 * δ ≤ ε ^ 2` and every cell `A` satisfies `2 ≤ ε * #A`. -/
theorem isPairColorRegular_of_forall_isVertexBoxRegularPair
    (h : ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts,
      S.pairColors.IsVertexBoxRegularPair δ A B)
    (hδ : 2 * δ ≤ ε ^ 2) (hcells : ∀ A ∈ S.vertexPart.parts, 2 ≤ ε * #A) :
    S.IsPairColorRegular ε := by
  refine isPairColorRegular_iff.2 fun c A hA B hB ↦ PairColorSystem.isRegularPair_iff.1 ?_ c
  obtain rfl | hAB := eq_or_ne A B
  · exact (h A hA A hA).isRegularPair_self hδ (hcells A hA)
  · have hε : 0 ≤ ε := by nlinarith [hcells A hA, (Nat.cast_nonneg (α := ℝ) #A)]
    exact (h A hA B hB).isRegularPair_of_disjoint (S.vertexPart.disjoint hA hB hAB) hε
      (by linarith [sq_nonneg ε])

end PairSkeleton3

end TauCeti
