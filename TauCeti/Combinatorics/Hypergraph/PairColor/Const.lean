/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
import Mathlib.Tactic.Linarith
import TauCeti.Data.Finset.Basic

/-!
# The constant pair coloring

`PairColorSystem.const c` gives every ordered distinct pair the color `c`, with the identity as
palette reversal. It is the lower skeleton coloring of the coarsest triadic complexes, which have
a single pair color.

Its density in `c` is one on every pair of sets that contains an ordered distinct pair, and zero
otherwise; every other color has density zero. Consequently the regularity of the constant
coloring is decided by the singleton tests alone:

* a pair of disjoint sets is `ε`-regular for every `ε > 0`
  (`PairColorSystem.isRegularPair_const_of_disjoint`);
* for `ε ≥ 0`, a set paired with itself is `ε`-regular exactly when it has at most one
  element or more than `1 / ε` elements (`PairColorSystem.isRegularPair_const_self_iff`). A set
  `A` with `2 ≤ #A ≤ 1 / ε` fails at the tests `{v}` and `{v}` for `v ∈ A`, which contain no
  distinct pair and so have density zero, against density one on `(A, A)`.

So a lower skeleton with the constant coloring is `ε`-pair-color regular exactly when each of its
cells has at most one element or more than `1 / ε` elements
(`PairSkeleton3.isPairColorRegular_const_iff`), while a test of the pairs of distinct cells alone
would accept every partition. Because pair densities are taken among ordered distinct pairs, the
diagonal tests matter even for a coloring this simple.

## Main definitions

* `TauCeti.PairColorSystem.const`: the coloring of all ordered distinct pairs by one color.

## Main results

* `TauCeti.PairColorSystem.pairColorDensity_const_self`: the density of the constant color is one
  on every pair of sets containing an ordered distinct pair.
* `TauCeti.PairColorSystem.pairColorDensity_const_of_ne`: every other color has density zero.
* `TauCeti.PairColorSystem.isRegularPair_const_of_disjoint`: disjoint sets form regular pairs.
* `TauCeti.PairColorSystem.isRegularPair_const_self_iff`: the diagonal regularity criterion.
* `TauCeti.PairSkeleton3.isPairColorRegular_const_iff`: the regularity criterion for a lower
  skeleton with the constant coloring.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*}

namespace PairColorSystem

/-- The constant pair coloring: every ordered distinct pair of `V` has the color `c`, and palette
reversal is the identity. -/
def const (c : κ) : PairColorSystem κ V where
  color _ := c
  rev := id
  rev_involutive _ := rfl
  color_rev _ := rfl

variable {c c' : κ} {ε : ℝ} {s t : Finset V}

@[simp]
theorem const_color (c : κ) (p : {p : V × V // p.1 ≠ p.2}) : (const c).color p = c :=
  (rfl)

@[simp]
theorem const_rev (c c' : κ) : (const c : PairColorSystem κ V).rev c' = c' :=
  (rfl)

/-- The total color of the constant coloring is `c` off the diagonal. -/
@[simp]
theorem colorOfPair_const_eq_some_iff (u v : V) : (const c).colorOfPair u v = some c' ↔
    u ≠ v ∧ c = c' := by
  simp [colorOfPair_eq_some_iff]

/-- The constant color has density one on every pair of sets containing an ordered distinct
pair. -/
theorem pairColorDensity_const_self [DecidableEq V]
    (h : ((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2).Nonempty) :
    pairColorDensity (const c) c s t = 1 := by
  classical
  rw [pairColorDensity_def]
  simp only [colorOfPair_const_eq_some_iff, and_true]
  exact div_self (Nat.cast_ne_zero.2 h.card_pos.ne')

/-- Every color other than the constant one has density zero. -/
theorem pairColorDensity_const_of_ne (hc : c' ≠ c) (s t : Finset V) :
    pairColorDensity (const c) c' s t = 0 := by
  classical
  rw [pairColorDensity_def]
  simp [colorOfPair_const_eq_some_iff, Ne.symm hc]

/-- Two pairs of sets with ordered distinct pairs give every color the same density in the
constant coloring. -/
private theorem pairColorDensity_const_eq [DecidableEq V] {s' t' : Finset V}
    (h : ((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2).Nonempty)
    (h' : ((s' ×ˢ t').filter fun p ↦ p.1 ≠ p.2).Nonempty) (c' : κ) :
    pairColorDensity (const c) c' s' t' = pairColorDensity (const c) c' s t := by
  by_cases hc : c' = c
  · rw [hc, pairColorDensity_const_self h, pairColorDensity_const_self h']
  · rw [pairColorDensity_const_of_ne hc, pairColorDensity_const_of_ne hc]

/-- **Regularity between disjoint sets.** In the constant coloring, two disjoint sets form an
`ε`-regular pair for every `ε > 0`: every test of positive size sees one color with density one. -/
theorem isRegularPair_const_of_disjoint (hε : 0 < ε) (hst : Disjoint s t)
    (c : κ) : (const c).IsRegularPair ε s t := by
  classical
  refine isRegularPair_iff.2 fun c' s' hs' t' ht' hs ht ↦ ?_
  obtain rfl | hsn := s.eq_empty_or_nonempty
  · rw [subset_empty.1 hs']
    simpa using hε.le
  obtain rfl | htn := t.eq_empty_or_nonempty
  · rw [subset_empty.1 ht']
    simpa using hε.le
  -- Both tests are nonempty, so both rectangles contain distinct pairs.
  have hs'n : s'.Nonempty :=
    card_pos.1 (by exact_mod_cast (by positivity : 0 < ε * #s).trans_le hs)
  have ht'n : t'.Nonempty :=
    card_pos.1 (by exact_mod_cast (by positivity : 0 < ε * #t).trans_le ht)
  rw [pairColorDensity_const_eq (by rw [filter_ne_product_of_disjoint hst]; exact hsn.product htn)
    (by rw [filter_ne_product_of_disjoint (hst.mono hs' ht')]; exact hs'n.product ht'n), sub_self,
    abs_zero]
  exact hε.le

/-- **Regularity of a set with itself.** For `ε ≥ 0`, a set `A` paired with itself is `ε`-regular
in the constant coloring exactly when it has at most one element or more than `1 / ε` elements.
Otherwise the tests `{v}` and `{v}` for `v ∈ A` are large enough, contain no ordered distinct pair,
and so have density zero against density one on `(A, A)`. -/
theorem isRegularPair_const_self_iff {A : Finset V} (hε : 0 ≤ ε) (c : κ) :
    (const c).IsRegularPair ε A A ↔ #A ≤ 1 ∨ 1 < ε * #A := by
  classical
  constructor
  · intro h
    by_contra! hA
    obtain ⟨hA₁, hA₂⟩ := hA
    obtain ⟨v, hv⟩ := card_pos.1 (by omega : 0 < #A)
    have hv' := singleton_subset_iff.2 hv
    have := isRegularPair_iff.1 h c {v} hv' {v} hv' (by simpa using hA₂) (by simpa using hA₂)
    rw [pairColorDensity_singleton_self, pairColorDensity_const_self
      (filter_ne_product_nonempty hA₁ ⟨v, hv⟩)] at this
    simp only [Rat.cast_zero, Rat.cast_one, zero_sub, abs_neg, abs_one] at this
    -- The singleton tests force `1 ≤ ε`, so `ε * #A ≥ 2`, against `ε * #A ≤ 1`.
    have h₂ : (2 : ℝ) ≤ #A := by exact_mod_cast hA₁
    nlinarith
  · intro hA
    refine isRegularPair_iff.2 fun c' s' hs' t' ht' hs ht ↦ ?_
    by_cases hA₁ : #A ≤ 1
    · -- No subset of `A` contains an ordered distinct pair, so every density vanishes.
      have hnone {s t : Finset V} (hs : s ⊆ A) (ht : t ⊆ A) :
          (s ×ˢ t).filter (fun p ↦ p.1 ≠ p.2) = ∅ :=
        filter_false_of_mem fun p hp ↦ not_not.2 <| card_le_one.1 hA₁ _
          (hs (mem_product.1 hp).1) _ (ht (mem_product.1 hp).2)
      rw [pairColorDensity_eq_zero_of_support_eq_empty _ _ _ _ (hnone hs' ht'),
        pairColorDensity_eq_zero_of_support_eq_empty _ _ _ _ (hnone subset_rfl subset_rfl)]
      simpa using hε
    · -- Every test has at least two elements, so it contains an ordered distinct pair.
      have hA₂ := hA.resolve_left hA₁
      have hs₁ : 1 < #s' := by exact_mod_cast hA₂.trans_le hs
      have ht₁ : 1 < #t' := by exact_mod_cast hA₂.trans_le ht
      rw [pairColorDensity_const_eq
        (filter_ne_product_nonempty (not_le.1 hA₁) (card_pos.1 (by omega : 0 < #A)))
        (filter_ne_product_nonempty hs₁ (card_pos.1 (by omega : 0 < #t'))),
        sub_self, abs_zero]
      exact hε

end PairColorSystem

namespace PairSkeleton3

variable [Fintype V] [DecidableEq V] {ε : ℝ}

/-- **Regularity of a lower skeleton with the constant coloring.** For `ε > 0`, the lower skeleton
with vertex cells `P` and the constant coloring is `ε`-pair-color regular exactly when every cell
has at most one element or more than `1 / ε` elements. -/
theorem isPairColorRegular_const_iff (P : Finpartition (univ : Finset V)) (c : κ) (hε : 0 < ε) :
    (⟨P, .const c⟩ : PairSkeleton3 κ V).IsPairColorRegular ε ↔
      ∀ A ∈ P.parts, #A ≤ 1 ∨ 1 < ε * #A := by
  refine ⟨fun h A hA ↦ (PairColorSystem.isRegularPair_const_self_iff hε.le c).1
    (h.isRegularPair hA hA), fun h ↦ isPairColorRegular_iff.2 fun c' A hA B hB ↦ ?_⟩
  refine PairColorSystem.isRegularPair_iff.1 ?_ c'
  obtain rfl | hAB := eq_or_ne A B
  · exact (PairColorSystem.isRegularPair_const_self_iff hε.le c).2 (h A hA)
  · exact PairColorSystem.isRegularPair_const_of_disjoint hε (P.disjoint hA hB hAB) c

end PairSkeleton3

end TauCeti
