/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Finset.SymmDiff
import TauCeti.Data.Finset.SymmDiff

/-!
# Symmetric differences of translates of finite sets

An element `g` acting injectively on a type `X` (for example, any element of a group acting on
`X`) moves a finite set `F ⊆ X` to a translate `g • F` of the same size, so `g • F` has as many
points outside `F` as `F` has outside `g • F`. Hence the symmetric difference `g • F ∆ F` has
twice as many points as `g • F \ F`. Combining translation invariance of cardinality with the
triangle inequality `#(s ∆ u) ≤ #(s ∆ t) + #(t ∆ u)` also gives subadditivity of `#((g • F) ∆ F)`
under products, powers, inverses, and words in the acting monoid or group. Følner-type arguments
use these identities to pass between symmetric and one-sided differences and to reduce Følner
conditions to generating sets.

## Main results

* `Finset.card_smul_finset_sdiff_eq`: `#(g • F \ F) = #(F \ g • F)`.
* `Finset.card_smul_finset_symmDiff`: `#((g • F) ∆ F) = 2 * #(g • F \ F)`.
* `Finset.card_mul_smul_finset_symmDiff_le`:
  `#(((g * h) • F) ∆ F) ≤ #((h • F) ∆ F) + #((g • F) ∆ F)`.
* `Finset.card_list_prod_smul_finset_symmDiff_le`: word bound for `#((L.prod • F) ∆ F)`.
* `Finset.card_insert_one_smul_finset_le`:
  `#(insert 1 S • F) ≤ (∑ g ∈ S, #(g • F \ F)) + #F`.
* `Finset.card_inv_smul_finset_symmDiff_self`: `#((g⁻¹ • F) ∆ F) = #((g • F) ∆ F)`.
* `Finset.card_zpow_smul_finset_symmDiff_le`: `#((g ^ n • F) ∆ F) ≤ n.natAbs * #((g • F) ∆ F)`.

## References

* A. Garrido, *An introduction to amenable groups*, Lemma 3.4.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open scoped BigOperators Pointwise symmDiff

namespace Finset

section IsLeftCancelSMul

variable {G X : Type*} [SMul G X] [IsLeftCancelSMul G X] [DecidableEq X]

/-- An injective action moves as many points of `F` outside `F` as it leaves uncovered in `F`. -/
@[to_additive
/-- An injective additive action moves as many points of `F` outside `F` as it leaves uncovered
in `F`. -/]
theorem card_smul_finset_sdiff_eq (g : G) (F : Finset X) : #(g • F \ F) = #(F \ g • F) :=
  card_sdiff_comm (card_smul_finset g F)

/-- A translate `g • F` of a finite set has as many points outside `F` as `F` has outside `g • F`,
so its symmetric difference with `F` has twice as many points as `g • F \ F`. -/
@[to_additive
/-- An additive translate `g +ᵥ F` of a finite set has as many points outside `F` as `F` has
outside `g +ᵥ F`, so its symmetric difference with `F` has twice as many points as
`g +ᵥ F \ F`. -/]
theorem card_smul_finset_symmDiff (g : G) (F : Finset X) : #((g • F) ∆ F) = 2 * #(g • F \ F) :=
  card_symmDiff_of_card_eq (card_smul_finset g F)

/-- An injective action preserves the cardinality of symmetric differences of finite sets. -/
@[to_additive (attr := simp)
/-- An injective additive action preserves the cardinality of symmetric differences of finite
sets. -/]
theorem card_smul_finset_symmDiff_smul_finset (g : G) (s t : Finset X) :
    #((g • s) ∆ (g • t)) = #(s ∆ t) := by
  rw [← smul_finset_symmDiff, card_smul_finset]

end IsLeftCancelSMul

section Monoid

variable {M X : Type*} [Monoid M] [MulAction M X] [IsLeftCancelSMul M X] [DecidableEq X]

/-- Subadditivity of translation symmetric-difference cardinality under multiplication. -/
@[to_additive
/-- Subadditivity of translation symmetric-difference cardinality under addition. -/]
theorem card_mul_smul_finset_symmDiff_le (g h : M) (F : Finset X) :
    #(((g * h) • F) ∆ F) ≤ #((h • F) ∆ F) + #((g • F) ∆ F) :=
  calc
    #(((g * h) • F) ∆ F) = #((g • (h • F)) ∆ F) := by rw [mul_smul]
    _ ≤ #((g • (h • F)) ∆ (g • F)) + #((g • F) ∆ F) := card_symmDiff_le _ (g • F) _
    _ = #((h • F) ∆ F) + #((g • F) ∆ F) := by rw [card_smul_finset_symmDiff_smul_finset]

/-- Subadditivity of translation symmetric-difference cardinality along a list product. -/
@[to_additive
/-- Subadditivity of translation symmetric-difference cardinality along a list sum. -/]
theorem card_list_prod_smul_finset_symmDiff_le (L : List M) (F : Finset X) :
    #((L.prod • F) ∆ F) ≤ (L.map fun g ↦ #((g • F) ∆ F)).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
    simpa only [List.prod_cons, List.map_cons, List.sum_cons, Nat.add_comm] using
      (card_mul_smul_finset_symmDiff_le g L.prod F).trans (Nat.add_le_add_right ih _)

/-- Bound on `#((g ^ n • F) ∆ F)` for natural powers in an injectively acting monoid. -/
@[to_additive
/-- Bound on `#(((n • g) +ᵥ F) ∆ F)` for natural multiples in an injectively acting additive
monoid. -/]
theorem card_pow_smul_finset_symmDiff_le (g : M) (n : ℕ) (F : Finset X) :
    #((g ^ n • F) ∆ F) ≤ n * #((g • F) ∆ F) := by
  simpa using card_list_prod_smul_finset_symmDiff_le (List.replicate n g) F

end Monoid

section InsertOne

variable {M X : Type*} [Monoid M] [MulAction M X] [DecidableEq M] [DecidableEq X]

/-- The cardinality of `({1} ∪ S) • F` exceeds `#F` by at most `∑ g ∈ S, #(g • F \ F)`. -/
@[to_additive
/-- The cardinality of `({0} ∪ S) +ᵥ F` exceeds `#F` by at most `∑ g ∈ S, #(g +ᵥ F \ F)`. -/]
theorem card_insert_one_smul_finset_le (S : Finset M) (F : Finset X) :
    #(insert (1 : M) S • F) ≤ (∑ g ∈ S, #(g • F \ F)) + #F := by
  have hsub : insert (1 : M) S • F \ F ⊆ S.biUnion fun g ↦ g • F \ F := by
    intro x hx
    rw [mem_sdiff, mem_smul] at hx
    obtain ⟨⟨g, hg, y, hy, rfl⟩, hxF⟩ := hx
    rcases mem_insert.1 hg with rfl | hgS
    · exact (hxF (by simpa using hy)).elim
    · exact mem_biUnion.2 ⟨g, hgS, mem_sdiff.2 ⟨smul_mem_smul_finset hy, hxF⟩⟩
  have hFsub : F ⊆ insert (1 : M) S • F := by
    simpa using smul_finset_subset_smul (t := F) (mem_insert_self 1 S)
  rw [← card_sdiff_add_card_eq_card hFsub]
  exact Nat.add_le_add_right ((card_le_card hsub).trans card_biUnion_le) _

end InsertOne

section Group

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- Moving an inverse action across a symmetric difference of finite sets preserves cardinality. -/
@[to_additive (attr := simp)
/-- Moving a negated additive action across a symmetric difference of finite sets preserves
cardinality. -/]
theorem card_symmDiff_inv_smul_finset (g : G) (s t : Finset X) :
    #(s ∆ (g⁻¹ • t)) = #((g • s) ∆ t) := by
  rw [← card_smul_finset_symmDiff_smul_finset g, smul_inv_smul]

/-- Moving an inverse action from the left argument of a symmetric difference to the right. -/
@[to_additive (attr := simp)
/-- Moving a negated additive action from the left argument of a symmetric difference to the
right. -/]
theorem card_inv_smul_finset_symmDiff (g : G) (s t : Finset X) :
    #((g⁻¹ • s) ∆ t) = #(s ∆ (g • t)) := by
  simpa [inv_inv] using (card_symmDiff_inv_smul_finset g⁻¹ s t).symm

/-- Translating a finite set by `g⁻¹` produces a symmetric difference of the same cardinality as
translating by `g`. -/
@[to_additive
/-- Translating a finite set by `-g` produces a symmetric difference of the same cardinality as
translating by `g`. -/]
theorem card_inv_smul_finset_symmDiff_self (g : G) (F : Finset X) :
    #((g⁻¹ • F) ∆ F) = #((g • F) ∆ F) := by
  rw [card_inv_smul_finset_symmDiff, symmDiff_comm]

/-- Bound on `#((g ^ n • F) ∆ F)` for integer powers in a group action. -/
@[to_additive
/-- Bound on `#(((n • g) +ᵥ F) ∆ F)` for integer multiples in an additive group action. -/]
theorem card_zpow_smul_finset_symmDiff_le (g : G) (n : ℤ) (F : Finset X) :
    #((g ^ n • F) ∆ F) ≤ n.natAbs * #((g • F) ∆ F) := by
  cases n with
  | ofNat k =>
    simpa using card_pow_smul_finset_symmDiff_le g k F
  | negSucc k =>
    calc
      #((g ^ Int.negSucc k • F) ∆ F) = #(((g⁻¹ ^ (k + 1)) • F) ∆ F) := by
        rw [zpow_negSucc, ← inv_pow]
      _ ≤ (k + 1) * #((g⁻¹ • F) ∆ F) := card_pow_smul_finset_symmDiff_le g⁻¹ (k + 1) F
      _ = (Int.negSucc k).natAbs * #((g • F) ∆ F) := by
        rw [Int.natAbs_negSucc, card_inv_smul_finset_symmDiff_self]

end Group

end Finset
