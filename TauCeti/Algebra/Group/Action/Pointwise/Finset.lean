/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import Mathlib.Data.Finset.SymmDiff
import TauCeti.Data.Finset.SymmDiff

/-!
# Symmetric differences of translates of finite sets

An element `g` acting injectively on a type `X` (for example, any element of a group acting on
`X`) moves a finite set `F ⊆ X` to a translate `g • F` of the same size, so `g • F` has as many
points outside `F` as `F` has outside `g • F`. Hence the symmetric difference `g • F ∆ F` has
twice as many points as `g • F \ F`.

For a monoid acting left-cancellatively on `X`, the size `|gF △ F|` of the translation boundary of
`F` satisfies a triangle bound in `g`, extending to list words and natural powers. Together with
`|({1} ∪ S) • F| ≤ (∑ g ∈ S, |gF \ F|) + |F|`, this relates boundary sums to Cayley-ball expansion.
For a group action, `|g⁻¹F △ F| = |gF △ F|` extends power bounds to integer exponents and shows
that the boundary under any element (or finite subset) of `Subgroup.closure S` is bounded,
uniformly in `F`, by a multiple of the sum of the boundaries for finitely many elements of `S`.
This lets Følner conditions be tested on generators only.

## Main results

* `Finset.card_smul_finset_symmDiff`: `#((g • F) ∆ F) = 2 * #(g • F \ F)`.
* `Finset.card_smul_finset_symmDiff_smul_finset`: `#((g • s) ∆ (g • t)) = #(s ∆ t)`.
* `Finset.card_mul_smul_finset_symmDiff_le`:
  `#(((g * h) • F) ∆ F) ≤ #((g • F) ∆ F) + #((h • F) ∆ F)`.
* `Finset.card_list_prod_smul_finset_symmDiff_le`, `Finset.card_pow_smul_finset_symmDiff_le`:
  word and natural-power bounds for `#((g • F) ∆ F)`.
* `Finset.card_insert_one_smul_finset_le`:
  `#(insert 1 S • F) ≤ (∑ g ∈ S, #(g • F \ F)) + #F`.
* `Finset.card_inv_smul_finset_symmDiff`: `#((g⁻¹ • F) ∆ F) = #((g • F) ∆ F)`.
* `Finset.card_zpow_smul_finset_symmDiff_le`: `#((g ^ n • F) ∆ F) ≤ n.natAbs * #((g • F) ∆ F)`.
* `Finset.exists_card_smul_finset_symmDiff_le_mul_sum`,
  `Finset.exists_finset_card_smul_symmDiff_le_of_subset_closure`: quantitative generator-to-test-set
  boundary bounds for elements and finite subsets of `Subgroup.closure S`.

## References

* A. Garrido, *An introduction to amenable groups*, Lemma 3.4.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open scoped BigOperators Pointwise symmDiff

namespace Finset

section LeftCancel

variable {G X : Type*} [SMul G X] [IsLeftCancelSMul G X] [DecidableEq X]

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

end LeftCancel

section Monoid

variable {G X : Type*} [Monoid G] [MulAction G X] [IsLeftCancelSMul G X] [DecidableEq X]

/-- **Triangle bound** for translation boundaries: the boundary of a finite set under a product
`g * h` has at most as many points as the boundaries under `g` and `h` together. -/
@[to_additive /-- **Triangle bound** for translation boundaries: the boundary of a finite set
under a sum `g + h` has at most as many points as the boundaries under `g` and `h` together. -/]
theorem card_mul_smul_finset_symmDiff_le (g h : G) (F : Finset X) :
    #(((g * h) • F) ∆ F) ≤ #((g • F) ∆ F) + #((h • F) ∆ F) :=
  calc #(((g * h) • F) ∆ F)
      ≤ #(((g * h) • F) ∆ (g • F)) + #((g • F) ∆ F) := card_symmDiff_le _ (g • F) _
    _ = #((h • F) ∆ F) + #((g • F) ∆ F) := by
        rw [mul_smul, card_smul_finset_symmDiff_smul_finset]
    _ = #((g • F) ∆ F) + #((h • F) ∆ F) := add_comm _ _

/-- Subadditivity of translation symmetric-difference cardinality along a list sum. -/
theorem card_list_sum_vadd_finset_symmDiff_le {A X : Type*} [AddMonoid A] [AddAction A X]
    [IsLeftCancelVAdd A X] [DecidableEq X] (L : List A) (F : Finset X) :
    #((L.sum +ᵥ F) ∆ F) ≤ (L.map fun g ↦ #((g +ᵥ F) ∆ F)).sum :=
  L.le_sum_of_subadditive (fun g ↦ #((g +ᵥ F) ∆ F)) (by simp) fun g h ↦
    card_add_vadd_finset_symmDiff_le g h F

/-- Subadditivity of translation symmetric-difference cardinality along a list product. -/
@[to_additive existing]
theorem card_list_prod_smul_finset_symmDiff_le (L : List G) (F : Finset X) :
    #((L.prod • F) ∆ F) ≤ (L.map fun g ↦ #((g • F) ∆ F)).sum :=
  L.apply_prod_le_sum_map (fun g ↦ #((g • F) ∆ F)) (by simp) fun g h ↦
    card_mul_smul_finset_symmDiff_le g h F

/-- Bound on `#((g ^ n • F) ∆ F)` for natural powers in an injectively acting monoid. -/
@[to_additive
/-- Bound on `#(((n • g) +ᵥ F) ∆ F)` for natural multiples in an injectively acting additive
monoid. -/]
theorem card_pow_smul_finset_symmDiff_le (g : G) (n : ℕ) (F : Finset X) :
    #((g ^ n • F) ∆ F) ≤ n * #((g • F) ∆ F) := by
  simpa only [List.prod_replicate, List.map_replicate, List.sum_replicate, smul_eq_mul] using
    card_list_prod_smul_finset_symmDiff_le (List.replicate n g) F

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

/-- The boundary of a finite set under `g⁻¹` has as many points as its boundary under `g`. -/
@[to_additive (attr := simp) /-- The boundary of a finite set under `-g` has as many points as its
boundary under `g`. -/]
theorem card_inv_smul_finset_symmDiff (g : G) (F : Finset X) :
    #((g⁻¹ • F) ∆ F) = #((g • F) ∆ F) := by
  rw [← card_smul_finset g ((g⁻¹ • F) ∆ F), smul_finset_symmDiff, smul_inv_smul, symmDiff_comm]

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
        rw [Int.natAbs_negSucc, card_inv_smul_finset_symmDiff]

/-- The boundary of a finite set under an element `g` of the subgroup generated by `S` is
controlled by finitely many elements of `S`: there are a finite `T ⊆ S` and `n : ℕ` such that
`|gF △ F| ≤ n · ∑_{t ∈ T} |tF △ F|` for every finite set `F`. -/
@[to_additive /-- The boundary of a finite set under an element `g` of the additive subgroup
generated by `S` is controlled by finitely many elements of `S`: there are a finite `T ⊆ S` and
`n : ℕ` such that `|(g +ᵥ F) △ F| ≤ n · ∑_{t ∈ T} |(t +ᵥ F) △ F|` for every finite set `F`. -/]
theorem exists_card_smul_finset_symmDiff_le_mul_sum {S : Set G} {g : G}
    (hg : g ∈ Subgroup.closure S) :
    ∃ T : Finset G, (T : Set G) ⊆ S ∧ ∃ n : ℕ, ∀ F : Finset X,
      #((g • F) ∆ F) ≤ n * ∑ t ∈ T, #((t • F) ∆ F) := by
  classical
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact ⟨{x}, by simpa using hx, 1, fun F => by simp⟩
  | one => exact ⟨∅, by simp, 0, fun F => by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨T₁, hT₁, n₁, h₁⟩ := hx
    obtain ⟨T₂, hT₂, n₂, h₂⟩ := hy
    refine ⟨T₁ ∪ T₂, by simpa using And.intro hT₁ hT₂, n₁ + n₂, fun F => ?_⟩
    calc #(((x * y) • F) ∆ F) ≤ #((x • F) ∆ F) + #((y • F) ∆ F) :=
          card_mul_smul_finset_symmDiff_le x y F
      _ ≤ n₁ * ∑ t ∈ T₁, #((t • F) ∆ F) + n₂ * ∑ t ∈ T₂, #((t • F) ∆ F) :=
          Nat.add_le_add (h₁ F) (h₂ F)
      _ ≤ (n₁ + n₂) * ∑ t ∈ T₁ ∪ T₂, #((t • F) ∆ F) := by
          rw [Nat.add_mul]
          exact Nat.add_le_add (Nat.mul_le_mul_left _ (sum_le_sum_of_subset subset_union_left))
            (Nat.mul_le_mul_left _ (sum_le_sum_of_subset subset_union_right))
  | inv x _ hx =>
    obtain ⟨T, hT, n, h⟩ := hx
    exact ⟨T, hT, n, fun F => (card_inv_smul_finset_symmDiff x F).trans_le (h F)⟩

/-- Quantitative generator-to-test-set bound: for any finite set `K` contained in
`Subgroup.closure S`, there exist a finite `K₀ ⊆ S` and `M : ℕ` bounding `#((g • F) ∆ F)` for all
`g ∈ K` and `F : Finset X` simultaneously. -/
@[to_additive
/-- Quantitative generator-to-test-set bound: for any finite set `K` contained in
`AddSubgroup.closure S`, there exist a finite `K₀ ⊆ S` and `M : ℕ` bounding `#((g +ᵥ F) ∆ F)` for
all `g ∈ K` and `F : Finset X` simultaneously. -/]
theorem exists_finset_card_smul_symmDiff_le_of_subset_closure {S : Set G} {K : Finset G}
    (hK : (K : Set G) ⊆ Subgroup.closure S) :
    ∃ K₀ : Finset G, (K₀ : Set G) ⊆ S ∧ ∃ M : ℕ,
      ∀ F : Finset X, ∀ g ∈ K, #((g • F) ∆ F) ≤ M * ∑ s ∈ K₀, #((s • F) ∆ F) := by
  classical
  induction K using Finset.induction with
  | empty => exact ⟨∅, by simp, 0, fun _ _ hg ↦ (notMem_empty _ hg).elim⟩
  | insert g K hgK ih =>
    rw [coe_insert, Set.insert_subset_iff] at hK
    obtain ⟨K₁, hK₁, M₁, hM₁⟩ := exists_card_smul_finset_symmDiff_le_mul_sum (X := X) hK.1
    obtain ⟨K₂, hK₂, M₂, hM₂⟩ := ih hK.2
    refine ⟨K₁ ∪ K₂, coe_union K₁ K₂ ▸ Set.union_subset hK₁ hK₂, max M₁ M₂, fun F x hx ↦ ?_⟩
    rcases mem_insert.1 hx with rfl | hxK
    · exact (hM₁ F).trans (Nat.mul_le_mul (le_max_left _ _)
        (sum_le_sum_of_subset subset_union_left))
    · exact (hM₂ F x hxK).trans (Nat.mul_le_mul (le_max_right _ _)
        (sum_le_sum_of_subset subset_union_right))

end Group

end Finset
