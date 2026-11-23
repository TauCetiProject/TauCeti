/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Covers by boundedly many proper subspaces have finite character

Let `V` be a finite-dimensional vector space over a division ring `K`, let `A ⊆ V` and `t : ℕ`.
If every finite subset of `A` is contained in the union of at most `t` proper subspaces of `V`,
then so is `A` itself. Equivalently, if no `t` proper subspaces cover `A`, then some finite subset
of `A` already has this property.

Finiteness theorems for linear equations in multiplicative groups of finite rank use this to pass
from finite sets of solutions to the full solution set: a uniform bound for the number of proper
subspaces needed to cover each finite set of solutions, which lie in finitely generated subgroups
and a common number field, becomes a bound for the whole set, with no finite generation assumed of
the ambient group.

The proof follows the span/cover induction of Evertse–Schlickewei–Schmidt, Section 6.

Finite-dimensionality is necessary: if `A` is a basis of an infinite-dimensional space, every
finite subset of `A` lies in one proper subspace, but `A` spans the whole space.

## Main results

* `Submodule.exists_finite_subset_forall_not_subset_biUnion`: if no family of at most `t` proper
  subspaces covers `A`, neither does any such family cover some finite subset of `A`.
* `Submodule.exists_subset_biUnion_iff_forall_finite`: `A` is covered by at most `t` proper
  subspaces if and only if each of its finite subsets is.

## References

* J.-H. Evertse, H. P. Schlickewei, W. M. Schmidt, *Linear equations in variables which lie in a
  multiplicative group*, Ann. of Math. 155 (2002), 807–836, Section 6.
-/

public section

open Finset Module Set

namespace Submodule

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {A : Set V} {t : ℕ}

/-- The span/cover induction: if no proper family of at most `t` subspaces covers `A`, then for
each `k` some finite `F ⊆ A` forces every proper family `𝒲` of at most `t` subspaces covering `F`
to have measure `∑ W ∈ 𝒲, finrank K (span K (W ∩ F))` at least `k`. -/
private theorem exists_finite_subset_le_sum_finrank_span_inter
    (hA : ∀ 𝒲 : Finset (Submodule K V), #𝒲 ≤ t → (∀ W ∈ 𝒲, W ≠ ⊤) →
      ¬A ⊆ ⋃ W ∈ 𝒲, (W : Set V)) (k : ℕ) :
    ∃ F ⊆ A, F.Finite ∧ ∀ 𝒲 : Finset (Submodule K V), #𝒲 ≤ t → (∀ W ∈ 𝒲, W ≠ ⊤) →
      F ⊆ ⋃ W ∈ 𝒲, (W : Set V) → k ≤ ∑ W ∈ 𝒲, finrank K (span K ((W : Set V) ∩ F)) := by
  classical
  induction k with
  | zero => exact ⟨∅, empty_subset _, finite_empty, fun _ _ _ _ ↦ Nat.zero_le _⟩
  | succ k ih =>
    obtain ⟨F, hFA, hF, hk⟩ := ih
    -- `A` is not covered by the empty family, so it is nonempty
    obtain ⟨a₀, ha₀⟩ : A.Nonempty := by
      by_contra h
      exact hA ∅ (by simp) (by simp) (by simp [not_nonempty_iff_eq_empty.mp h])
    -- a point of `A` outside each proper family of at most `t` subspaces
    have hw (𝒰 : Finset (Submodule K V)) :
        ∃ a ∈ A, #𝒰 ≤ t → (∀ U ∈ 𝒰, U ≠ ⊤) → ∀ U ∈ 𝒰, a ∉ U := by
      by_cases h𝒰 : #𝒰 ≤ t ∧ ∀ U ∈ 𝒰, U ≠ ⊤
      · obtain ⟨a, haA, ha⟩ := not_subset.mp (hA 𝒰 h𝒰.1 h𝒰.2)
        exact ⟨a, haA, fun _ _ U hU haU ↦ ha (mem_biUnion hU haU)⟩
      · exact ⟨a₀, ha₀, fun ht hp ↦ absurd ⟨ht, hp⟩ h𝒰⟩
    choose w hwA hw using hw
    -- the finitely many families of spans of subsets of `F`
    set 𝒞 : Set (Finset (Submodule K V)) :=
      {𝒰 | (𝒰 : Set (Submodule K V)) ⊆ (span K ·) '' {S | S ⊆ F}}
    have h𝒞 : 𝒞.Finite :=
      ((hF.finite_subsets.image _).finite_subsets).preimage Finset.coe_injective.injOn
    refine ⟨F ∪ w '' 𝒞, union_subset hFA (image_subset_iff.mpr fun 𝒰 _ ↦ hwA 𝒰),
      hF.union (h𝒞.image w), fun 𝒲 ht hp hcover ↦ ?_⟩
    -- restrict `𝒲` to `F`, and find the member of `𝒲` containing the new point
    set 𝒰 := 𝒲.image fun W : Submodule K V ↦ span K ((W : Set V) ∩ F)
    have h𝒰 : 𝒰 ∈ 𝒞 := by
      intro U hU
      obtain ⟨W, -, rfl⟩ := Finset.mem_image.mp hU
      exact ⟨_, inter_subset_right, rfl⟩
    obtain ⟨W₀, hW₀, haW₀⟩ := mem_iUnion₂.mp (hcover (Or.inr ⟨𝒰, h𝒰, rfl⟩))
    have hnot : w 𝒰 ∉ span K ((W₀ : Set V) ∩ F) := by
      refine hw 𝒰 (card_image_le.trans ht) (fun U hU ↦ ?_) _ (Finset.mem_image_of_mem _ hW₀)
      obtain ⟨W, hW, rfl⟩ := Finset.mem_image.mp hU
      exact ne_top_of_le_ne_top (hp W hW) (span_le.mpr inter_subset_left)
    -- the measure strictly increases at `W₀`
    have hmono (W : Submodule K V) :
        span K ((W : Set V) ∩ F) ≤ span K ((W : Set V) ∩ (F ∪ w '' 𝒞)) :=
      span_mono (inter_subset_inter_right _ subset_union_left)
    have hlt : span K ((W₀ : Set V) ∩ F) < span K ((W₀ : Set V) ∩ (F ∪ w '' 𝒞)) :=
      IsConcreteLE.lt_iff_le_and_exists.mpr
        ⟨hmono W₀, w 𝒰, subset_span ⟨haW₀, Or.inr ⟨𝒰, h𝒰, rfl⟩⟩, hnot⟩
    exact Nat.succ_le_of_lt <| (hk 𝒲 ht hp (subset_union_left.trans hcover)).trans_lt <|
      Finset.sum_lt_sum (fun W _ ↦ finrank_mono (hmono W))
        ⟨W₀, hW₀, finrank_lt_finrank_of_lt hlt⟩

/-- **Finite witnesses for non-covering.** In a finite-dimensional vector space, if no family of
at most `t` proper subspaces covers `A`, then some finite subset of `A` is not covered by any family
of at most `t` proper subspaces either. -/
theorem exists_finite_subset_forall_not_subset_biUnion
    (hA : ∀ 𝒲 : Finset (Submodule K V), #𝒲 ≤ t → (∀ W ∈ 𝒲, W ≠ ⊤) →
      ¬A ⊆ ⋃ W ∈ 𝒲, (W : Set V)) :
    ∃ F ⊆ A, F.Finite ∧ ∀ 𝒲 : Finset (Submodule K V), #𝒲 ≤ t → (∀ W ∈ 𝒲, W ≠ ⊤) →
      ¬F ⊆ ⋃ W ∈ 𝒲, (W : Set V) := by
  obtain ⟨F, hFA, hF, hk⟩ :=
    exists_finite_subset_le_sum_finrank_span_inter hA (t * finrank K V + 1)
  refine ⟨F, hFA, hF, fun 𝒲 ht hp hcover ↦ ?_⟩
  have hle : ∑ W ∈ 𝒲, finrank K (span K ((W : Set V) ∩ F)) ≤ t * finrank K V :=
    calc ∑ W ∈ 𝒲, finrank K (span K ((W : Set V) ∩ F))
        ≤ ∑ _W ∈ 𝒲, finrank K V := Finset.sum_le_sum fun W _ ↦ finrank_le _
      _ = #𝒲 * finrank K V := by rw [sum_const, smul_eq_mul]
      _ ≤ t * finrank K V := Nat.mul_le_mul_right _ ht
  have := hk 𝒲 ht hp hcover
  omega

/-- **Covers by boundedly many proper subspaces have finite character.** In a finite-dimensional
vector space, `A` is contained in the union of at most `t` proper subspaces if and only if every
finite subset of `A` is. -/
theorem exists_subset_biUnion_iff_forall_finite :
    (∃ 𝒲 : Finset (Submodule K V), #𝒲 ≤ t ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧ A ⊆ ⋃ W ∈ 𝒲, (W : Set V)) ↔
      ∀ F ⊆ A, F.Finite → ∃ 𝒲 : Finset (Submodule K V),
        #𝒲 ≤ t ∧ (∀ W ∈ 𝒲, W ≠ ⊤) ∧ F ⊆ ⋃ W ∈ 𝒲, (W : Set V) := by
  refine ⟨fun ⟨𝒲, ht, hp, hA⟩ F hFA _ ↦ ⟨𝒲, ht, hp, hFA.trans hA⟩, fun h ↦ ?_⟩
  by_contra hA
  obtain ⟨F, hFA, hF, hno⟩ := exists_finite_subset_forall_not_subset_biUnion
    fun 𝒲 ht hp hcover ↦ hA ⟨𝒲, ht, hp, hcover⟩
  obtain ⟨𝒲, ht, hp, hcover⟩ := h F hFA hF
  exact hno 𝒲 ht hp hcover

end Submodule
