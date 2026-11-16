/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
import Mathlib.Data.List.Chain

/-!
# Reduced words in a free product

An element of the free product `M ∗ N` is the image under `Monoid.Coprod.mk` of a word in the
letters `M ⊕ N`. A word is *reduced* when none of its letters is `1` and consecutive letters lie in
different factors. Every element of `M ∗ N` is the image of a reduced word: merging adjacent letters
of the same factor and deleting letters equal to `1` reduces any word. This is the existence part of
the normal form theorem for free products. It holds for factors that are only `MulOneClass`es:
adjacent letters are merged in the free monoid `FreeMonoid (M ⊕ N)`, which is associative.

## Main results

* `Monoid.Coprod.inl_mul_inl_mul`, `Monoid.Coprod.inr_mul_inr_mul`: adjacent letters of the same
  factor merge.
* `Monoid.Coprod.exists_reduced_list_mk_eq`: every element of `M ∗ N` is the image of a reduced
  word.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial group theory*, Springer, 1977, Chapter IV, §1
  (the normal form theorem for free products).
-/

public section

namespace Monoid.Coprod

variable {M N : Type*} [MulOneClass M] [MulOneClass N]

/-- Two letters of `M` merge: `inl m * (inl m' * x) = inl (m * m') * x`. For `MulOneClass` factors
this is not an instance of `mul_assoc`: Mathlib makes `M ∗ N` a monoid only when `M` and `N` are. -/
theorem inl_mul_inl_mul (m m' : M) (x : M ∗ N) : inl m * (inl m' * x) = inl (m * m') * x := by
  -- Reassociate in the free monoid `FreeMonoid (M ⊕ N)`.
  obtain ⟨w, rfl⟩ := mk_surjective x
  rw [map_mul inl, ← mk_of_inl, ← mk_of_inl (N := N) m']
  simp only [← map_mul, mul_assoc]

/-- Two letters of `N` merge: `inr n * (inr n' * x) = inr (n * n') * x`. For `MulOneClass` factors
this is not an instance of `mul_assoc`: Mathlib makes `M ∗ N` a monoid only when `M` and `N` are. -/
theorem inr_mul_inr_mul (n n' : N) (x : M ∗ N) : inr n * (inr n' * x) = inr (n * n') * x := by
  obtain ⟨w, rfl⟩ := mk_surjective x
  rw [map_mul inr, ← mk_of_inr, ← mk_of_inr (M := M) n']
  simp only [← map_mul, mul_assoc]

/-- Left multiplication by a letter of `M` preserves the images of reduced words. -/
private theorem exists_reduced_list_mk_eq_inl_mul (m : M) {L : List (M ⊕ N)}
    (hc : (L.map Sum.isRight).IsChain (· ≠ ·)) (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) :
    ∃ L' : List (M ⊕ N), (L'.map Sum.isRight).IsChain (· ≠ ·) ∧ Sum.inl 1 ∉ L' ∧
      Sum.inr 1 ∉ L' ∧ mk (FreeMonoid.ofList L') = inl m * mk (FreeMonoid.ofList L) := by
  match L, hc, h₁, h₂ with
  | [], _, _, _ =>
    by_cases hm : m = 1
    · exact ⟨[], by simp [hm]⟩
    · exact ⟨[.inl m], by simp [Ne.symm hm, FreeMonoid.ofList_cons]⟩
  | .inl m' :: L, hc, h₁, h₂ =>
    rw [FreeMonoid.ofList_cons, map_mul mk, mk_of_inl, inl_mul_inl_mul]
    by_cases hm : m * m' = 1
    · exact ⟨L, by simpa using hc.tail, fun h => h₁ (List.mem_cons_of_mem _ h),
        fun h => h₂ (List.mem_cons_of_mem _ h), by simp [hm]⟩
    · exact ⟨.inl (m * m') :: L, by simpa using hc, by simp_all [Ne.symm hm], by simpa using h₂,
        by simp [FreeMonoid.ofList_cons]⟩
  | .inr n :: L, hc, h₁, h₂ =>
    by_cases hm : m = 1
    · exact ⟨_, hc, h₁, h₂, by simp [hm]⟩
    · exact ⟨.inl m :: .inr n :: L, by simpa using hc, by simp_all [Ne.symm hm],
        by simpa using h₂, by simp [FreeMonoid.ofList_cons]⟩

/-- Left multiplication by a letter of `N` preserves the images of reduced words. -/
private theorem exists_reduced_list_mk_eq_inr_mul (n : N) {L : List (M ⊕ N)}
    (hc : (L.map Sum.isRight).IsChain (· ≠ ·)) (h₁ : Sum.inl 1 ∉ L) (h₂ : Sum.inr 1 ∉ L) :
    ∃ L' : List (M ⊕ N), (L'.map Sum.isRight).IsChain (· ≠ ·) ∧ Sum.inl 1 ∉ L' ∧
      Sum.inr 1 ∉ L' ∧ mk (FreeMonoid.ofList L') = inr n * mk (FreeMonoid.ofList L) := by
  match L, hc, h₁, h₂ with
  | [], _, _, _ =>
    by_cases hn : n = 1
    · exact ⟨[], by simp [hn]⟩
    · exact ⟨[.inr n], by simp [Ne.symm hn, FreeMonoid.ofList_cons]⟩
  | .inr n' :: L, hc, h₁, h₂ =>
    rw [FreeMonoid.ofList_cons, map_mul mk, mk_of_inr, inr_mul_inr_mul]
    by_cases hn : n * n' = 1
    · exact ⟨L, by simpa using hc.tail, fun h => h₁ (List.mem_cons_of_mem _ h),
        fun h => h₂ (List.mem_cons_of_mem _ h), by simp [hn]⟩
    · exact ⟨.inr (n * n') :: L, by simpa using hc, by simpa using h₁, by simp_all [Ne.symm hn],
        by simp [FreeMonoid.ofList_cons]⟩
  | .inl m :: L, hc, h₁, h₂ =>
    by_cases hn : n = 1
    · exact ⟨_, hc, h₁, h₂, by simp [hn]⟩
    · exact ⟨.inr n :: .inl m :: L, by simpa using hc, by simpa using h₁,
        by simp_all [Ne.symm hn], by simp [FreeMonoid.ofList_cons]⟩

/-- **Reduced words in a free product.** Every element of `M ∗ N` is the image of a word in the
letters `M ⊕ N` none of whose letters is `1` and whose consecutive letters lie in different
factors. -/
theorem exists_reduced_list_mk_eq (x : M ∗ N) :
    ∃ L : List (M ⊕ N), (L.map Sum.isRight).IsChain (· ≠ ·) ∧ Sum.inl 1 ∉ L ∧ Sum.inr 1 ∉ L ∧
      mk (FreeMonoid.ofList L) = x := by
  induction x using induction_on' with
  | one => exact ⟨[], by simp⟩
  | inl_mul m x ih =>
    obtain ⟨L, hc, h₁, h₂, rfl⟩ := ih
    exact exists_reduced_list_mk_eq_inl_mul m hc h₁ h₂
  | inr_mul n x ih =>
    obtain ⟨L, hc, h₁, h₂, rfl⟩ := ih
    exact exists_reduced_list_mk_eq_inr_mul n hc h₁ h₂

end Monoid.Coprod
