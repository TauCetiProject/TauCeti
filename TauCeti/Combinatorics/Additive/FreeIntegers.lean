/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finsupp.Lex
public import Mathlib.Data.Finsupp.Weight
public import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith

/-!
# Free families of integers

A family `e : ι → M` *has no small relations up to `B`* (`TauCeti.HasNoSmallRelations B e`) if
two vectors `α, β : ι →₀ ℕ` with `degree α = degree β ≤ B` and `∑ α i • e i = ∑ β i • e i` are
equal. For `ι = Fin N` and `B = (N + 1) ^ 2` these are the free integers `e 1, …, e N`.

For a decreasing family `y` of nonnegative integers with `B * y j < y i` whenever `i < j`, the
weight `∑ α i * y i` is strictly increasing in `α` for the lexicographic order on vectors of a
fixed degree `d ≤ B`: if `α` and `β` first differ at `j`, with `α j < β j`, the gain `y j` at `j`
exceeds the loss `∑_{i > j} α i * y i`, which is at most `d` times `max_{i > j} y i`. So such a
family has no small relations up to `B`. Reversing the order gives the same for increasing
families with `B * y i < y j` whenever `i < j`.

## Main definitions

* `TauCeti.HasNoSmallRelations B e`: vectors of the same degree at most `B` with the same
  weight with respect to `e` are equal.

## Main results

* `Finsupp.weight_comp`, `Finsupp.weight_add_const`: the weight with respect to `f ∘ e` and to
  `e + c`.
* `TauCeti.HasNoSmallRelations.mono`: the predicate passes to smaller bounds.
* `TauCeti.hasNoSmallRelations_comp_iff`: it is invariant under composition with an injective
  additive homomorphism; `TauCeti.hasNoSmallRelations_neg_iff` is the case of negation.
* `TauCeti.hasNoSmallRelations_add_const_iff`: it is invariant under translation.
* `TauCeti.weight_lt_weight_of_toLex_lt`: for `y` as above and `α, β` of the same degree at most
  `B` with `toLex α < toLex β`, the weight of `α` is less than that of `β`.
* `TauCeti.hasNoSmallRelations_of_rapid_decrease`: rapidly decreasing nonnegative integers have
  no small relations.
* `TauCeti.hasNoSmallRelations_of_lacunary`: lacunary nonnegative integers have no small
  relations.

## Provenance

The predicate is `New.HasNoSmallRelations` of the folder `grh` of
https://github.com/lsernau/grh-lean at commit 72fead102f663d5c7a407964a13dc0cf9d977207, file
`Lib/General/LinearAlgebra/MatrixPolynomials`, with the bound `(n + 1) ^ 2` made a parameter. The
lexicographic comparison follows `New.hasNoSmallRelations_of_lacunary` of
`Lib/GaloisRep/WeightCongruence` there, under the weaker gap condition `B * y j < y i`.
-/

@[expose] public section

open Finset

namespace TauCeti

variable {ι M M' : Type*}

/-- The family `e` has no small relations up to `B`: two vectors `α, β : ι →₀ ℕ` with
`degree α = degree β ≤ B` and `weight e α = weight e β` are equal. -/
def HasNoSmallRelations [AddCommMonoid M] (B : ℕ) (e : ι → M) : Prop :=
  ∀ d ≤ B, {α : ι →₀ ℕ | α.degree = d}.InjOn (Finsupp.weight e)

/-- Having no small relations passes to smaller bounds. -/
theorem HasNoSmallRelations.mono [AddCommMonoid M] {B B' : ℕ} {e : ι → M}
    (he : HasNoSmallRelations B e) (h : B' ≤ B) : HasNoSmallRelations B' e :=
  fun d hd ↦ he d (hd.trans h)

/-- Composing with an additive homomorphism commutes with taking weights. -/
theorem _root_.Finsupp.weight_comp [AddCommMonoid M] [AddCommMonoid M'] (f : M →+ M') (e : ι → M)
    (α : ι →₀ ℕ) : Finsupp.weight (f ∘ e) α = f (Finsupp.weight e α) := by
  simp [Finsupp.weight_apply, map_finsuppSum]

/-- Having no small relations is invariant under composition with an injective additive
homomorphism. -/
theorem hasNoSmallRelations_comp_iff [AddCommMonoid M] [AddCommMonoid M'] {B : ℕ}
    {f : M →+ M'} (hf : Function.Injective f) {e : ι → M} :
    HasNoSmallRelations B (f ∘ e) ↔ HasNoSmallRelations B e := by
  refine forall₂_congr fun d _ ↦ ?_
  simp only [Set.InjOn, Finsupp.weight_comp, hf.eq_iff]

/-- Having no small relations is invariant under negation. -/
theorem hasNoSmallRelations_neg_iff [AddCommGroup M] {B : ℕ} {e : ι → M} :
    HasNoSmallRelations B (-e) ↔ HasNoSmallRelations B e :=
  hasNoSmallRelations_comp_iff (f := (AddEquiv.neg M).toAddMonoidHom) neg_injective

/-- Translating every entry by `c` adds `degree α • c` to the weight. -/
theorem _root_.Finsupp.weight_add_const [AddCommMonoid M] (e : ι → M) (c : M) (α : ι →₀ ℕ) :
    Finsupp.weight (fun i ↦ e i + c) α = Finsupp.weight e α + α.degree • c := by
  simp [Finsupp.weight_apply, Finsupp.degree_apply, Finsupp.sum, smul_add, sum_add_distrib,
    ← sum_nsmul_assoc]

/-- Having no small relations is invariant under translation. -/
theorem hasNoSmallRelations_add_const_iff [AddCancelCommMonoid M] {B : ℕ} {e : ι → M} (c : M) :
    HasNoSmallRelations B (fun i ↦ e i + c) ↔ HasNoSmallRelations B e := by
  refine forall₂_congr fun d _ ↦ ?_
  refine forall₂_congr fun α (hα : α.degree = d) ↦ forall₂_congr fun β (hβ : β.degree = d) ↦ ?_
  simp [Finsupp.weight_add_const, hα, hβ]

/-- Let `a, b` be integers, `b` nonnegative, with equal sums over a finite set `s`, agreeing
below `j ∈ s`, with `a j < b j`. Then the sum of the `a i` with `j < i` is at least `1`. -/
private theorem one_le_sum_ite_lt [LinearOrder ι] {s : Finset ι} {j : ι} (hjs : j ∈ s)
    {a b : ι → ℤ} (hb : ∀ i, 0 ≤ b i) (h_eq : ∀ i < j, a i = b i) (h_j : a j < b j)
    (h_sum : ∑ i ∈ s, a i = ∑ i ∈ s, b i) : 1 ≤ ∑ i ∈ s, if j < i then a i else 0 := by
  have h : ∑ i ∈ s, ((if i = j then 1 else 0) - if j < i then a i else 0) ≤
      ∑ i ∈ s, (b i - a i) := by
    refine sum_le_sum fun i _ ↦ ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h.ne, h.not_gt, h_eq i h]
    · simp only [lt_irrefl, ite_true, ite_false]
      lia
    · simp only [h, h.ne', ite_true, ite_false]
      linarith [hb i]
  rw [sum_sub_distrib, sum_sub_distrib, h_sum, sub_self] at h
  simp only [sum_ite_eq', hjs, ite_true] at h
  lia

/-- Let `y` be nonnegative integers with `B * y j < y i` whenever `i < j`, and let `a, b` be
nonnegative integers on a finite set `s` with equal sums at most `B`, agreeing below `j ∈ s`,
with `a j < b j`. Then `∑ a i * y i < ∑ b i * y i`. -/
private theorem sum_mul_lt_sum_mul [LinearOrder ι] {B : ℕ} {y : ι → ℤ} (hy : ∀ i, 0 ≤ y i)
    (h_gap : ∀ i j, i < j → B * y j < y i) {s : Finset ι} {j : ι} (hjs : j ∈ s)
    {a b : ι → ℤ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (h_eq : ∀ i < j, a i = b i)
    (h_j : a j < b j) (h_sum : ∑ i ∈ s, a i = ∑ i ∈ s, b i) (hB : ∑ i ∈ s, a i ≤ B) :
    ∑ i ∈ s, a i * y i < ∑ i ∈ s, b i * y i := by
  -- `F i` is `a i` for `i > j` and `0` otherwise.
  set F : ι → ℤ := fun i ↦ if j < i then a i else 0
  have h_one : 1 ≤ ∑ i ∈ s, F i := one_le_sum_ite_lt hjs hb h_eq h_j h_sum
  -- The difference of the sums is at least `y j - ∑ F i * y i`.
  have h_diff : y j - ∑ i ∈ s, F i * y i ≤ ∑ i ∈ s, (b i - a i) * y i := by
    rw [show y j = ∑ i ∈ s, (if i = j then y j else 0) by simp [hjs], ← sum_sub_distrib]
    refine sum_le_sum fun i _ ↦ ?_
    rcases lt_trichotomy i j with h | rfl | h
    · simp [F, h.ne, h.not_gt, h_eq i h]
    · simp only [F, lt_irrefl, ite_true, ite_false]
      nlinarith [hy i]
    · simp only [F, h, h.ne', ite_true, ite_false]
      nlinarith [hy i, hb i]
  have h_le : ∑ i ∈ s, F i ≤ B :=
    (sum_le_sum fun i _ ↦ by by_cases h : j < i <;> simp [F, h, ha i]).trans hB
  -- Each term `F i * y i` is at most `F i * (y j - 1) / B`.
  have h_term : (B : ℤ) * ∑ i ∈ s, F i * y i ≤ (∑ i ∈ s, F i) * (y j - 1) := by
    rw [mul_sum, sum_mul]
    refine sum_le_sum fun i _ ↦ ?_
    by_cases h : j < i
    · simp only [F, h, ite_true]
      nlinarith [h_gap j i h, ha i]
    · simp [F, h]
  have h_small : ∑ i ∈ s, F i * y i < y j := by
    refine lt_of_mul_lt_mul_left ?_ (show (0 : ℤ) ≤ B by lia)
    nlinarith [mul_le_mul_of_nonneg_right h_le (hy j)]
  simp only [sub_mul, sum_sub_distrib] at h_diff
  linarith

/-- Let `y` be nonnegative integers with `B * y j < y i` whenever `i < j`. If `α, β : ι →₀ ℕ`
have the same degree at most `B` and `toLex α < toLex β`, then the weight of `α` with respect
to `y` is less than that of `β`. -/
theorem weight_lt_weight_of_toLex_lt [LinearOrder ι] {B : ℕ} {y : ι → ℤ} (hy : ∀ i, 0 ≤ y i)
    (h_gap : ∀ i j, i < j → B * y j < y i) {α β : ι →₀ ℕ} (h_deg : α.degree = β.degree)
    (hB : β.degree ≤ B) (h_lt : toLex α < toLex β) :
    Finsupp.weight y α < Finsupp.weight y β := by
  obtain ⟨j, h_eq, h_j⟩ := Finsupp.Lex.lt_iff.1 h_lt
  change ∀ i, i < j → α i = β i at h_eq
  change α j < β j at h_j
  classical
  -- Write all sums over `s = supp α ∪ supp β`.
  set s := α.support ∪ β.support
  have hjs : j ∈ s := mem_union_right _ (Finsupp.mem_support_iff.2 (by lia))
  have h_weight (γ : ι →₀ ℕ) (hγ : γ.support ⊆ s) :
      Finsupp.weight y γ = ∑ i ∈ s, (γ i : ℤ) * y i := by
    rw [Finsupp.weight_apply, Finsupp.sum_of_support_subset _ hγ _ (by simp)]
    simp
  have h_degree (γ : ι →₀ ℕ) (hγ : γ.support ⊆ s) : (γ.degree : ℤ) = ∑ i ∈ s, (γ i : ℤ) := by
    rw [Finsupp.degree_apply, sum_subset hγ (by simp_all)]
    push_cast; rfl
  rw [h_weight α subset_union_left, h_weight β subset_union_right]
  refine sum_mul_lt_sum_mul hy h_gap hjs (fun i ↦ (α i).cast_nonneg)
    (fun i ↦ (β i).cast_nonneg) (fun i hi ↦ by rw [h_eq i hi]) (by exact_mod_cast h_j) ?_ ?_
  · rw [← h_degree α subset_union_left, ← h_degree β subset_union_right, h_deg]
  · rw [← h_degree α subset_union_left]
    exact_mod_cast h_deg ▸ hB

/-- Nonnegative integers `y i` with `B * y j < y i` whenever `i < j` (a rapidly decreasing
family) have no small relations up to `B`. -/
theorem hasNoSmallRelations_of_rapid_decrease [LinearOrder ι] {B : ℕ} {y : ι → ℤ}
    (hy : ∀ i, 0 ≤ y i) (h_gap : ∀ i j, i < j → B * y j < y i) : HasNoSmallRelations B y := by
  intro d hd α (hα : α.degree = d) β (hβ : β.degree = d) h
  by_contra h_ne
  rcases lt_or_gt_of_ne (toLex.injective.ne h_ne) with h_lt | h_lt
  · exact (weight_lt_weight_of_toLex_lt hy h_gap (hα.trans hβ.symm) (hβ ▸ hd) h_lt).ne h
  · exact (weight_lt_weight_of_toLex_lt hy h_gap (hβ.trans hα.symm) (hα ▸ hd) h_lt).ne' h

/-- Nonnegative integers `y i` with `B * y i < y j` whenever `i < j` (a lacunary family) have
no small relations up to `B`. -/
theorem hasNoSmallRelations_of_lacunary [LinearOrder ι] {B : ℕ} {y : ι → ℤ}
    (hy : ∀ i, 0 ≤ y i) (h_gap : ∀ i j, i < j → B * y i < y j) : HasNoSmallRelations B y :=
  hasNoSmallRelations_of_rapid_decrease (ι := ιᵒᵈ) hy fun i j h ↦ h_gap j i h

end TauCeti
