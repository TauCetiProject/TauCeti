/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Pi

/-!
# Hamming support, and Hamming data under coordinate decompositions and reindexing

This file builds on `hammingNorm`, `hammingDist`, and `hammingDist_eq_hammingNorm` from
`Mathlib.InformationTheory.Hamming`.

The Hamming support of a word `x : ι → A` is `Function.support x`, the set of its nonzero
coordinates, and its Hamming weight is the number of elements of that support. The first part of
this file relates `Function.support`, its finset version, `hammingNorm` and `hammingDist`: the
distance from `x` to `y` is the weight of `y - x`, and the weight of a sum is governed by

```text
wt(x + y) + #(supp x ∩ supp y) + #(supp x \ supp (x + y)) = wt x + wt y,
```

where the last set consists of the coordinates at which `y` cancels `x`. It follows that weight is
subadditive and is additive on words with disjoint supports. Scaling coordinatewise by `c`
intersects the support with `supp c`.

The file also records that Hamming weight and distance on a function whose domain is a disjoint
union split as sums over the two coordinate types. Weight also splits over a retained coordinate
set and its complement. These identities let constructions assembled from independent coordinate
blocks reduce their Hamming data to the data of the blocks.

It also proves that Hamming distance and Hamming weight are invariant under relabelling a finite
coordinate type along an equivalence, and evaluates a product over the coordinates of a word which
only depends on which coordinates vanish; this is how weight monomials `X^(n - wt x) Y^(wt x)`
factor over the coordinates.
-/

public section

namespace TauCeti

/-! ### Hamming support -/

section Support

open Function

variable {ι A : Type*}

section Zero

variable [Fintype ι] [Zero A] [DecidableEq A]

/-- The Hamming weight of a word is the number of elements of its support. -/
theorem hammingNorm_eq_ncard_support (x : ι → A) : hammingNorm x = (support x).ncard := by
  rw [hammingNorm, ← Set.ncard_coe_finset, Finset.coe_filter_univ]
  rfl

/-- The Hamming weight of a word is the cardinality of its support, viewed as a finset. -/
theorem hammingNorm_eq_card_toFinset_support (x : ι → A) [Fintype (support x)] :
    hammingNorm x = (support x).toFinset.card := by
  rw [hammingNorm_eq_ncard_support, Set.ncard_eq_toFinset_card']

/-- A word whose support is contained in the support of another word has at most its weight. -/
theorem hammingNorm_le_hammingNorm_of_support_subset {B : Type*} [Zero B] [DecidableEq B]
    {x : ι → A} {y : ι → B} (h : support x ⊆ support y) : hammingNorm x ≤ hammingNorm y := by
  simpa only [hammingNorm_eq_ncard_support] using Set.ncard_le_ncard h

/-- Two words with the same support have the same Hamming weight. -/
theorem hammingNorm_eq_hammingNorm_of_support_eq {B : Type*} [Zero B] [DecidableEq B]
    {x : ι → A} {y : ι → B} (h : support x = support y) : hammingNorm x = hammingNorm y := by
  simp only [hammingNorm_eq_ncard_support, h]

end Zero

/-- The Hamming distance between two words is the number of coordinates at which they differ. -/
theorem hammingDist_eq_ncard_setOf_ne {β : ι → Type*} [Fintype ι] [∀ i, DecidableEq (β i)]
    (x y : ∀ i, β i) : hammingDist x y = {i | x i ≠ y i}.ncard := by
  rw [hammingDist, ← Set.ncard_coe_finset, Finset.coe_filter_univ]

/-- Negation preserves Hamming weight. -/
@[simp]
theorem hammingNorm_neg {β : ι → Type*} [Fintype ι] [∀ i, SubtractionMonoid (β i)]
    [∀ i, DecidableEq (β i)] (x : ∀ i, β i) : hammingNorm (-x) = hammingNorm x :=
  hammingNorm_comp (fun _ ↦ Neg.neg) (fun _ ↦ neg_injective) (fun _ ↦ neg_zero)

section AddGroup

variable {β : ι → Type*} [Fintype ι] [∀ i, AddGroup (β i)] [∀ i, DecidableEq (β i)]

/-- The Hamming distance from `x` to `y` is the Hamming weight of `x - y`. -/
theorem hammingDist_eq_hammingNorm_sub (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (x - y) := by
  simp_rw [hammingDist, hammingNorm, Pi.sub_apply, ne_eq, sub_eq_zero]

/-- The Hamming distance from `x` to `y` is the Hamming weight of `y - x`. -/
theorem hammingDist_eq_hammingNorm_sub' (x y : ∀ i, β i) :
    hammingDist x y = hammingNorm (y - x) := by
  rw [hammingDist_comm, hammingDist_eq_hammingNorm_sub]

end AddGroup

/-- The Hamming distance from `x` to `y` is the number of elements of the support of `y - x`. -/
theorem hammingDist_eq_ncard_support_sub [Fintype ι] [AddGroup A] [DecidableEq A]
    (x y : ι → A) : hammingDist x y = (support (y - x)).ncard := by
  rw [hammingDist_eq_hammingNorm_sub', hammingNorm_eq_ncard_support]

section AddZeroClass

variable [Fintype ι] [AddZeroClass A] [DecidableEq A]

/-- The **weight of a sum**. Coordinates in the support of both words are counted twice on the
right, and the coordinates at which `y` cancels `x` are lost from the support of `x + y`. -/
theorem hammingNorm_add_add_ncard_inter_add_ncard_sdiff (x y : ι → A) :
    hammingNorm (x + y) + (support x ∩ support y).ncard + (support x \ support (x + y)).ncard =
      hammingNorm x + hammingNorm y := by
  -- Every coordinate in the support of `x` or `y` either survives in `x + y` or is a coordinate
  -- at which `y` cancels `x`, and these two cases are disjoint.
  have hunion : support (x + y) ∪ (support x \ support (x + y)) = support x ∪ support y := by
    ext i
    by_cases hx : x i = 0 <;> simp [hx]
  have hdisj := Set.ncard_union_eq (Set.disjoint_sdiff_right (s := support (x + y))
    (t := support x))
  rw [hunion] at hdisj
  have hinter := Set.ncard_union_add_ncard_inter (support x) (support y)
  simp only [hammingNorm_eq_ncard_support]
  omega

/-- Hamming weight is subadditive. -/
theorem hammingNorm_add_le (x y : ι → A) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  have := hammingNorm_add_add_ncard_inter_add_ncard_sdiff x y
  omega

/-- Words with disjoint supports have additive Hamming weight. -/
theorem hammingNorm_add_of_disjoint {x y : ι → A} (h : Disjoint (support x) (support y)) :
    hammingNorm (x + y) = hammingNorm x + hammingNorm y := by
  have hdiff : support x \ support (x + y) = ∅ := by
    refine Set.sdiff_eq_empty.mpr fun i hi ↦ ?_
    have hy : y i = 0 := Function.notMem_support.mp (Set.disjoint_left.mp h hi)
    simpa [hy] using hi
  have := hammingNorm_add_add_ncard_inter_add_ncard_sdiff x y
  rw [h.inter_eq, hdiff, Set.ncard_empty] at this
  omega

end AddZeroClass

/-- The weight of a coordinatewise scaling `c • x` is the number of coordinates at which both
`c` and `x` are nonzero. -/
theorem hammingNorm_smul_eq_ncard_inter [Fintype ι] {R : Type*} [Semiring R] [IsCancelMulZero R]
    [AddCommMonoid A] [Module R A] [Module.IsTorsionFree R A] [DecidableEq A] (c : ι → R)
    (x : ι → A) : hammingNorm (c • x) = (support c ∩ support x).ncard := by
  rw [hammingNorm_eq_ncard_support]
  congr 1
  ext i
  simp

end Support

variable {ι κ : Type*} {β : ι ⊕ κ → Type*}

/-- A constant word has full weight unless its constant value is zero. -/
@[simp]
theorem hammingNorm_const {A : Type*} [Fintype ι] [Zero A] [DecidableEq A] (a : A) :
    hammingNorm (Function.const ι a) = if a = 0 then 0 else Fintype.card ι := by
  by_cases ha : a = 0 <;> simp [hammingNorm, Function.const, ha]

/-- The Hamming distance between two pairs of words combined on a disjoint union is the sum of
the distances between the respective words. -/
@[simp]
theorem hammingDist_sumRec [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    (x x' : ∀ i, β (.inl i)) (y y' : ∀ j, β (.inr j)) :
    hammingDist (Sum.rec (motive := β) x y) (Sum.rec (motive := β) x' y') =
      hammingDist x x' + hammingDist y y' := by
  simp only [hammingDist, Finset.card_filter]
  rw [Fintype.sum_sum_type]

/-- The Hamming weight of two words combined on a disjoint union is the sum of their weights. -/
@[simp]
theorem hammingNorm_sumRec [Fintype ι] [Fintype κ] [∀ z, DecidableEq (β z)]
    [∀ z, Zero (β z)] (x : ∀ i, β (.inl i)) (y : ∀ j, β (.inr j)) :
    hammingNorm (Sum.rec (motive := β) x y) = hammingNorm x + hammingNorm y := by
  have sumRec_zero :
      Sum.rec (motive := β) (0 : ∀ i, β (.inl i)) (0 : ∀ j, β (.inr j)) = 0 := by
    funext z
    cases z <;> rfl
  simpa only [← hammingDist_zero_right, sumRec_zero] using
    hammingDist_sumRec x (0 : ∀ i, β (.inl i)) y (0 : ∀ j, β (.inr j))

/-- The Hamming distance between two pairs of words over a common alphabet, combined on a disjoint
union, is the sum of the distances between the respective words. -/
@[simp]
theorem hammingDist_sumElim {A : Type*} [Fintype ι] [Fintype κ] [DecidableEq A]
    (x x' : ι → A) (y y' : κ → A) :
    hammingDist (Sum.elim x y) (Sum.elim x' y') = hammingDist x x' + hammingDist y y' :=
  hammingDist_sumRec (β := fun _ ↦ A) x x' y y'

/-- The Hamming weight of two words over a common alphabet, combined on a disjoint union, is the
sum of their weights. -/
@[simp]
theorem hammingNorm_sumElim {A : Type*} [Fintype ι] [Fintype κ] [DecidableEq A] [Zero A]
    (x : ι → A) (y : κ → A) :
    hammingNorm (Sum.elim x y) = hammingNorm x + hammingNorm y :=
  hammingNorm_sumRec (β := fun _ ↦ A) x y

/-- Hamming weight splits over a retained coordinate set and its complement. -/
theorem hammingNorm_eq_domRestrict_add_domRestrict_compl {ι : Type*} {A : ι → Type*}
    [Fintype ι] [∀ i, Zero (A i)] [∀ i, DecidableEq (A i)]
    (s : Set ι) [DecidablePred (· ∈ s)] (x : ∀ i, A i) :
    hammingNorm x = hammingNorm (s.domRestrict x) + hammingNorm (sᶜ.domRestrict x) := by
  simp only [hammingNorm, Finset.card_filter]
  exact (Fintype.sum_subtype_add_sum_subtype (· ∈ s) _).symm

/-- A product over the coordinates which takes the value `a` at the zero coordinates of a word
and `b` elsewhere is `a ^ (n - wt x) * b ^ (wt x)`, where `n` is the length and `wt` is the
Hamming weight. -/
@[simp] theorem prod_ite_eq_zero_eq_pow_mul_pow_hammingNorm {M : Type*} {β : ι → Type*} [Fintype ι]
    [∀ i, Zero (β i)] [∀ i, DecidableEq (β i)] [CommMonoid M] (x : ∀ i, β i) (a b : M) :
    ∏ i, (if x i = 0 then a else b) = a ^ (Fintype.card ι - hammingNorm x) * b ^ hammingNorm x := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i ↦ x i = 0)
  rw [Finset.card_univ] at h
  rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, hammingNorm, ← h, Nat.add_sub_cancel]

end TauCeti

namespace Equiv

variable {α ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq α]

/-- Relabelling coordinates along an equivalence preserves the Hamming distance. -/
theorem hammingDist_comp (e : κ ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  simp only [hammingDist, Function.comp_apply]
  exact Finset.card_equiv e (by simp)

/-- Relabelling coordinates along an equivalence preserves the Hamming weight. -/
theorem hammingNorm_comp [Zero α] (e : κ ≃ ι) (x : ι → α) :
    hammingNorm (x ∘ e) = hammingNorm x := by
  simp only [hammingNorm, Function.comp_apply]
  exact Finset.card_equiv e (by simp)

section Relabelling

variable {R : Type*} [Semiring R]

/-- Relabelling a word along an equivalence of finite coordinate types preserves its Hamming
weight, when the relabelling is expressed as a linear map between function spaces. -/
@[simp]
theorem hammingNorm_funLeft [DecidableEq R] (e : κ ≃ ι) (x : ι → R) :
    hammingNorm (LinearMap.funLeft R R e x) = hammingNorm x :=
  Equiv.hammingNorm_comp e x

/-- Relabelling two words along an equivalence of finite coordinate types preserves their Hamming
distance, when the relabelling is expressed as a linear map between function spaces. -/
@[simp]
theorem hammingDist_funLeft [DecidableEq R] (e : κ ≃ ι) (x y : ι → R) :
    hammingDist (LinearMap.funLeft R R e x) (LinearMap.funLeft R R e y) = hammingDist x y :=
  Equiv.hammingDist_comp e x y

end Relabelling

end Equiv
