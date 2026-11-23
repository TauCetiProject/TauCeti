/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Wentao Li
-/
module

public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.Data.Set.Card
public import Mathlib.InformationTheory.Hamming
public import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.Notation.Indicator

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
additive on words with disjoint supports; weight is also subadditive. Scaling coordinatewise by `c`
intersects the support with `supp c`. The weight of an integer vector, and of its image in any
additive group with one (such as its reduction modulo `n`), is at most the vector's sum of squares.

The file also records that Hamming weight and distance on a function whose domain is a disjoint
union split as sums over the two coordinate types. Weight also splits over a retained coordinate
set and its complement. These identities let constructions assembled from independent coordinate
blocks reduce their Hamming data to the data of the blocks.

It also proves that Hamming distance and Hamming weight are invariant under relabelling a finite
coordinate type along an equivalence, and evaluates a product over the coordinates of a word which
only depends on which coordinates vanish; this is how weight monomials `X^(n - wt x) Y^(wt x)`
factor over the coordinates. For set indicators, weight is cardinality and distance is the
cardinality of the symmetric difference.

Finally, for a binary word `c : ι → Bool` and any `x` in a commutative semiring,
`∑ y, x ^ hammingDist y c = (1 + x) ^ card ι` (`TauCeti.sum_pow_hammingDist_eq`), and for every
radius `D` and word `a` a greedy code through `a` has distinct words at distance more than `D` and
meets every closed ball of radius `D`
(`TauCeti.exists_finset_pairwise_lt_hammingDist_forall_exists`). Both are adapted from the
lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>), file
`CKSD/Nonparametric/LowerBounds/Testing.lean` (`CKSD.sum_pow_hammingDist_eq`,
`CKSD.exists_hamming_packing`).
-/

public section

namespace Finset

open scoped symmDiff

variable {ι A : Type*} [Fintype ι] [Zero A] [One A] [NeZero (1 : A)] [DecidableEq A]

/-- The Hamming weight of the indicator of a finite subset is its cardinality. -/
@[simp]
theorem hammingNorm_indicator_one (s : Finset ι) :
    hammingNorm ((s : Set ι).indicator (1 : ι → A)) = s.card := by
  classical
  rw [hammingNorm]
  congr 1
  ext i
  by_cases hi : i ∈ s <;>
    simp [Set.indicator_apply, hi, NeZero.ne]

/-- Two indicators differ at exactly the elements of the symmetric difference of their sets. -/
@[simp]
theorem hammingDist_indicator_one [DecidableEq ι] (s t : Finset ι) :
    hammingDist ((s : Set ι).indicator (1 : ι → A)) ((t : Set ι).indicator 1) = (s ∆ t).card := by
  classical
  rw [hammingDist]
  congr 1
  ext i
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;>
    simp [Set.indicator_apply, Finset.mem_symmDiff, hs, ht, NeZero.ne,
      NeZero.ne' (1 : A)]

end Finset

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

/-- Hamming weight is subadditive. -/
theorem hammingNorm_add_le {β : ι → Type*} [Fintype ι] [∀ i, AddZeroClass (β i)]
    [∀ i, DecidableEq (β i)] (x y : ∀ i, β i) :
    hammingNorm (x + y) ≤ hammingNorm x + hammingNorm y := by
  classical
  refine (Finset.card_le_card fun i ↦ ?_).trans (Finset.card_union_le _ _)
  simp only [Finset.mem_union, Finset.mem_filter_univ, Pi.add_apply]
  grind [add_zero]

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

/-- The Hamming weight of an integer vector is bounded by its sum of squares. -/
theorem hammingNorm_le_sum_sq [Fintype ι] (z : ι → ℤ) : (hammingNorm z : ℤ) ≤ ∑ i, z i ^ 2 := by
  have hsum : ∑ i, (if z i ≠ 0 then (1 : ℤ) else 0) ≤ ∑ i, z i ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs with hz
    · have := sq_pos_of_ne_zero hz
      omega
    · exact sq_nonneg _
  simpa only [Finset.sum_boole, hammingNorm] using hsum

/-- The Hamming weight of the image of an integer vector in any additive group with one, such as
its reduction modulo `n`, is bounded by its sum of squares. -/
theorem hammingNorm_intCast_le_sum_sq [Fintype ι] (R : Type*) [AddGroupWithOne R]
    [DecidableEq R] (z : ι → ℤ) : (hammingNorm (fun i ↦ (z i : R)) : ℤ) ≤ ∑ i, z i ^ 2 :=
  -- Casting coordinatewise sends `0` to `0`, so it cannot increase the Hamming weight.
  (Nat.cast_le.mpr <| hammingNorm_comp_le_hammingNorm (fun _ ↦ Int.cast) fun _ ↦
    Int.cast_zero).trans (hammingNorm_le_sum_sq z)

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
  simp only [hammingNorm, Finset.card_filter]
  rw [Fintype.sum_sum_type]

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
theorem hammingNorm_eq_domRestrict_add_domRestrict_compl {A : ι → Type*} [Fintype ι]
    [∀ i, Zero (A i)] [∀ i, DecidableEq (A i)]
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

/-! ### Binary words and greedy codes -/

section Codes

open Finset

/-- The exponential moment of the Hamming distance to a fixed binary word:
`∑ y, x ^ hammingDist y c = (1 + x) ^ n` over the words `y : ι → Bool`, with `n = card ι`. -/
theorem sum_pow_hammingDist_eq {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (c : ι → Bool) (x : R) : ∑ y : ι → Bool, x ^ hammingDist y c = (1 + x) ^ Fintype.card ι := by
  have h (y : ι → Bool) : x ^ hammingDist y c = ∏ i, if y i ≠ c i then x else 1 := by
    rw [prod_ite, prod_const, prod_const_one, mul_one, hammingDist]
  have hb (i : ι) : ∑ b : Bool, (if b ≠ c i then x else 1) = 1 + x := by
    cases c i <;> simp [add_comm]
  calc ∑ y : ι → Bool, x ^ hammingDist y c
      = ∏ i, ∑ b : Bool, (if b ≠ c i then x else 1) := by
        simp only [h]
        exact (Fintype.prod_sum fun i (b : Bool) ↦ if b ≠ c i then x else 1).symm
    _ = (1 + x) ^ Fintype.card ι := by simp only [hb, prod_const, card_univ]

/-- A greedy code: for every radius `D` and word `a`, some finite code containing `a` has distinct
words at distance more than `D` and meets the closed ball of radius `D` about every word. -/
theorem exists_finset_pairwise_lt_hammingDist_forall_exists {ι : Type*} {β : ι → Type*}
    [Fintype ι] [∀ i, Finite (β i)] [∀ i, DecidableEq (β i)] (D : ℕ) (a : ∀ i, β i) :
    ∃ C : Finset (∀ i, β i), a ∈ C ∧
      (C : Set (∀ i, β i)).Pairwise (fun x y ↦ D < hammingDist x y) ∧
      ∀ y, ∃ x ∈ C, hammingDist y x ≤ D := by
  classical
  have (i : ι) : Fintype (β i) := Fintype.ofFinite _
  let valid : Finset (∀ i, β i) → Prop := fun C ↦
    a ∈ C ∧ (C : Set (∀ i, β i)).Pairwise fun x y ↦ D < hammingDist x y
  obtain ⟨C, hC, hmax⟩ := exists_max_image (univ.filter valid) card
    ⟨{a}, mem_filter.mpr ⟨mem_univ _, mem_singleton_self a, by simp⟩⟩
  obtain ⟨ha, hsep⟩ := (mem_filter.mp hC).2
  refine ⟨C, ha, hsep, fun y ↦ ?_⟩
  by_contra! hy
  have hyC : y ∉ C := fun h ↦ by simpa using hy y h
  have hval : valid (insert y C) := by
    refine ⟨mem_insert_of_mem ha, ?_⟩
    rw [coe_insert, Set.pairwise_insert]
    exact ⟨hsep, fun x hx _ ↦ ⟨hy x hx, hammingDist_comm y x ▸ hy x hx⟩⟩
  have := hmax _ (mem_filter.mpr ⟨mem_univ _, hval⟩)
  rw [card_insert_of_notMem hyC] at this
  omega

end Codes

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

variable {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]

/-- Relabelling a word along an equivalence of finite coordinate types preserves its Hamming
weight, when the relabelling is expressed as a linear map between function spaces. -/
@[simp]
theorem hammingNorm_funLeft [DecidableEq M] (e : κ ≃ ι) (x : ι → M) :
    hammingNorm (LinearMap.funLeft R M e x) = hammingNorm x :=
  Equiv.hammingNorm_comp e x

/-- Relabelling two words along an equivalence of finite coordinate types preserves their Hamming
distance, when the relabelling is expressed as a linear map between function spaces. -/
@[simp]
theorem hammingDist_funLeft [DecidableEq M] (e : κ ≃ ι) (x y : ι → M) :
    hammingDist (LinearMap.funLeft R M e x) (LinearMap.funLeft R M e y) = hammingDist x y :=
  Equiv.hammingDist_comp e x y

end Relabelling

end Equiv
