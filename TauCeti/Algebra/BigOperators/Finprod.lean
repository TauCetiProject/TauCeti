/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finprod

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-!
# Regrouping finitely supported products

`Fintype.prod_sum_type` splits a product over `α ⊕ β` into the two partial products, but it needs
both index types to be finite.  This file records the `finprod` analogue, which only needs the two
restricted families to have finite multiplicative support. Regrouping by the fibers of an
arbitrary map is also available, without finiteness assumptions on the fibers, as is cancelling a
finitely supported factor whose product is `1`. Finally, a product over a finset is compared with
the `finprod` of a finitely supported family whose factors off the finset are all at least `1`, or
all at most `1`.

## Main results

* `TauCeti.hasFiniteMulSupport_sum_type`: a family on `α ⊕ β` has finite multiplicative support as
  soon as its two restrictions do.
* `TauCeti.finprod_sum_type`: `∏ᶠ v : α ⊕ β, f v = (∏ᶠ a, f (.inl a)) * ∏ᶠ b, f (.inr b)`.
* `TauCeti.finprod_fiberwise`: regroup a finitely supported product by the fibers of a map.
* `TauCeti.finprod_mul_eq_right_of_finprod_eq_one`: multiplying by a finitely supported family
  with product `1` preserves a product, without any finiteness assumption on the other factor.
* `TauCeti.finprod_comm`: the two iterated products of a family of two variables agree when the
  family has finite multiplicative support jointly in both variables.
* `Finset.prod_le_finprod_of_one_le₀` and `Finset.finprod_le_prod_of_le_one₀`: a product over a
  finset is at most, respectively at least, the `finprod` when the factors off the finset are at
  least, respectively at most, `1`.
-/

public section

namespace TauCeti

open Function Set

variable {α β M : Type*} {f : α ⊕ β → M}

section One

variable [One M]

@[to_additive]
theorem mulSupport_sum_type (f : α ⊕ β → M) :
    mulSupport f =
      Sum.inl '' mulSupport (f ∘ Sum.inl) ∪ Sum.inr '' mulSupport (f ∘ Sum.inr) := by
  ext x
  cases x <;> simp [Sum.inl_injective.mem_set_image, Sum.inr_injective.mem_set_image]

/-- Finite multiplicative support on both summands implies finite multiplicative support on their
disjoint union. -/
@[to_additive]
theorem hasFiniteMulSupport_sum_type (hl : HasFiniteMulSupport (f ∘ Sum.inl))
    (hr : HasFiniteMulSupport (f ∘ Sum.inr)) : HasFiniteMulSupport f := by
  rw [HasFiniteMulSupport, mulSupport_sum_type]
  exact (Set.Finite.image _ hl).union (Set.Finite.image _ hr)

end One

variable [CommMonoid M]

/-- A product over a disjoint union of index types splits as the product of the two partial
products, provided both partial families have finite multiplicative support. -/
@[to_additive]
theorem finprod_sum_type (f : α ⊕ β → M) (hl : HasFiniteMulSupport (f ∘ Sum.inl))
    (hr : HasFiniteMulSupport (f ∘ Sum.inr)) :
    ∏ᶠ v : α ⊕ β, f v = (∏ᶠ a : α, f (Sum.inl a)) * ∏ᶠ b : β, f (Sum.inr b) := by
  have hfl : (range (Sum.inl : α → α ⊕ β) ∩ mulSupport f).Finite :=
    (Set.Finite.image Sum.inl hl).subset (by rintro _ ⟨⟨a, rfl⟩, hx⟩; exact ⟨a, hx, rfl⟩)
  have hfr : (range (Sum.inr : β → α ⊕ β) ∩ mulSupport f).Finite :=
    (Set.Finite.image Sum.inr hr).subset (by rintro _ ⟨⟨b, rfl⟩, hx⟩; exact ⟨b, hx, rfl⟩)
  rw [← finprod_mem_univ, ← range_inl_union_range_inr,
    finprod_mem_union' isCompl_range_inl_range_inr.disjoint hfl hfr,
    finprod_mem_range Sum.inl_injective, finprod_mem_range Sum.inr_injective]

/-- Regroup a finitely supported product by the fibers of an arbitrary map. Neither the index
sets nor the fibers need be finite. -/
@[to_additive /-- Regroup a finitely supported sum by the fibers of an arbitrary map. Neither the
index sets nor the fibers need be finite. -/]
theorem finprod_fiberwise {α β M : Type*} [CommMonoid M] (g : α → β) (f : α → M)
    (hf : (mulSupport f).Finite) :
    (∏ᶠ b, ∏ᶠ a : {a // g a = b}, f a) = ∏ᶠ a, f a := by
  classical
  have hb (b : β) : (∏ᶠ a : {a // g a = b}, f a) =
      ∏ a ∈ hf.toFinset with g a = b, f a := by
    exact (finprod_set_coe_eq_finprod_mem (f := f) {a | g a = b}).trans
      (finprod_mem_eq_prod_filter f {a | g a = b} hf)
  calc
    _ = ∏ᶠ b, ∏ a ∈ hf.toFinset with g a = b, f a := finprod_congr hb
    _ = ∏ a ∈ hf.toFinset, f a := finprod_prod_filter g hf.toFinset f
    _ = ∏ᶠ a, f a := (finprod_eq_prod f hf).symm

/-- Multiplying a family by a finitely supported family whose product is `1` does not change its
product. The other family need not have finite multiplicative support: if it does not, neither
does the product family, and both products are `1`. -/
@[to_additive /-- Adding a finitely supported family whose sum is `0` to a family does not change
its sum. The other family need not have finite support: if it does not, neither does the sum
family, and both sums are `0`. -/]
theorem finprod_mul_eq_right_of_finprod_eq_one {ι : Type*} {f g : ι → M}
    (hf : HasFiniteMulSupport f) (hf1 : ∏ᶠ i, f i = 1) : ∏ᶠ i, f i * g i = ∏ᶠ i, g i := by
  by_cases hg : HasFiniteMulSupport g
  · rw [finprod_mul_distrib hf hg, hf1, one_mul]
  · have hfg : ¬HasFiniteMulSupport fun i ↦ f i * g i := fun hfg ↦ hg <|
      (hfg.union hf).subset fun i hi ↦ by
        by_contra h
        simp only [Set.mem_union, mem_mulSupport, not_or, not_not] at h
        exact hi (by simpa [h.2] using h.1)
    rw [finprod_of_infinite_mulSupport hfg, finprod_of_infinite_mulSupport hg]

/-- The two iterated products of a family of two variables agree when the family has finite
multiplicative support jointly in both variables. This is the `finprod` analogue of
`Finset.prod_comm`. -/
@[to_additive /-- The two iterated sums of a family of two variables agree when the family has
finite support jointly in both variables. This is the `finsum` analogue of `Finset.sum_comm`. -/]
theorem finprod_comm {ι κ : Type*} {f : ι → κ → M} (hf : HasFiniteMulSupport (uncurry f)) :
    ∏ᶠ i, ∏ᶠ k, f i k = ∏ᶠ k, ∏ᶠ i, f i k := by
  have hf' : HasFiniteMulSupport fun x : κ × ι ↦ f x.2 x.1 :=
    Set.Finite.preimage (Equiv.prodComm κ ι).injective.injOn hf
  calc
    ∏ᶠ i, ∏ᶠ k, f i k = ∏ᶠ x : ι × κ, f x.1 x.2 := (finprod_curry (uncurry f) hf).symm
    _ = ∏ᶠ x : κ × ι, f x.2 x.1 :=
      (finprod_comp_equiv (Equiv.prodComm κ ι) (f := fun x : ι × κ ↦ f x.1 x.2)).symm
    _ = ∏ᶠ k, ∏ᶠ i, f i k := finprod_curry _ hf'

end TauCeti

namespace Finset

open Function

section OrderedWithZero

variable {ι M₀ : Type*} [CommMonoidWithZero M₀] [PartialOrder M₀] [ZeroLEOneClass M₀]
  [PosMulMono M₀] {f : ι → M₀}

/-- A product over a finset is at most the `finprod` of a finitely supported family whose factors
off the finset are at least `1`. This is the `finprod` analogue of
`Finset.prod_le_prod_of_subset_of_one_le₀`. -/
theorem prod_le_finprod_of_one_le₀ (s : Finset ι) (hf : HasFiniteMulSupport f)
    (hf₀ : ∀ i ∈ s, 0 ≤ f i) (hf₁ : ∀ i ∉ s, 1 ≤ f i) : ∏ i ∈ s, f i ≤ ∏ᶠ i, f i := by
  classical
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (s := s ∪ hf.toFinset)
    fun i hi ↦ Finset.mem_union_right s (hf.mem_toFinset.mpr hi)]
  exact Finset.prod_le_prod_of_subset_of_one_le₀ Finset.subset_union_left hf₀
    fun i _ hi ↦ hf₁ i hi

/-- The `finprod` of a finitely supported nonnegative family whose factors off a finset are at
most `1` is at most the product over that finset. This is the `finprod` analogue of
`Finset.prod_le_prod_of_subset_of_le_one₀`. -/
theorem finprod_le_prod_of_le_one₀ (s : Finset ι) (hf : HasFiniteMulSupport f)
    (hf₀ : ∀ i, 0 ≤ f i) (hf₁ : ∀ i ∉ s, f i ≤ 1) : ∏ᶠ i, f i ≤ ∏ i ∈ s, f i := by
  classical
  rw [finprod_eq_finsetProd_of_mulSupport_subset f (s := s ∪ hf.toFinset)
    fun i hi ↦ Finset.mem_union_right s (hf.mem_toFinset.mpr hi)]
  exact Finset.prod_le_prod_of_subset_of_le_one₀ Finset.subset_union_left (fun i _ ↦ hf₀ i)
    fun i _ hi ↦ hf₁ i hi

end OrderedWithZero

end Finset
