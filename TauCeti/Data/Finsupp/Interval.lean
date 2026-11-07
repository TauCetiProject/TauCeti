/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sets of multi-indices bounded coordinatewise

A finite set of multi-indices `m : σ →₀ ℕ` with `mᵢ ≤ rᵢ` for every `i` lies in the box
`Iic r`, so it has at most `∏ᵢ (rᵢ + 1)` elements. A sum over such a set of terms bounded by
`C ≥ 0` is therefore at most `∏ᵢ (rᵢ + 1) C`. This is how the monomials of a polynomial with
partial degrees `degreeOf i P ≤ r i` are counted.

Since the boxes `Iic m` are finite, subtracting a fixed multi-index has finite fibres. When
`j ∉ s.support`, the box `Iic (single j k + s)` decomposes along coordinate `j` as `Iic k ×ˢ Iic s`.

## Main results

* `Finsupp.card_le_prod_of_forall_le`: `#s ≤ ∏ᵢ (rᵢ + 1)`.
* `Finsupp.sum_le_prod_mul_of_forall_le`: `∑ m ∈ s, f m ≤ ∏ᵢ (rᵢ + 1) C` when `f ≤ C` on `s`.
* `Finsupp.Iic_single_add`, `Finsupp.prod_Iic_single_add`, `Finsupp.sum_Iic_single_add`:
  splitting `Iic (single j k + s)` into `Iic k` and `Iic s` when `j ∉ s.support`.
* `Finsupp.tendsto_sub_cofinite`: `n ↦ n - d` maps the cofinite filter into itself.
-/

public section

open Finset

namespace Finsupp

variable {σ : Type*} [Fintype σ]

/-- A finite set of multi-indices bounded coordinatewise by `r` has at most `∏ᵢ (rᵢ + 1)`
elements. -/
theorem card_le_prod_of_forall_le {s : Finset (σ →₀ ℕ)} {r : σ → ℕ}
    (h : ∀ m ∈ s, ∀ i, m i ≤ r i) : #s ≤ ∏ i, (r i + 1) := by
  classical
  set f : σ →₀ ℕ := equivFunOnFinite.symm r
  have hs : s ⊆ Iic f := fun m hm ↦ mem_Iic.2 fun i ↦ by simpa [f] using h m hm i
  have hf : #(Iic f) = ∏ i, (r i + 1) := by
    rw [card_Iic, prod_subset (subset_univ _) fun i _ hi ↦ by
      simp [f, notMem_support_iff.1 hi]]
    simp [f]
  exact (card_le_card hs).trans hf.le

/-- A sum of terms bounded by `C ≥ 0` over a set of multi-indices bounded coordinatewise by `r`
is at most `∏ᵢ (rᵢ + 1) C`. -/
theorem sum_le_prod_mul_of_forall_le {R : Type*} [CommSemiring R] [PartialOrder R]
    [IsOrderedRing R] {s : Finset (σ →₀ ℕ)} {r : σ → ℕ} (hs : ∀ m ∈ s, ∀ i, m i ≤ r i)
    {f : (σ →₀ ℕ) → R} {C : R} (hf : ∀ m ∈ s, f m ≤ C) (hC : 0 ≤ C) :
    ∑ m ∈ s, f m ≤ (∏ i, ((r i : R) + 1)) * C := by
  refine (sum_le_card_nsmul s f C hf).trans ?_
  rw [nsmul_eq_mul]
  gcongr
  simpa using Nat.mono_cast (α := R) (card_le_prod_of_forall_le hs)

end Finsupp

namespace Finsupp

section SingleAdd

variable {σ α : Type*} [DecidableEq σ] [AddCommMonoid α] [PartialOrder α]
  [CanonicallyOrderedAdd α] [OrderBot α] [LocallyFiniteOrder α] [DecidableEq α]

/-- When `j ∉ s.support`, the initial interval `Iic (single j k + s)` is the image of
`Iic k ×ˢ Iic s` under `(m, β') ↦ single j m + β'`. -/
theorem Iic_single_add {j : σ} (k : α) {s : σ →₀ α} (hj : j ∉ s.support) :
    Iic (single j k + s) = (Iic k ×ˢ Iic s).image fun p ↦ single j p.1 + p.2 := by
  have hsj : s j = 0 := notMem_support_iff.1 hj
  ext β
  simp only [mem_Iic, mem_image, mem_product, Prod.exists]
  constructor
  · intro hβ
    refine ⟨β j, β.erase j, ⟨?_, fun i ↦ ?_⟩, single_add_erase j β⟩
    · simpa [hsj] using hβ j
    · rcases eq_or_ne i j with rfl | hij
      · simp
      · simpa [hij, hij.symm] using hβ i
  · rintro ⟨m, β', ⟨hm, hβ'⟩, rfl⟩
    exact fun i ↦ add_le_add (single_le_single.2 hm i) (hβ' i)

/-- When `j ∉ s.support`, a product over `Iic (single j k + s)` splits as an iterated product over
`m ∈ Iic k` and `β' ∈ Iic s`. -/
@[to_additive (dont_translate := σ α)
/-- When `j ∉ s.support`, a sum over `Iic (single j k + s)` splits as an iterated sum over
`m ∈ Iic k` and `β' ∈ Iic s`. -/]
theorem prod_Iic_single_add {M : Type*} [CommMonoid M] {j : σ} (k : α) {s : σ →₀ α}
    (hj : j ∉ s.support) (f : (σ →₀ α) → M) :
    ∏ β ∈ Iic (single j k + s), f β =
      ∏ m ∈ Iic k, ∏ β' ∈ Iic s, f (single j m + β') := by
  have hsj : s j = 0 := notMem_support_iff.1 hj
  rw [Iic_single_add k hj, prod_image, prod_product]
  rintro ⟨m₁, β₁⟩ hp₁ ⟨m₂, β₂⟩ hp₂ heq
  rw [mem_coe, mem_product, mem_Iic, mem_Iic] at hp₁ hp₂
  have hβ₁j : β₁ j = 0 := nonpos_iff_eq_zero.1 ((hp₁.2 j).trans_eq hsj)
  have hβ₂j : β₂ j = 0 := nonpos_iff_eq_zero.1 ((hp₂.2 j).trans_eq hsj)
  have hm : m₁ = m₂ := by simpa [hβ₁j, hβ₂j] using DFunLike.congr_fun heq j
  refine Prod.ext hm (Finsupp.ext fun i ↦ ?_)
  rcases eq_or_ne i j with rfl | hij
  · exact hβ₁j.trans hβ₂j.symm
  · simpa [hij, hij.symm] using DFunLike.congr_fun heq i

end SingleAdd

open Filter

/-- Subtracting a fixed multi-index `d` has finite fibres: if `n - d = m` then `n ≤ m + d`. -/
theorem tendsto_sub_cofinite {σ : Type*} (d : σ →₀ ℕ) :
    Tendsto (fun n : σ →₀ ℕ ↦ n - d) cofinite cofinite := by
  classical
  exact Tendsto.cofinite_of_finite_preimage_singleton fun m ↦
    ((Set.finite_Iic (m + d)).subset fun _ hn ↦
      tsub_le_iff_right.1 (le_of_eq hn)).to_subtype

end Finsupp
