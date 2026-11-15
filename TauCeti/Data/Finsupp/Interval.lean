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

Since the boxes `Iic m` are finite, subtracting a fixed multi-index has finite fibres.

## Main results

* `Finsupp.card_le_prod_of_forall_le`: `#s ≤ ∏ᵢ (rᵢ + 1)`.
* `Finsupp.sum_le_prod_mul_of_forall_le`: `∑ m ∈ s, f m ≤ ∏ᵢ (rᵢ + 1) C` when `f ≤ C` on `s`.
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

open Filter

/-- Subtracting a fixed multi-index `d` has finite fibres: if `n - d = m` then `n ≤ m + d`. -/
theorem tendsto_sub_cofinite {σ : Type*} (d : σ →₀ ℕ) :
    Tendsto (fun n : σ →₀ ℕ ↦ n - d) cofinite cofinite := by
  classical
  exact Tendsto.cofinite_of_finite_preimage_singleton fun m ↦
    ((Set.finite_Iic (m + d)).subset fun _ hn ↦
      tsub_le_iff_right.1 (le_of_eq hn)).to_subtype

end Finsupp
