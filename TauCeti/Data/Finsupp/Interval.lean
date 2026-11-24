/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Data.Finsupp.Antidiagonal
public import Mathlib.Data.Finsupp.Interval
public import Mathlib.Data.Pi.Interval
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Sets of multi-indices bounded coordinatewise

A finite set of multi-indices `m : σ →₀ ℕ` with `mᵢ ≤ rᵢ` for every `i` lies in the box
`Iic r`, so it has at most `∏ᵢ (rᵢ + 1)` elements. A sum over such a set of terms bounded by
`C ≥ 0` is therefore at most `∏ᵢ (rᵢ + 1) C`. This is how the monomials of a polynomial with
partial degrees `degreeOf i P ≤ r i` are counted.

In finitely many variables, a sum over the antidiagonal of `m`, the pairs `(a, b)` with
`a + b = m`, is a sum over the box `Iic m` of the corresponding functions `σ → ℕ`. This
translates Cauchy products of formal power series into multi-index sums over boxes.

## Main results

* `Finsupp.card_le_prod_of_forall_le`: `#s ≤ ∏ᵢ (rᵢ + 1)`.
* `Finsupp.sum_le_prod_mul_of_forall_le`: `∑ m ∈ s, f m ≤ ∏ᵢ (rᵢ + 1) C` when `f ≤ C` on `s`.
* `Finsupp.sum_antidiagonal_eq_sum_Iic_coe`: a sum over the antidiagonal of `m` is the sum over
  `Iic ⇑m` of the corresponding pairs of functions.
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
  calc #s ≤ #(Iic r) := card_le_card_of_injOn (⇑) (fun m hm ↦ mem_Iic.2 fun i ↦ h m hm i)
        DFunLike.coe_injective.injOn
    _ = ∏ i, (r i + 1) := by simp [Pi.card_Iic]

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

/-- In finitely many variables, a sum over the antidiagonal of a multi-index `m` is the sum over
the box `Iic ⇑m` of functions `σ → ℕ`, the second index being `⇑m - b`. -/
theorem sum_antidiagonal_eq_sum_Iic_coe {M : Type*} [AddCommMonoid M] [DecidableEq σ]
    (F : (σ → ℕ) → (σ → ℕ) → M) (m : σ →₀ ℕ) :
    ∑ p ∈ antidiagonal m, F p.1 p.2 = ∑ b ∈ Iic (m : σ → ℕ), F b (m - b) := by
  refine sum_nbij' (·.1) (fun b ↦ (equivFunOnFinite.symm b, m - equivFunOnFinite.symm b)) ?_
    (fun b hb ↦ mem_antidiagonal.2 <| add_tsub_cancel_of_le fun i ↦ by simpa using mem_Iic.1 hb i)
    ?_ (fun b _ ↦ by simp) ?_
  -- The remaining goals concern a pair `(a, b)` in the antidiagonal, so `m = a + b`.
  all_goals
    rintro ⟨a, b⟩ h
    rw [mem_antidiagonal] at h
    subst h
  · simp
  · simp
  · rw [← coe_tsub, add_tsub_cancel_left]

end Finsupp
