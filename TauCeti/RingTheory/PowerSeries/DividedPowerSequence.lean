/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Power series whose coefficients multiply like divided powers

A sequence `(γₙ)` in a commutative semiring multiplies like divided powers when
`γₘ * γₙ = (m + n).choose m • γₘ₊ₙ` for all `m` and `n`; these are the multiplication relations
of a divided power structure, and the coefficients of `exp(a X) = ∑ (aⁿ / n!) Xⁿ` satisfy them
over a `ℚ`-algebra. This file proves that the power series whose coefficients multiply like
divided powers are closed under multiplication. The proof is the Vandermonde identity
`Nat.add_choose_eq`, and divides by no factorial.

This closure is what makes the divided-power exponential `∑ₙ γₙ(x) Xⁿ` of a sum of elements
satisfy the multiplication relations again, as in the base change of divided power algebras.

## Main declarations

* `PowerSeries.coeff_mul_coeff_mul_eq_choose_nsmul`: if the coefficients of `f` and of `g`
  multiply like divided powers, then so do those of `f * g`.
-/

public section

namespace PowerSeries

open Finset

variable {A : Type*} [CommSemiring A]

/-- If the coefficients of `f` and of `g` multiply like divided powers, that is
`fₘ * fₙ = (m + n).choose m • fₘ₊ₙ` and likewise for `g`, then so do the coefficients of
`f * g`. -/
theorem coeff_mul_coeff_mul_eq_choose_nsmul {f g : A⟦X⟧}
    (hf : ∀ m n, coeff m f * coeff n f = (m + n).choose m • coeff (m + n) f)
    (hg : ∀ m n, coeff m g * coeff n g = (m + n).choose m • coeff (m + n) g) (m n : ℕ) :
    coeff m (f * g) * coeff n (f * g) = (m + n).choose m • coeff (m + n) (f * g) := by
  -- The term of the double sum indexed by `x ∈ antidiagonal m` and `p ∈ antidiagonal (m + n)`.
  set F : ℕ × ℕ → ℕ × ℕ → A := fun x p ↦
    (p.1.choose x.1 * p.2.choose x.2) • (coeff p.1 f * coeff p.2 g) with hF
  -- For fixed `x`, the terms with `p = x + y`, `y ∈ antidiagonal n`, exhaust the nonzero ones.
  have hx (x : ℕ × ℕ) (hx : x ∈ antidiagonal m) :
      ∑ y ∈ antidiagonal n, F x (x + y) = ∑ p ∈ antidiagonal (m + n), F x p := by
    have hmap := sum_map (antidiagonal n) (addLeftEmbedding x) (F x)
    simp only [addLeftEmbedding_apply] at hmap
    rw [← hmap]
    refine sum_subset (fun p hp ↦ ?_) fun p hp hp' ↦ ?_
    · obtain ⟨y, hy, rfl⟩ := mem_map.mp hp
      rw [mem_antidiagonal] at hx hy ⊢
      simp only [addLeftEmbedding_apply, Prod.fst_add, Prod.snd_add]
      omega
    · have hle : ¬(x.1 ≤ p.1 ∧ x.2 ≤ p.2) := fun hle ↦ hp' <| mem_map.mpr
        ⟨(p.1 - x.1, p.2 - x.2), by rw [mem_antidiagonal] at hx hp ⊢; omega, by
          ext <;> simp [hle.1, hle.2]⟩
      rw [not_and_or, not_le, not_le] at hle
      rcases hle with h | h <;> simp [hF, Nat.choose_eq_zero_of_lt h]
  simp only [coeff_mul, sum_mul_sum, smul_sum]
  calc ∑ x ∈ antidiagonal m, ∑ y ∈ antidiagonal n,
        coeff x.1 f * coeff x.2 g * (coeff y.1 f * coeff y.2 g)
      = ∑ x ∈ antidiagonal m, ∑ y ∈ antidiagonal n, F x (x + y) := by
        refine sum_congr rfl fun x _ ↦ sum_congr rfl fun y _ ↦ ?_
        simp only [hF, Prod.fst_add, Prod.snd_add]
        rw [mul_mul_mul_comm, hf, hg, smul_mul_smul_comm]
    _ = ∑ p ∈ antidiagonal (m + n), ∑ x ∈ antidiagonal m, F x p := by
        rw [sum_congr rfl hx, sum_comm]
    _ = _ := by
        refine sum_congr rfl fun p hp ↦ ?_
        rw [mem_antidiagonal] at hp
        rw [← hp, Nat.add_choose_eq, sum_smul]

end PowerSeries
