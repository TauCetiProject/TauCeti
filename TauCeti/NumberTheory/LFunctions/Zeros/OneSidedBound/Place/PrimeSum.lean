/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Place.OfInt

/-!
# Capped prime sums at cyclotomic places

At a place `τ`, each prime power `n` is charged against the cutoff weight at the
translated place `[-n] * τ`. The cap can therefore depend on `n`, unlike in a Riesz
sum with a single cutoff. A common lower bound on the weights shows when enlarging
the ambient cutoff does not change the sum. This lets the same finite sum be used
at the full order and at smaller derivative orders.

The convention is that of `New.Data.primeSum` in
`grh/src/New/Reduction/Data/AdmissibleData.lean` of [grh-lean](https://github.com/lsernau/grh-lean)
at revision `72fead1`.
-/

public section

open Finset

namespace TauCeti.OneSidedBound.Parameters

/-- The Legendre-weighted prime sum at order `y` and place `τ`, with varying caps `κ`
and natural cutoff `N`. The labels of the places are the cyclotomic units at level `s`. -/
noncomputable def placePrimeSum (P : Parameters) (s N : ℕ)
    (κ : (ZMod (P.q₁ s))ˣ → ℝ) (y : ℝ) (τ : (ZMod (P.q₁ s))ˣ) : ℝ :=
  ∑ n ∈ Icc 1 N, primeWeight P.d 1 n * max (y / n - κ (P.placeOfInt s (-(n : ℤ)) * τ)) 0

/-- Expand the capped prime sum as a sum over integers from `1` to `N`. -/
theorem placePrimeSum_def (P : Parameters) (s N : ℕ)
    (κ : (ZMod (P.q₁ s))ˣ → ℝ) (y : ℝ) (τ : (ZMod (P.q₁ s))ˣ) :
    P.placePrimeSum s N κ y τ =
      ∑ n ∈ Icc 1 N, primeWeight P.d 1 n * max (y / n - κ (P.placeOfInt s (-(n : ℤ)) * τ)) 0 :=
  (rfl)

/-- At order zero, nonnegative cap weights give no contribution. -/
@[simp] theorem placePrimeSum_zero (P : Parameters) {s : ℕ} (N : ℕ)
    {κ : (ZMod (P.q₁ s))ˣ → ℝ} (hκ : ∀ τ, 0 ≤ κ τ) (τ : (ZMod (P.q₁ s))ˣ) :
    P.placePrimeSum s N κ 0 τ = 0 := by
  simp [placePrimeSum_def, max_eq_right (neg_nonpos.mpr (hκ _))]

/-- Scaling the order and all cap weights by the same nonnegative factor scales the prime
sum by that factor. -/
theorem placePrimeSum_mul (P : Parameters) {s : ℕ} (N : ℕ) (κ : (ZMod (P.q₁ s))ˣ → ℝ)
    (y : ℝ) (τ : (ZMod (P.q₁ s))ˣ) {c : ℝ} (hc : 0 ≤ c) :
    P.placePrimeSum s N (fun σ ↦ c * κ σ) (c * y) τ = c * P.placePrimeSum s N κ y τ := by
  rw [placePrimeSum_def, placePrimeSum_def, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ ↦ ?_
  have h (z : ℝ) : max (c * z) 0 = c * max z 0 := by
    simpa only [mul_zero] using (mul_max_of_nonneg z 0 hc).symm
  rw [mul_div_assoc, ← mul_sub, h]
  ring

/-- If the cap weights are at least `c ≥ 0`, then indices past `N` contribute nothing at
orders at most `(N + 1) * c`. Thus an increased cutoff leaves the prime sum unchanged. -/
theorem placePrimeSum_eq_of_le_cutoff (P : Parameters) {s N M : ℕ}
    {κ : (ZMod (P.q₁ s))ˣ → ℝ} {y c : ℝ} (τ : (ZMod (P.q₁ s))ˣ)
    (hNM : N ≤ M) (hc : 0 ≤ c) (hκ : ∀ σ, c ≤ κ σ) (hy : y ≤ ((N : ℝ) + 1) * c) :
    P.placePrimeSum s N κ y τ = P.placePrimeSum s M κ y τ := by
  simp only [placePrimeSum_def]
  refine sum_subset (Icc_subset_Icc_right hNM) fun n hn hn' ↦ ?_
  have hn₁ := (mem_Icc.mp hn).1
  have hN : N + 1 ≤ n := by
    by_contra! h
    exact hn' (mem_Icc.mpr ⟨hn₁, by omega⟩)
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn₁
  have hc' : y / (n : ℝ) ≤ c := (div_le_iff₀ hn₀).mpr <| by
    rw [mul_comm c]
    exact hy.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hN) hc)
  rw [max_eq_right (sub_nonpos.mpr (hc'.trans (hκ _))), mul_zero]

end TauCeti.OneSidedBound.Parameters
