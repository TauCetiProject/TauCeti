/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.SelbergSieve
public import TauCeti.NumberTheory.SieveDimension.Basic

/-!
# Euler-product sieve dimension for `BoundingSieve`

Abbreviates `TauCeti.HasProductSieveDimension` at the sifting prime factors
`(s.prodPrimes.primeFactors : Set ℕ)` and multiplicative density `s.nu` of a `BoundingSieve`, so
`one_le_const`, `mono_const`, and `mono_dim` apply directly while `hasProductDimension_iff` and
`HasProductDimension.prod_le` rewrite the interval product over `s.prodPrimes.primeFactors`.

## Main definitions and results

* `BoundingSieve.HasProductDimension`: abbreviation for
  `TauCeti.HasProductSieveDimension (s.prodPrimes.primeFactors : Set ℕ) s.nu`.
* `BoundingSieve.hasProductDimension_iff`, `BoundingSieve.HasProductDimension.prod_le`:
  characterization and interval bound on `s.prodPrimes.primeFactors.filter (w ≤ · ∧ · < z)`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, §12.3–12.4.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
-/

public noncomputable section

open Finset Nat Real

namespace BoundingSieve

/-- The Euler-product dimension bound on the prime factors of the native sieve product,
abbreviating `TauCeti.HasProductSieveDimension` at `(s.prodPrimes.primeFactors : Set ℕ)` and
`s.nu`. -/
abbrev HasProductDimension (s : BoundingSieve) (κ K : ℝ) : Prop :=
  TauCeti.HasProductSieveDimension (s.prodPrimes.primeFactors : Set ℕ) s.nu κ K

open Classical in
/-- `BoundingSieve.HasProductDimension` is equivalent to bounding the Euler-product ratio over
`s.prodPrimes.primeFactors.filter (fun p ↦ w ≤ p ∧ p < z)` for all `2 ≤ w ≤ z`. -/
theorem hasProductDimension_iff (s : BoundingSieve) (κ K : ℝ) :
    s.HasProductDimension κ K ↔
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
          (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ := by
  rw [HasProductDimension, TauCeti.hasProductSieveDimension_def]
  refine forall₄_congr fun w z _ _ ↦ Iff.of_eq (congrArg
    (fun S ↦ (∏ p ∈ S, (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ) ?_)
  ext p
  simp only [mem_filter, mem_range, Nat.lt_ceil, mem_coe]
  exact ⟨fun ⟨hz, hp, _, hw⟩ ↦ ⟨hp, hw, hz⟩,
    fun ⟨hp, hw, hz⟩ ↦ ⟨hz, hp, Nat.prime_of_mem_primeFactors hp, hw⟩⟩

/-- Applying `BoundingSieve.HasProductDimension` on `2 ≤ w ≤ z` bounds the Euler-product ratio over
prime factors of `s.prodPrimes` in `[w, z)` by `K * (log z / log w) ^ κ`. -/
theorem HasProductDimension.prod_le {s : BoundingSieve} {κ K w z : ℝ}
    (h : s.HasProductDimension κ K) (hw : 2 ≤ w) (hwz : w ≤ z) :
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ :=
  (s.hasProductDimension_iff κ K).mp h w z hw hwz

end BoundingSieve
