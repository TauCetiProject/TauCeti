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

Specializes `TauCeti.HasProductSieveDimension` to the sifting prime factors
`s.prodPrimes.primeFactors` and multiplicative density `s.nu` of a `BoundingSieve`, providing a
shared Euler-product dimension hypothesis usable across combinatorial and Selberg-type sieves.

## Main definitions and results

* `BoundingSieve.HasProductDimension`: Euler-product sieve dimension on `s.prodPrimes.primeFactors`
  for `s.nu`.
* `BoundingSieve.hasProductDimension_def`: explicit quantifier and product formula.
* `BoundingSieve.hasProductDimension_iff_hasProductSieveDimension`: equivalence with
  `TauCeti.HasProductSieveDimension (s.prodPrimes.primeFactors : Set ℕ) s.nu`.
* `BoundingSieve.HasProductDimension.mono_const`, `BoundingSieve.HasProductDimension.mono_dim`:
  monotonicity in the constant `K` and in the dimension `κ`.

## References

* K. S. Kedlaya, *Notes on Analytic Number Theory*, Chapter 12, §12.4.
* D. R. Heath-Brown, *Lectures on sieves*, §1 (2002).
-/

public noncomputable section

open Finset Nat Real

namespace BoundingSieve

/-- The Euler-product dimension bound on the prime factors of the native sieve product. -/
def HasProductDimension (s : BoundingSieve) (κ K : ℝ) : Prop :=
  ∀ w z : ℝ, 2 ≤ w → w ≤ z →
    (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
      (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ

/-- Explicit formula for `BoundingSieve.HasProductDimension`. -/
theorem hasProductDimension_def (s : BoundingSieve) (κ K : ℝ) :
    s.HasProductDimension κ K ↔
      ∀ w z : ℝ, 2 ≤ w → w ≤ z →
        (∏ p ∈ s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z),
          (1 - s.nu p)⁻¹) ≤ K * (Real.log z / Real.log w) ^ κ := Iff.rfl

/-- `BoundingSieve.HasProductDimension` agrees with `TauCeti.HasProductSieveDimension` on the prime
set `(s.prodPrimes.primeFactors : Set ℕ)` and density `s.nu`. -/
theorem hasProductDimension_iff_hasProductSieveDimension (s : BoundingSieve) (κ K : ℝ) :
    s.HasProductDimension κ K ↔
      TauCeti.HasProductSieveDimension (s.prodPrimes.primeFactors : Set ℕ) s.nu κ K := by
  classical
  rw [hasProductDimension_def, TauCeti.hasProductSieveDimension_def]
  refine forall₄_congr fun w z _ _ ↦ ?_
  have hfin : s.prodPrimes.primeFactors.filter (fun p : ℕ ↦ w ≤ (p : ℝ) ∧ (p : ℝ) < z) =
      (Finset.range ⌈z⌉₊).filter
        (fun p : ℕ ↦ p ∈ (s.prodPrimes.primeFactors : Set ℕ) ∧ p.Prime ∧ w ≤ (p : ℝ)) := by
    ext p
    simp only [mem_filter, mem_range, Nat.lt_ceil, mem_coe]
    exact ⟨fun ⟨hp, hw, hz⟩ ↦ ⟨hz, hp, Nat.prime_of_mem_primeFactors hp, hw⟩,
      fun ⟨hz, hp, _, hw⟩ ↦ ⟨hp, hw, hz⟩⟩
  rw [hfin]
  convert Iff.rfl

/-- Monotonicity of `BoundingSieve.HasProductDimension` in the constant `K`. -/
theorem HasProductDimension.mono_const {s : BoundingSieve} {κ K₁ K₂ : ℝ}
    (h : s.HasProductDimension κ K₁) (hK : K₁ ≤ K₂) :
    s.HasProductDimension κ K₂ := by
  rw [hasProductDimension_iff_hasProductSieveDimension] at h ⊢
  exact h.mono_const hK

/-- Monotonicity of `BoundingSieve.HasProductDimension` in the dimension `κ`. -/
theorem HasProductDimension.mono_dim {s : BoundingSieve} {κ₁ κ₂ K : ℝ}
    (h : s.HasProductDimension κ₁ K) (hκ : κ₁ ≤ κ₂) :
    s.HasProductDimension κ₂ K := by
  rw [hasProductDimension_iff_hasProductSieveDimension] at h ⊢
  exact h.mono_dim hκ

end BoundingSieve
