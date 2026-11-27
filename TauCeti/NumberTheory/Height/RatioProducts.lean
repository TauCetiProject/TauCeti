/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.FamilyOverPairs

/-!
# Heights of products of inverse ratios

In a determinant comparison, the ratio for one pair can itself be a product of several
ratios of special values. A bound for each inverse ratio gives a bound for the inverse of
the full product, even after inserting a rational power of the twist modulus. This power
costs no height when the modulus at each embedding is prime to its residue characteristic.

The estimate follows the budget of `New.Data.HasSmallRatios.heightLe_inv_rpow_mul_prod` in
`grh/src/New/Determinant/Chain/Moduli.lean` of lsernau/grh-lean (revision `72fead1`).
-/

public section

namespace TauCeti.PrimePadicIso

/-- If each of the products indexed by `A` contains at most `t` ratios whose inverses have
height at most `c`, the inverse of the combined product has height at most `#A * t * c`.
A rational power of a modulus prime to the prime of each embedding does not affect the bound.
The products need not have the same length, and ratios are allowed to vanish. -/
theorem heightLe_inv_rpow_mul_prod {α β : Type*} {A : Finset α} {B : α → Finset β} {t : ℕ}
    {f : α → β → PrimePadicIso → ℂ} {c : ℝ} (hc : 0 ≤ c)
    (hcard : ∀ a ∈ A, (B a).card ≤ t)
    (hf : ∀ a ∈ A, ∀ i ∈ B a, HeightLe (fun ι ↦ (f a i ι)⁻¹) c)
    {N : PrimePadicIso → ℕ} (hN : ∀ ι : PrimePadicIso, ι.prime.Coprime (N ι)) (e : ℚ) :
    HeightLe (fun ι ↦ (((N ι : ℝ) ^ (e : ℝ) : ℝ) * (∏ a ∈ A, ∏ i ∈ B a, f a i ι))⁻¹)
      ((A.card : ℝ) * t * c) := by
  have hrow (a : α) (ha : a ∈ A) : HeightLe (fun ι ↦ (∏ i ∈ B a, f a i ι)⁻¹) (t * c) := by
    have h := HeightLe.prod (hf a ha)
    have hcost : ((B a).card : ℝ) * c ≤ t * c :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard a ha) hc
    refine h.mono (by simpa using hcost) (fun ι ↦ ?_)
    simp [Finset.prod_apply, Finset.prod_inv_distrib]
  have h := (HeightLe.prod hrow).rpow_mul N (fun _ ↦ -e) hN
  refine h.mono (by simp [mul_assoc]) (fun ι ↦ ?_)
  simp [Real.rpow_neg (Nat.cast_nonneg _), mul_inv_rev, mul_comm, Finset.prod_apply,
    Finset.prod_inv_distrib]

end TauCeti.PrimePadicIso
