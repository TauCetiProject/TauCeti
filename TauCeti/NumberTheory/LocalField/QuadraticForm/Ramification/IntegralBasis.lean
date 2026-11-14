/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Eisenstein.Quadratic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.Defect.Basic

/-!
# The integral basis of `K(√u)` for a unit of odd quadratic defect

Let `K` be a nonarchimedean local field, `π` a uniformizer, and `u` a unit of `𝒪[K]` whose defect
exponent `δ(u) = 2k + 1` is odd, so that `K(√u)/K` is ramified. An optimal square approximation
`b² ` of `u`, with `v_K(u - b²) = 2k + 1`, gives the element `ω = (√u - b)/π^k`. It is a root of
`X² + (2b/π^k) X + (b² - u)/π^{2k}`, which is Eisenstein: the constant coefficient has valuation
`1`, and the middle coefficient has valuation `v_K(2) - k > 0` because the possible defects of a
unit force `2k + 1 < 2 v_K(2)`. Hence `(1, ω)` is a basis of `𝒪[K(√u)]` over `𝒪[K]`.

This is the integral basis on which the unit norms of a ramified quadratic extension are read
off. Its trace and norm are `Tr ω = -2b/π^k` and `N ω = (b² - u)/π^{2k}`.

## Main results

* `TauCeti.exists_basis_integerRing_of_defectExponent_eq_odd`: the basis `(1, (√u - b)/π^k)`, with
  its trace and norm.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §63A.
-/

public section

open ValuativeRel IsLocalRing IsNonarchimedeanLocalField

namespace TauCeti

variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [Algebra K L] [ValuativeExtension K L]
  [Algebra.IsQuadraticExtension K L]

/-- **The integral basis of `K(√u)` for a unit of odd defect** (O'Meara §63A). Let `π` be a
uniformizer of `K`, `u` a unit of `𝒪[K]` with defect exponent `2k + 1`, and `x ∈ L` a square root
of `u`. Then there is `b ∈ K` with `v_K(u - b²) = 2k + 1` such that `(1, ω)`, `ω = (x - b)/π^k`, is
a basis of `𝒪[L]` over `𝒪[K]`, with `Tr ω = -2b/π^k` and `N ω = (b² - u)/π^{2k}`. -/
theorem exists_basis_integerRing_of_defectExponent_eq_odd {π : 𝒪[K]} (hπ : Irreducible π)
    {u : Kˣ} (hu : valuation K (u : K) = 1) {k : ℕ}
    (hd : defectExponent u = ((2 * k + 1 : ℕ) : ℤ)) {x : L}
    (hx2 : x ^ 2 = algebraMap K L u) :
    ∃ b : K, valuation K ((u : K) - b ^ 2) = valuation K (π : K) ^ (2 * k + 1) ∧
      ∃ B : Module.Basis (Fin 2) 𝒪[K] 𝒪[L], B 0 = 1 ∧
        (B 1 : L) = (x - algebraMap K L b) / algebraMap K L ((π : K) ^ k) ∧
        Algebra.trace K L (B 1 : L) = -(2 * b / (π : K) ^ k) ∧
        Algebra.norm K (B 1 : L) = (b ^ 2 - u) / (π : K) ^ (2 * k) := by
  have hπ0 : (π : K) ≠ 0 := fun h ↦ hπ.ne_zero (Subtype.ext h)
  have hπk : (π : K) ^ k ≠ 0 := pow_ne_zero k hπ0
  obtain ⟨b, t, c, hbv, htm, hc, ht_eq, hc_eq⟩ :=
    exists_eisenstein_coefficients_of_defectExponent_eq_odd hπ hu hd
  obtain ⟨B, h0, h1, htr, hn⟩ := exists_basis_integerRing_of_sq_eq (t := t) (c := c)
    (b := b) hx2 hπk htm hc (by rw [ht_eq]; exact (mul_div_cancel₀ _ hπk).symm)
    (by rw [hc_eq, ← pow_mul, mul_comm k 2]; exact (mul_div_cancel₀ _ (pow_ne_zero _ hπ0)).symm)
  exact ⟨b, hbv, B, h0, h1, ht_eq ▸ htr, hc_eq ▸ hn⟩
end TauCeti
