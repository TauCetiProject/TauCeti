/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Airy.Basic
public import TauCeti.Analysis.Complex.Sector.Zeros

/-!
# Complex sector zeros of Airy functions

Following DLMF §9.9(i), the zeros of `airyBi` and `deriv airyBi` in the open sector
`π / 3 < arg z < π / 2` are indexed from `k = 1` by modulus. To make `TauCeti.airySectorZero f k`
well-defined before distinctness of moduli is proved, equal-modulus ties are broken by principal
argument (`Complex.polarLt`).

Because `airyBi` and `deriv airyBi` are entire and nonzero at the origin, their zeros in
`π / 3 < arg z < π / 2` are locally norm-finite (`TauCeti.finite_airySectorZeros`), and every zero
of `airyBi` or `deriv airyBi` in that sector equals `airySectorZero f k` for some `k ≥ 1`
(`TauCeti.exists_airySectorZero_eq`).

## Main definitions and results

* `TauCeti.airySectorZero`: the `k`-th zero of `f : ℂ → ℂ` in `π / 3 < arg z < π / 2` in polar
  order, defined as `TauCeti.sectorZero (π / 3) (π / 2) f k`.
* `TauCeti.finite_airySectorZeros`: for `f = airyBi` or `f = deriv airyBi`, the sector zeros
  `TauCeti.sectorZeros (π / 3) (π / 2) f` of norm at most `R` form a finite set.
* `TauCeti.exists_airySectorZero_eq`: for `f = airyBi` or `f = deriv airyBi`, every zero of `f` in
  `π / 3 < arg z < π / 2` equals `airySectorZero f k` for some `k ≥ 1`.

## References

* NIST Digital Library of Mathematical Functions, §9.9(i), <https://dlmf.nist.gov/9.9>.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- The `k`-th zero (`k ≥ 1`) of `f` in the open sector `π / 3 < arg z < π / 2`, ordered by modulus
and, among zeros of equal modulus, by principal argument: exactly `k - 1` zeros in the sector
precede it in that order. -/
abbrev airySectorZero (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  sectorZero (π / 3) (π / 2) f k

/-- For `f = airyBi` or `f = deriv airyBi`, `f` has at most finitely many sector zeros of norm
`≤ R` in `π / 3 < arg z < π / 2`. -/
theorem finite_airySectorZeros {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi) (R : ℝ) :
    {z ∈ sectorZeros (π / 3) (π / 2) f | ‖z‖ ≤ R}.Finite := by
  rcases hf with rfl | rfl
  · exact finite_sectorZeros_of_differentiable differentiable_airyBi ⟨0, airyBi_zero_ne_zero⟩ R
  · exact finite_sectorZeros_of_differentiable differentiable_airyBi.deriv
      ⟨0, deriv_airyBi_zero_ne_zero⟩ R

/-- **Unconditional completeness of `airySectorZero`.** For `f = airyBi` or `f = deriv airyBi`,
every zero `z` of `f` in `π / 3 < arg z < π / 2` equals `airySectorZero f k` for some `k ≥ 1`. -/
theorem exists_airySectorZero_eq {f : ℂ → ℂ} (hf : f = airyBi ∨ f = deriv airyBi)
    {z : ℂ} (h₁ : π / 3 < arg z) (h₂ : arg z < π / 2) (hfz : f z = 0) :
    ∃ k : ℕ, 1 ≤ k ∧ airySectorZero f k = z :=
  exists_sectorZero_eq (finite_airySectorZeros hf)
    (mem_sectorZeros_iff.mpr
      ⟨fun h0 => by rw [h0, arg_zero] at h₁; linarith [Real.pi_pos], h₁, h₂, hfz⟩)

end TauCeti
