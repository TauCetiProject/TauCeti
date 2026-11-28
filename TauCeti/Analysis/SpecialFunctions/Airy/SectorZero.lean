/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Sector.Zeros
public import TauCeti.Analysis.SpecialFunctions.Airy.Basic

/-!
# The zeros of a function in the sector `π/3 < ph z < π/2`

The nonreal zeros of `Bi` and `Bi′` in the upper half-plane lie in the sector `π/3 < ph z < π/2`,
where they are listed as `β₁, β₂, …` and `β′₁, β′₂, …` in order of increasing modulus
(DLMF §9.9(i)). This file defines `TauCeti.airySectorZero` as an abbreviation for the general
polar-ordered sector-zero enumeration `TauCeti.sectorZero (π / 3) (π / 2)`: the `k`-th zero of
`f : ℂ → ℂ` in `sectorZeros (π / 3) (π / 2) f` with respect to `Complex.polarLt` (modulus first,
then principal argument).

Because `airySectorZero` is reducible (`abbrev`), the general `TauCeti.sectorZero_*` API from
`TauCeti.Analysis.Complex.Sector.Zeros` — including `TauCeti.sectorZero_def`,
`TauCeti.sectorZero_zero`, `TauCeti.sectorZero_eq_of_ncard`, `TauCeti.exists_sectorZero_eq`,
`TauCeti.sectorZero_spec_of_le_encard`, `TauCeti.sectorZero_spec_of_infinite`,
`TauCeti.polarLt_sectorZero_of_lt`, and `TauCeti.norm_sectorZero_le_norm_sectorZero` — applies
directly to `airySectorZero` whenever `f` has finitely many sector zeros in each closed disc
around `0` and (for attainment or monotonicity) a valid positive index `1 ≤ k` with
`(k : ℕ∞) ≤ (sectorZeros (π / 3) (π / 2) f).encard`. For `f = airyBi` and `f = deriv airyBi`,
that local norm-finiteness hypothesis is supplied by `TauCeti.finite_airySectorZeros` (via
`TauCeti.finite_sectorZeros_of_differentiable`).

## Main definitions and results

* `TauCeti.airySectorZero`: the `k`-th zero (`k ≥ 1`) of `f` in `π / 3 < arg z < π / 2` in
  `Complex.polarLt` order, defined as `TauCeti.sectorZero (π / 3) (π / 2)`.
* `TauCeti.finite_airySectorZeros`: for `f = airyBi` or `f = deriv airyBi`, the sector zeros
  `TauCeti.sectorZeros (π / 3) (π / 2) f` of norm at most `R` form a finite set.

## References

* NIST Digital Library of Mathematical Functions, §9.9(i), <https://dlmf.nist.gov/9.9>.
-/

public section

noncomputable section

open Complex
open scoped Real

namespace TauCeti

/-- Total polar-ordered selector `TauCeti.sectorZero (π / 3) (π / 2)` for zeros of `f` in the
open sector `π / 3 < arg z < π / 2`. When `f` has finitely many sector zeros in each closed disc
around `0`, `1 ≤ k`, and `(k : ℕ∞) ≤ (sectorZeros (π / 3) (π / 2) f).encard`,
`airySectorZero f k` attains its defining specification (`TauCeti.sectorZero_spec_of_le_encard`).
At `k = 0`, `airySectorZero f 0 = airySectorZero f 1` (`TauCeti.sectorZero_zero`). -/
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

end TauCeti
