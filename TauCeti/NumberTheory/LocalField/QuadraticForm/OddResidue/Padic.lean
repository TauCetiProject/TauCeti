/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Symbol
import TauCeti.Algebra.Group.Units.Basic

/-!
# The Hilbert symbol `(-1, p)` over `ℚ_p`

For a prime `p ≡ 3 (mod 4)` the unit `-1` has nonsquare residue in `𝔽_p`, and `p` is a
uniformizer of `ℚ_p`. The odd-residue unit–uniformizer calculation therefore gives
`(-1, p)_p = -1`: the prime `p` is not of the form `x² + y²` in `ℚ_p`. Equivalently, by
`TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares`, the ternary form
`⟨1, 1, -p⟩` is anisotropic over `ℚ_p`.

For `p = 3` this is the local obstruction carried by the form `⟨1, 1, -3⟩` over `ℚ`, which is
isotropic over `ℝ` but anisotropic over `ℚ_3`.

## Main results

* `Padic.hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three`: `(-1, p)_p = -1` when
  `p ≡ 3 (mod 4)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 1.
-/

public section

open TauCeti ValuativeRel

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- If `p ≡ 3 (mod 4)`, then the Hilbert symbol `(-1, p)` over `ℚ_p` is `-1`: the prime `p` is not
a sum of two squares in `ℚ_p`. -/
theorem hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three (hp : p % 4 = 3) :
    hilbertSymbol (-1 : ℚ_[p]ˣ)
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) = -1 := by
  have h2 : IsUnit (2 : 𝒪[ℚ_[p]]) :=
    (natCastValuation_eq_zero_iff (K := ℚ_[p]) 2 (by norm_num)).mp
      (natCastValuation_two p (by omega))
  have hu : (normalizedValuation ℚ_[p] (-1 : ℚ_[p]ˣ)).toAdd = 0 := by
    rw [toAdd_normalizedValuation_eq_valuation]
    simpa [padicValInt] using valuation_intCast (p := p) (-1)
  have hπ : IsUniformizer ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) := by
    rw [isUniformizer_def]
    apply Multiplicative.toAdd.injective
    rw [toAdd_normalizedValuation_eq_valuation, Units.val_mk0, valuation_p, toAdd_ofAdd]
  rcases Int.units_eq_one_or (hilbertSymbol (-1 : ℚ_[p]ˣ) _) with h | h
  · have hsq := (hilbertSymbol_eq_one_iff_isSquare_of_valuation_zero_of_isUniformizer h2 hu hπ).mp h
    exact absurd (isSquare_units_val_iff.mpr hsq)
      (by simpa using not_isSquare_neg_one_of_mod_four_eq_three p hp)
  · exact h

end Padic
