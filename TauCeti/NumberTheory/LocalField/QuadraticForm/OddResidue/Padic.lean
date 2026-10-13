/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Symbol
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.HilbertSymbol.Henselian
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Hilbert symbols of integers over `ℚ_p` for odd `p`

Let `p` be an odd prime. The prime `p` is a uniformizer of `ℚ_p` and the residue field of `ℚ_p`
is `𝔽_p`, so the odd-residue formulas for the Hilbert symbol become formulas in terms of
residues modulo `p`.

* Two natural numbers prime to `p` are units of `ℤ_p`, and their symbol is `1`.
* For `n` prime to `p`, the symbol `(n, p)_p` is the Legendre symbol `(n / p)`: it is `1`
  exactly when `n` is a square modulo `p`. Together with the dyadic value
  `TauCeti.hilbertSymbol_natCast_natCast_padicTwo`, these are the local factors of the product
  formula behind quadratic reciprocity.
* For `p ≡ 3 (mod 4)` the unit `-1` has nonsquare residue in `𝔽_p`, so `(-1, p)_p = -1`: the
  prime `p` is not of the form `x² + y²` in `ℚ_p`. Equivalently, by
  `TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares`, the ternary form
  `⟨1, 1, -p⟩` is anisotropic over `ℚ_p`. For `p = 3` this is the local obstruction carried by
  the form `⟨1, 1, -3⟩` over `ℚ`, which is isotropic over `ℝ` but anisotropic over `ℚ_3`.

## Main results

* `Padic.hilbertSymbol_natCast_natCast_eq_one`: `(m, n)_p = 1` for `m, n` prime to `p`.
* `Padic.hilbertSymbol_natCast_self_eq_legendreSym`: `(n, p)_p = (n / p)` for `n` prime to `p`.
* `Padic.hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three`: `(-1, p)_p = -1` when
  `p ≡ 3 (mod 4)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 1.
-/

public section

open TauCeti ValuativeRel IsLocalRing

namespace Padic

variable (p : ℕ) [Fact p.Prime]

variable {p} in
/-- **The Hilbert symbol of two `p`-adic units.** For an odd prime `p` and natural numbers `m`
and `n` prime to `p`, the Hilbert symbol `(m, n)` over `ℚ_p` is `1`. -/
theorem hilbertSymbol_natCast_natCast_eq_one (hp : p ≠ 2) {m n : ℕ} (hm : ¬ p ∣ m)
    (hn : ¬ p ∣ n) :
    hilbertSymbol (Units.mk0 (m : ℚ_[p]) (Nat.cast_ne_zero.2 fun h ↦ hm (h ▸ dvd_zero p)))
      (Units.mk0 (n : ℚ_[p]) (Nat.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero p))) = 1 := by
  have hcop {k : ℕ} (hk : ¬ p ∣ k) : IsUnit (k : 𝒪[ℚ_[p]]) := by
    simpa using (PadicInt.isUnit_natCast_of_coprime
      (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hk)).map (integerRingEquiv p).symm
  have h2 : IsUnit (2 : 𝒪[ℚ_[p]]) := by
    simpa using hcop fun h ↦ hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h)
  have h := hilbertSymbol_units_map_eq_one (K := ℚ_[p]) h2 (hcop hm).unit (hcop hn).unit
  convert h using 2 <;> ext <;> simp

variable {p} in
/-- **The Hilbert symbol `(n, p)` over `ℚ_p` is the Legendre symbol `(n / p)`**, for an odd prime
`p` and a natural number `n` prime to `p`: the integral unit `n` pairs with the uniformizer `p` to
`1` exactly when its residue is a square in `𝔽_p`. -/
theorem hilbertSymbol_natCast_self_eq_legendreSym (hp : p ≠ 2) {n : ℕ} (hn : ¬ p ∣ n) :
    ((hilbertSymbol (Units.mk0 (n : ℚ_[p]) (Nat.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero p)))
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) : ℤˣ) : ℤ) =
      legendreSym p n := by
  classical
  have h2 : IsUnit (2 : 𝒪[ℚ_[p]]) :=
    (natCastValuation_eq_zero_iff (K := ℚ_[p]) 2 (by norm_num)).mp (natCastValuation_two p hp)
  -- `n` is an integral unit of `ℚ_[p]`.
  have hu : IsUnit (n : 𝒪[ℚ_[p]]) := by
    simpa using (PadicInt.isUnit_natCast_of_coprime
      (((Fact.out : p.Prime).coprime_iff_not_dvd).2 hn)).map (integerRingEquiv p).symm
  have hmk : Units.map (Subring.subtype 𝒪[ℚ_[p]] : 𝒪[ℚ_[p]] →* ℚ_[p]) hu.unit =
      Units.mk0 (n : ℚ_[p]) (Nat.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero p)) :=
    Units.ext (by simp)
  -- The residue field of `ℚ_[p]` is `𝔽_p`, the residue of `n` going to `n`.
  let E : 𝓀[ℚ_[p]] ≃+* ZMod p :=
    (ResidueField.mapEquiv (integerRingEquiv p)).trans PadicInt.residueField
  have hres : IsSquare (Units.map (residue 𝒪[ℚ_[p]] : 𝒪[ℚ_[p]] →* 𝓀[ℚ_[p]]) hu.unit) ↔
      IsSquare (n : ZMod p) := by
    rw [← isSquare_units_val_iff]
    have hE : E (Units.map (residue 𝒪[ℚ_[p]] : 𝒪[ℚ_[p]] →* 𝓀[ℚ_[p]]) hu.unit : 𝓀[ℚ_[p]]) =
        n := by
      simp
    rw [← hE]
    exact ⟨fun h ↦ h.map E, fun h ↦ by simpa using h.map E.symm⟩
  have hn0 : ((n : ℤ) : ZMod p) ≠ 0 := by
    rw [Int.cast_natCast, Ne, ZMod.natCast_eq_zero_iff]
    exact hn
  rw [← hmk,
    hilbertSymbol_unit_uniformizer_eq_ite h2 _ (TauCeti.Padic.isUniformizer_natCast_self p)]
  split_ifs with h <;> rw [hres] at h
  · exact ((legendreSym.eq_one_iff p hn0).2 (by simpa using h)).symm
  · exact ((legendreSym.eq_neg_one_iff p).2 (by simpa using h)).symm

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
  rcases Int.units_eq_one_or (hilbertSymbol (-1 : ℚ_[p]ˣ) _) with h | h
  · have hsq := (hilbertSymbol_eq_one_iff_isSquare_of_valuation_zero_of_isUniformizer h2 hu
      (TauCeti.Padic.isUniformizer_natCast_self p)).mp h
    exact absurd (isSquare_units_val_iff.mpr hsq)
      (by simpa using not_isSquare_neg_one_of_mod_four_eq_three p hp)
  · exact h

end Padic
