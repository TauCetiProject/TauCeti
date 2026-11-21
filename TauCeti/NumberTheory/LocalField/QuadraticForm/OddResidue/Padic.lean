/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.Basic
public import Mathlib.NumberTheory.Padics.RingHoms
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Symbol
import TauCeti.NumberTheory.LocalField.QuadraticForm.OddResidue.Formula
import TauCeti.NumberTheory.Padics.PadicIntegers
import TauCeti.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.HilbertSymbol.Henselian
import TauCeti.NumberTheory.LocalField.Henselian
import TauCeti.RingTheory.Henselian.SquareClasses

/-!
# Hilbert symbols over `ℚ_p` for odd `p`

Let `p` be an odd prime. The prime `p` is a uniformizer of `ℚ_p` and the residue field of `ℚ_p`
is `𝔽_p`, so the odd-residue formulas for the Hilbert symbol become formulas in terms of
residues modulo `p`.

* The residue sign of a unit `u` of `ℤ_p` is the quadratic character `(u / p)` of its reduction
  modulo `p`. Hence the odd-residue formula `TauCeti.hilbertSymbol_oddResidue_formula`, read at
  the uniformizer `p`, is Serre's closed formula: for `a = p ^ α u` and `b = p ^ β v` with `u, v`
  units of `ℤ_p`, `(a, b)_p = (-1) ^ (α β (p - 1)/2) · (u / p) ^ β · (v / p) ^ α`. Every element
  of `ℚ_pˣ` has this form, so the formula computes the symbol on all of `ℚ_pˣ`; for integers it
  reads in Legendre symbols.
* Two integers prime to `p` are units of `ℤ_p`, and their symbol is `1`.
* For an integer `n` prime to `p`, the symbol `(n, p)_p` is the Legendre symbol `(n / p)`: it is `1`
  exactly when `n` is a square modulo `p`. Together with the dyadic value
  `TauCeti.hilbertSymbol_natCast_natCast_padicTwo`, these are the local factors of the product
  formula behind quadratic reciprocity. As the symbol of a unit with the uniformizer detects
  squares, such an `n` is a square in `ℚ_p` exactly when it is a square modulo `p`.
* For `p ≡ 3 (mod 4)` the unit `-1` has nonsquare residue in `𝔽_p`, so `(-1, p)_p = -1`: the
  prime `p` is not of the form `x² + y²` in `ℚ_p`. Equivalently, by
  `TauCeti.hilbertSymbol_eq_one_iff_not_anisotropic_weightedSumSquares`, the ternary form
  `⟨1, 1, -p⟩` is anisotropic over `ℚ_p`. For `p = 3` this is the local obstruction carried by
  the form `⟨1, 1, -3⟩` over `ℚ`, which is isotropic over `ℝ` but anisotropic over `ℚ_3`.

## Main results

* `Units.oddResidueSign_map_integerRingEquiv_symm_eq_quadraticChar`: the residue sign of a unit
  of `ℤ_p` is the quadratic character of its reduction modulo `p`.
* `TauCeti.Padic.hilbertSymbol_formula_of_ne_two`: Serre's formula for the Hilbert symbol over
  `ℚ_p`.
* `TauCeti.Padic.coe_hilbertSymbol_pow_mul_intCast_pow_mul_intCast`: the same formula for
  `p ^ α m` and `p ^ β n` with integers `m, n` prime to `p`, in Legendre symbols.
* `TauCeti.Padic.hilbertSymbol_intCast_intCast_eq_one`: `(m, n)_p = 1` for integers `m, n` prime
  to `p`.
* `TauCeti.Padic.hilbertSymbol_intCast_self_eq_legendreSym`: `(n, p)_p = (n / p)` for an integer
  `n` prime to `p`.
* `TauCeti.Padic.isSquare_intCast_iff_legendreSym_eq_one`: an integer prime to `p` is a square in
  `ℚ_p` exactly when it is a square modulo `p`.
* `TauCeti.PadicInt.isSquare_iff_quadraticChar_toZMod_eq_one`: a unit of `ℤ_p` is a square in
  `ℤ_p` exactly when its reduction modulo `p` has quadratic character `1`.
* `TauCeti.PadicInt.isSquare_intCast_iff_legendreSym_eq_one`: an integer prime to `p` is a square in
  `ℤ_p` exactly when it is a square modulo `p`.
* `TauCeti.PadicInt.isSquare_mul_iff_quadraticChar_toZMod_eq`: the product of two units of `ℤ_p` is
  a square in `ℤ_p` exactly when their reductions modulo `p` have equal quadratic characters.
* `TauCeti.PadicInt.isSquare_mul_of_dvd_sub`: two `p`-adic integers congruent modulo `p`, one of
  which is a unit, have a square product in `ℤ_p`.
* `TauCeti.PadicInt.quadraticChar_toZMod_prod_eq_prod_legendreSym` and
  `TauCeti.PadicInt.isSquare_prod_mul_prod_iff_legendreSym_eq`: finite products of `p`-adic units
  have the same square class in `ℤ_p` exactly when the corresponding products of Legendre symbols
  of integer lifts modulo `p` agree.
* `Padic.hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three`: `(-1, p)_p = -1` when
  `p ≡ 3 (mod 4)`.

## References

* J.-P. Serre, *A Course in Arithmetic*, Chapter III, §1, Theorem 1.
-/

public section

open TauCeti ValuativeRel IsLocalRing

namespace Units

variable {p : ℕ} [Fact p.Prime]

open _root_.TauCeti.Units

/-- **The residue sign over `ℚ_p` is the Legendre character.** For a unit `u` of `ℤ_p`, the
residue sign of `u`, read in the integer ring of `ℚ_p`, is the quadratic character of the reduction
of `u` modulo `p`; for `u` the image of an integer `n`, this is `legendreSym p n`. -/
theorem oddResidueSign_map_integerRingEquiv_symm_eq_quadraticChar (u : ℤ_[p]ˣ) :
    oddResidueSign (Units.map ((_root_.Padic.integerRingEquiv p).symm : ℤ_[p] →* 𝒪[ℚ_[p]]) u) =
      (quadraticChar (ZMod p)).toUnitHom
        (Units.map (PadicInt.toZMod (p := p) : ℤ_[p] →* ZMod p) u) := by
  classical
  -- The residue field of `ℚ_[p]` is `𝔽_p`, the residue of `u` going to `u mod p`.
  let E : 𝓀[ℚ_[p]] ≃+* ZMod p :=
    (ResidueField.mapEquiv (_root_.Padic.integerRingEquiv p)).trans PadicInt.residueField
  let : Fintype 𝓀[ℚ_[p]] := Fintype.ofFinite _
  -- The ring isomorphism `E` preserves squares, hence the quadratic character.
  have hχ (x : 𝓀[ℚ_[p]]) : quadraticChar (ZMod p) (E x) = quadraticChar 𝓀[ℚ_[p]] x := by
    have hsq : IsSquare (E x) ↔ IsSquare x :=
      ⟨fun h ↦ by simpa using h.map E.symm, fun h ↦ h.map E⟩
    simp only [quadraticChar_apply, quadraticCharFun, map_eq_zero_iff E E.injective, hsq]
  apply Units.ext
  rw [oddResidueSign_int, MulChar.coe_toUnitHom, Units.coe_map, MonoidHom.coe_ofClass, ← hχ]
  simp [E, PadicInt.toZMod_eq_residueField_comp_residue]

end Units

namespace TauCeti.Padic

variable (p : ℕ) [Fact p.Prime]

variable {p} in
/-- **Serre's formula for the Hilbert symbol over `ℚ_p`, for `p` odd.** For `a = p ^ α u` and
`b = p ^ β v` with `u, v` units of `ℤ_p`,

`(a, b) = ((-1) ^ ((p - 1)/2)) ^ (α β) · (u / p) ^ β · (v / p) ^ α`,

where `(u / p)` is the quadratic character of the reduction of `u` modulo `p`, as a sign. -/
theorem hilbertSymbol_formula_of_ne_two (hp : p ≠ 2) {a b : ℚ_[p]ˣ} {α β : ℤ} {u v : ℤ_[p]ˣ}
    (ha : (a : ℚ_[p]) = (p : ℚ_[p]) ^ α * u) (hb : (b : ℚ_[p]) = (p : ℚ_[p]) ^ β * v) :
    hilbertSymbol a b = ((-1 : ℤˣ) ^ ((p - 1) / 2)) ^ (α * β) *
      (quadraticChar (ZMod p)).toUnitHom
        (Units.map (PadicInt.toZMod (p := p) : ℤ_[p] →* ZMod p) u) ^ β *
      (quadraticChar (ZMod p)).toUnitHom
        (Units.map (PadicInt.toZMod (p := p) : ℤ_[p] →* ZMod p) v) ^ α := by
  let ι : ℤ_[p]ˣ → 𝒪[ℚ_[p]]ˣ :=
    Units.map ((_root_.Padic.integerRingEquiv p).symm : ℤ_[p] →* 𝒪[ℚ_[p]])
  let π : ℚ_[p]ˣ := padicPrimeUnit p
  have hdecomp {c : ℚ_[p]ˣ} {γ : ℤ} {w : ℤ_[p]ˣ} (hc : (c : ℚ_[p]) = (p : ℚ_[p]) ^ γ * w) :
      c = π ^ γ * Units.map (Subring.subtype 𝒪[ℚ_[p]] : 𝒪[ℚ_[p]] →* ℚ_[p]) (ι w) :=
    Units.ext (by simp [hc, π, ι])
  rw [hdecomp ha, hdecomp hb,
    hilbertSymbol_oddResidue_formula (_root_.Padic.isUnit_two_integerRing hp)
      (isUniformizer_padicPrimeUnit p), Fintype.card_eq_nat_card, _root_.Padic.natCard_residueField,
    Units.oddResidueSign_map_integerRingEquiv_symm_eq_quadraticChar,
    Units.oddResidueSign_map_integerRingEquiv_symm_eq_quadraticChar]

variable {p} in
/-- **Serre's formula over `ℚ_p` for integers, with Legendre symbols.** For an odd prime `p`,
integers `m, n` prime to `p` and natural numbers `α, β`,

`(p ^ α m, p ^ β n) = (-1) ^ (α β (p - 1)/2) · (m / p) ^ β · (n / p) ^ α`. -/
theorem coe_hilbertSymbol_pow_mul_intCast_pow_mul_intCast (hp : p ≠ 2) (α β : ℕ) {m n : ℤ}
    (hm : ¬ (p : ℤ) ∣ m) (hn : ¬ (p : ℤ) ∣ n) :
    ((hilbertSymbol
        (Units.mk0 ((p : ℚ_[p]) ^ α * m) (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2
          (Fact.out : p.Prime).ne_zero)) (Int.cast_ne_zero.2 fun h ↦ hm (h ▸ dvd_zero _))))
        (Units.mk0 ((p : ℚ_[p]) ^ β * n) (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2
          (Fact.out : p.Prime).ne_zero)) (Int.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero _)))) :
        ℤˣ) : ℤ) =
      (-1) ^ (α * β * ((p - 1) / 2)) * legendreSym p m ^ β * legendreSym p n ^ α := by
  have hum := PadicInt.isUnit_intCast_iff.2 hm
  have hun := PadicInt.isUnit_intCast_iff.2 hn
  rw [hilbertSymbol_formula_of_ne_two hp (α := α) (β := β) (u := hum.unit) (v := hun.unit)
    (by simp) (by simp)]
  simp only [← Nat.cast_mul, zpow_natCast, ← pow_mul, Units.val_mul, Units.val_pow_eq_pow_val,
    Units.val_neg, Units.val_one, MulChar.coe_toUnitHom, Units.coe_map, MonoidHom.coe_ofClass,
    IsUnit.unit_spec, map_intCast, legendreSym]
  ring

variable {p} in
/-- **The Hilbert symbol of two `p`-adic units.** For an odd prime `p` and integers `m` and `n`
prime to `p`, the Hilbert symbol `(m, n)` over `ℚ_p` is `1`. -/
theorem hilbertSymbol_intCast_intCast_eq_one (hp : p ≠ 2) {m n : ℤ} (hm : ¬ (p : ℤ) ∣ m)
    (hn : ¬ (p : ℤ) ∣ n) :
    hilbertSymbol (Units.mk0 (m : ℚ_[p]) (Int.cast_ne_zero.2 fun h ↦ hm (h ▸ dvd_zero _)))
      (Units.mk0 (n : ℚ_[p]) (Int.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero _))) = 1 := by
  have h := hilbertSymbol_units_map_eq_one (K := ℚ_[p]) (_root_.Padic.isUnit_two_integerRing hp)
    (_root_.Padic.isUnit_intCast_integerRing hm).unit
    (_root_.Padic.isUnit_intCast_integerRing hn).unit
  convert h using 2 <;> ext <;> simp

variable {p} in
/-- **The Hilbert symbol `(n, p)` over `ℚ_p` is the Legendre symbol `(n / p)`**, for an odd prime
`p` and an integer `n` prime to `p`: the integral unit `n` pairs with the uniformizer `p` to `1`
exactly when its residue is a square in `𝔽_p`. -/
theorem hilbertSymbol_intCast_self_eq_legendreSym (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    ((hilbertSymbol (Units.mk0 (n : ℚ_[p]) (Int.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero _)))
      (padicPrimeUnit p) : ℤˣ) : ℤ) =
      legendreSym p n := by
  have h1 : ¬ (p : ℤ) ∣ 1 := by exact_mod_cast (Fact.out : p.Prime).not_dvd_one
  simpa [padicPrimeUnit_eq_mk0] using
    coe_hilbertSymbol_pow_mul_intCast_pow_mul_intCast hp 0 1 hn h1

variable {p} in
/-- **Squares in `ℚ_p` of integers prime to `p`.** For an odd prime `p` and an integer `n` prime
to `p`, the image of `n` in `ℚ_p` is a square exactly when `n` is a square modulo `p`, that is
`(n / p) = 1`. -/
theorem isSquare_intCast_iff_legendreSym_eq_one (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsSquare (n : ℚ_[p]) ↔ legendreSym p n = 1 := by
  have hval := _root_.Padic.toAdd_normalizedValuation_eq_zero_of_coe_eq
    (a := Units.mk0 (n : ℚ_[p]) (Int.cast_ne_zero.2 fun h ↦ hn (h ▸ dvd_zero _)))
    (u := (PadicInt.isUnit_intCast_iff.2 hn).unit) (by simp)
  have h := hilbertSymbol_eq_one_iff_isSquare_of_valuation_zero_of_isUniformizer
    (_root_.Padic.isUnit_two_integerRing hp) hval (isUniformizer_padicPrimeUnit p)
  rw [← Units.val_eq_one, hilbertSymbol_intCast_self_eq_legendreSym hp hn] at h
  rw [h, ← Units.isSquare_coe_iff, Units.val_mk0]

end TauCeti.Padic

namespace Padic

variable (p : ℕ) [Fact p.Prime]

/-- If `p ≡ 3 (mod 4)`, then the Hilbert symbol `(-1, p)` over `ℚ_p` is `-1`: the prime `p` is not
a sum of two squares in `ℚ_p`. -/
theorem hilbertSymbol_neg_one_eq_neg_one_of_mod_four_eq_three (hp : p % 4 = 3) :
    hilbertSymbol (-1 : ℚ_[p]ˣ) (TauCeti.padicPrimeUnit p) = -1 := by
  have h2 := isUnit_two_integerRing (p := p) (by omega)
  have hu : (normalizedValuation ℚ_[p] (-1 : ℚ_[p]ˣ)).toAdd = 0 := by
    rw [toAdd_normalizedValuation_eq_valuation]
    simpa [padicValInt] using valuation_intCast (p := p) (-1)
  rcases Int.units_eq_one_or (hilbertSymbol (-1 : ℚ_[p]ˣ) _) with h | h
  · have hsq := (hilbertSymbol_eq_one_iff_isSquare_of_valuation_zero_of_isUniformizer h2 hu
      (TauCeti.isUniformizer_padicPrimeUnit p)).mp h
    exact absurd (Units.isSquare_coe_iff.mpr hsq)
      (by simpa using not_isSquare_neg_one_of_mod_four_ne_one p (by omega))
  · exact h

end Padic

namespace TauCeti.PadicInt

variable {p : ℕ} [Fact p.Prime]

/-- **Squares of units in `ℤ_p`.** For an odd prime `p`, a unit of `ℤ_p` is a square in `ℤ_p` if
and only if its reduction modulo `p` has quadratic character `1`. -/
theorem isSquare_iff_quadraticChar_toZMod_eq_one (hp : p ≠ 2) {u : ℤ_[p]} (hu : IsUnit u) :
    IsSquare u ↔ quadraticChar (ZMod p) (_root_.PadicInt.toZMod u) = 1 := by
  have hres : IsSquare (residue ℤ_[p] u) ↔ IsSquare (_root_.PadicInt.toZMod u) := by
    rw [_root_.PadicInt.toZMod_eq_residueField_comp_residue, RingHom.comp_apply]
    exact ⟨fun h ↦ h.map _root_.PadicInt.residueField,
      fun h ↦ by simpa using h.map _root_.PadicInt.residueField.symm⟩
  rw [TauCeti.HenselianLocalRing.isSquare_iff_residue_isSquare (_root_.PadicInt.isUnit_two hp) hu,
    hres, quadraticChar_one_iff_isSquare ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu)]

/-- **Squares in `ℤ_p` of integers prime to `p`.** For an odd prime `p` and an integer `n` prime
to `p`, the image of `n` in `ℤ_p` is a square in `ℤ_p` exactly when `n` is a square modulo `p`,
that is `(n / p) = 1`. -/
theorem isSquare_intCast_iff_legendreSym_eq_one (hp : p ≠ 2) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n) :
    IsSquare (n : ℤ_[p]) ↔ legendreSym p n = 1 := by
  have hu : IsUnit (n : ℤ_[p]) := _root_.PadicInt.isUnit_intCast_iff.mpr hn
  simpa [legendreSym] using isSquare_iff_quadraticChar_toZMod_eq_one hp hu

/-- For an odd prime `p`, the product of two units of `ℤ_p` is a square in `ℤ_p` if and only if
their reductions modulo `p` have equal quadratic characters. -/
theorem isSquare_mul_iff_quadraticChar_toZMod_eq (hp : p ≠ 2) {u v : ℤ_[p]}
    (hu : IsUnit u) (hv : IsUnit v) :
    IsSquare (u * v) ↔
      quadraticChar (ZMod p) (_root_.PadicInt.toZMod u) =
        quadraticChar (ZMod p) (_root_.PadicInt.toZMod v) := by
  rw [isSquare_iff_quadraticChar_toZMod_eq_one hp (hu.mul hv), map_mul, map_mul]
  rcases quadraticChar_dichotomy ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu) with
    h1 | h1 <;>
    rcases quadraticChar_dichotomy ((_root_.PadicInt.isUnit_iff_toZMod_ne_zero v).mp hv) with
      h2 | h2 <;>
    simp [h1, h2]

/-- For an odd prime `p`, if two `p`-adic integers agree modulo `p` and one is a unit, then their
product is a square in `ℤ_p`. -/
theorem isSquare_mul_of_dvd_sub (hp : p ≠ 2) {u v : ℤ_[p]} (hu : IsUnit u)
    (huv : (p : ℤ_[p]) ∣ u - v) : IsSquare (u * v) := by
  have hmod : _root_.PadicInt.toZMod u = _root_.PadicInt.toZMod v :=
    (_root_.PadicInt.toZMod_eq_iff_dvd_sub u v).mpr huv
  have hv : IsUnit v := (_root_.PadicInt.isUnit_iff_toZMod_ne_zero v).mpr
    (hmod ▸ (_root_.PadicInt.isUnit_iff_toZMod_ne_zero u).mp hu)
  exact (isSquare_mul_iff_quadraticChar_toZMod_eq hp hu hv).mpr (by rw [hmod])

/-- For a finite family of `p`-adic integers congruent modulo `p` to integers `a i`, the quadratic
character of `∏ i ∈ s, u i` modulo `p` equals `∏ i ∈ s, legendreSym p (a i)`. -/
theorem quadraticChar_toZMod_prod_eq_prod_legendreSym {ι : Type*} (s : Finset ι)
    (u : ι → ℤ_[p]) (a : ι → ℤ) (ha : ∀ i ∈ s, (p : ℤ_[p]) ∣ u i - a i) :
    quadraticChar (ZMod p) (_root_.PadicInt.toZMod (∏ i ∈ s, u i)) =
      ∏ i ∈ s, legendreSym p (a i) := by
  rw [map_prod, map_prod]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  have hmod : _root_.PadicInt.toZMod (u i) = (a i : ZMod p) := by
    simpa only [map_intCast] using (_root_.PadicInt.toZMod_eq_iff_dvd_sub (u i) (a i)).mpr (ha i hi)
  rw [hmod, legendreSym]

/-- For an odd prime `p` and finite families of `p`-adic units congruent modulo `p` to integers
`a i` and `b j`, the product `(∏ i ∈ s, u i) * (∏ j ∈ t, v j)` is a square in `ℤ_p` if and only if
`∏ i ∈ s, legendreSym p (a i) = ∏ j ∈ t, legendreSym p (b j)`. -/
theorem isSquare_prod_mul_prod_iff_legendreSym_eq (hp : p ≠ 2) {ι κ : Type*}
    (s : Finset ι) (t : Finset κ) (u : ι → ℤ_[p]) (v : κ → ℤ_[p]) (a : ι → ℤ) (b : κ → ℤ)
    (hu : ∀ i ∈ s, IsUnit (u i)) (hv : ∀ j ∈ t, IsUnit (v j))
    (ha : ∀ i ∈ s, (p : ℤ_[p]) ∣ u i - a i) (hb : ∀ j ∈ t, (p : ℤ_[p]) ∣ v j - b j) :
    IsSquare ((∏ i ∈ s, u i) * ∏ j ∈ t, v j) ↔
      ∏ i ∈ s, legendreSym p (a i) = ∏ j ∈ t, legendreSym p (b j) := by
  rw [isSquare_mul_iff_quadraticChar_toZMod_eq hp (IsUnit.prod_iff.mpr hu) (IsUnit.prod_iff.mpr hv),
    quadraticChar_toZMod_prod_eq_prod_legendreSym s u a ha,
    quadraticChar_toZMod_prod_eq_prod_legendreSym t v b hb]

end TauCeti.PadicInt
