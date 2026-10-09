/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Order.Ring.Units
public import TauCeti.Data.ZMod.ExactDivisor
public import TauCeti.NumberTheory.LocalField.Padic
public import TauCeti.NumberTheory.LocalField.UnitsDecomposition
public import TauCeti.NumberTheory.Padics.RingHoms
import Mathlib.Analysis.Normed.Ring.Ultra
import TauCeti.NumberTheory.Padics.PadicIntegers

/-!
# Explicit local symbols for cyclotomic extensions of the rationals

For a prime `p` and a positive modulus `m`, this file defines the explicit homomorphism

`cyclotomicSymbol m p : ℚ_pˣ →* (ZMod m)ˣ`.

Write `m = p ^ j * d`, with `p ∤ d`, and `x = p ^ k w`, with `w ∈ ℤ_pˣ`. The symbol is the
unique residue class which is `w⁻¹` modulo `p ^ j` and `p ^ k` modulo `d`. The two reduction
theorems in this file characterize it without exposing its Chinese-remainder construction. The
real symbol is the sign, viewed in `(ZMod m)ˣ`.

These are the local factors in the elementary product formula for cyclotomic extensions of `ℚ`.
The normalization follows J. S. Milne, *Class Field Theory*, VII, Example 8.2.

## Main definitions

* `TauCeti.cyclotomicSymbol`: the explicit symbol at a finite prime.
* `TauCeti.realCyclotomicSymbol`: the explicit symbol at the real place.

## Main results

* `TauCeti.unitsMap_cyclotomicSymbol_primePow`: on the `p`-primary part of the modulus, the
  symbol is the inverse of the unit part.
* `TauCeti.unitsMap_cyclotomicSymbol_of_coprime`: on every divisor of the modulus coprime to
  `p`, the symbol is the valuation part `p ^ k`.
* `TauCeti.unitsMap_cyclotomicSymbol_primePow_of_eq_unit`,
  `TauCeti.unitsMap_cyclotomicSymbol_of_coprime_of_eq_unit`,
  `TauCeti.unitsMap_cyclotomicSymbol_self_primePow` and
  `TauCeti.unitsMap_cyclotomicSymbol_self_of_coprime`: the two reductions at a `p`-adic unit and
  at `p` itself.
* `TauCeti.cyclotomicSymbol_of_coprime`: at a prime not dividing the modulus, the symbol is `p`
  raised to the valuation.
* `TauCeti.cyclotomicSymbol_eq_one_of_norm_sub_one_lt` and
  `TauCeti.cyclotomicSymbol_eq_of_norm_sub_lt`: the symbol is trivial near `1`, hence locally
  constant.
* `TauCeti.realCyclotomicSymbol_of_pos` and `TauCeti.realCyclotomicSymbol_of_neg`: the two values
  of the real symbol.
-/

public section

noncomputable section

open scoped TauCeti.ExactDivisor

namespace TauCeti

private def padicPrimeUnit (p : ℕ) [Fact p.Prime] : ℚ_[p]ˣ :=
  Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)

private theorem normalizedValuation_padicPrimeUnit (p : ℕ) [Fact p.Prime] :
    normalizedValuation ℚ_[p] (padicPrimeUnit p) = .ofAdd 1 := by
  rw [padicPrimeUnit, normalizedValuation_natCast, Padic.natCastValuation_self]
  norm_num

private def padicUnitReduction (p j : ℕ) [Fact p.Prime] :
    unitFiltration ℚ_[p] 0 →* (ZMod (p ^ j))ˣ :=
  (PadicInt.unitsToZModPow j).toMonoidHom.comp
    ((Units.mapEquiv (Padic.integerRingEquiv p).toMulEquiv).toMonoidHom.comp
      unitFiltrationZeroEquivIntegerUnits.toMonoidHom)

private def padicIntegerUnitToFiltration (p : ℕ) [Fact p.Prime] :
    ℤ_[p]ˣ ≃* unitFiltration ℚ_[p] 0 :=
  (Units.mapEquiv (Padic.integerRingEquiv p).toMulEquiv).symm.trans
    unitFiltrationZeroEquivIntegerUnits.symm

private theorem coe_padicIntegerUnitToFiltration (p : ℕ) [Fact p.Prime] (w : ℤ_[p]ˣ) :
    (((padicIntegerUnitToFiltration p w : unitFiltration ℚ_[p] 0) : ℚ_[p]ˣ) : ℚ_[p]) = w :=
  by
    simp [padicIntegerUnitToFiltration, Units.coe_mapEquiv]

private theorem padicUnitReduction_padicIntegerUnitToFiltration (p j : ℕ) [Fact p.Prime]
    (w : ℤ_[p]ˣ) :
    padicUnitReduction p j (padicIntegerUnitToFiltration p w) =
      Units.map (PadicInt.toZModPow j : ℤ_[p] →+* ZMod (p ^ j)).toMonoidHom w :=
  by
    apply Units.ext
    simp [padicUnitReduction, padicIntegerUnitToFiltration, Units.coe_mapEquiv]

private theorem unitsEquivIntProd_eq_of_padic_decomposition (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]ˣ) (k : ℤ) (w : ℤ_[p]ˣ)
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * ((w : ℤ_[p]) : ℚ_[p])) :
    unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
      (normalizedValuation_padicPrimeUnit p) x =
        (.ofAdd k, padicIntegerUnitToFiltration p w) := by
  have hx_units : x = (padicPrimeUnit p) ^ k * padicIntegerUnitToFiltration p w := by
    apply Units.ext
    simpa [padicPrimeUnit, coe_padicIntegerUnitToFiltration] using hx
  rw [hx_units]
  have h := (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
    (normalizedValuation_padicPrimeUnit p)).apply_symm_apply
      (.ofAdd k, padicIntegerUnitToFiltration p w)
  simpa only [unitsEquivIntProd_symm_apply, toAdd_ofAdd] using h

private def cyclotomicSymbolComponents (m p : ℕ) [NeZero m] [Fact p.Prime] :
    Multiplicative ℤ × unitFiltration ℚ_[p] 0 →*
      (ZMod (p ^ padicValNat p m))ˣ × (ZMod (m / p ^ padicValNat p m))ˣ :=
  ((padicUnitReduction p (padicValNat p m))⁻¹.comp (MonoidHom.snd _ _)).prod
    ((zpowersHom _ (ZMod.unitOfCoprime p (by
      simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
        Nat.coprime_ordCompl (Fact.out : p.Prime) (NeZero.ne m)))).comp
      (MonoidHom.fst _ _))

/-- **The explicit local symbol of `ℚ(μ_m)/ℚ` at `p`.** If `m = p ^ j * d`, with `p ∤ d`, and
`x = p ^ k w`, with `w ∈ ℤ_pˣ`, then the symbol is the unique class in `(ZMod m)ˣ` which is
`w⁻¹` modulo `p ^ j` and `p ^ k` modulo `d`.

The two components are recorded by `unitsMap_cyclotomicSymbol_primePow` and
`unitsMap_cyclotomicSymbol_of_coprime`. -/
def cyclotomicSymbol (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] :
    ℚ_[p]ˣ →* (ZMod m)ˣ :=
  have hprimary : p ^ padicValNat p m ∥ m := by
    simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
      (Nat.isExactDivisor_primePow (N := m) (p := p))
  hprimary.unitsEquivProd.symm.toMonoidHom.comp <|
    (cyclotomicSymbolComponents m p).comp <|
      (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
        (normalizedValuation_padicPrimeUnit p)).toMonoidHom

/-- On a prime-power divisor `p ^ j` of the modulus, the explicit local cyclotomic symbol is the
inverse of the reduction of the p-adic unit part. -/
theorem unitsMap_cyclotomicSymbol_primePow (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] {j : ℕ}
    (hj : p ^ j ∣ m) (x : ℚ_[p]ˣ) (k : ℤ) (w : ℤ_[p]ˣ)
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * ((w : ℤ_[p]) : ℚ_[p])) :
    ZMod.unitsMap hj (cyclotomicSymbol m p x) =
      (Units.map (PadicInt.toZModPow j : ℤ_[p] →+* ZMod (p ^ j)).toMonoidHom w)⁻¹ := by
  have hprimary : p ^ padicValNat p m ∥ m := by
    simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
      (Nat.isExactDivisor_primePow (N := m) (p := p))
  have hjle : j ≤ padicValNat p m :=
    (padicValNat_dvd_iff_le (p := p) (NeZero.ne m)).mp hj
  have hjprimary : p ^ j ∣ p ^ padicValNat p m := pow_dvd_pow p hjle
  have hsplit :
      (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
        (normalizedValuation_padicPrimeUnit p)).toMulEquiv x =
          (.ofAdd k, padicIntegerUnitToFiltration p w) :=
    unitsEquivIntProd_eq_of_padic_decomposition p x k w hx
  have hmap : ZMod.unitsMap hj =
      (ZMod.unitsMap hjprimary).comp (ZMod.unitsMap hprimary.dvd) := by
    simpa using (ZMod.unitsMap_comp hjprimary hprimary.dvd).symm
  rw [hmap, MonoidHom.comp_apply, ← hprimary.unitsEquivProd_apply_fst]
  simp only [cyclotomicSymbol, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    cyclotomicSymbolComponents, MonoidHom.prod_apply, MonoidHom.inv_apply]
  rw [hprimary.unitsEquivProd.apply_symm_apply]
  rw [hsplit]
  simp only [MonoidHom.coe_snd]
  rw [padicUnitReduction_padicIntegerUnitToFiltration, map_inv]
  congr 1
  apply Units.ext
  simp only [ZMod.unitsMap_val, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_ofClass,
    PadicInt.cast_toZModPow j (padicValNat p m) hjle]

/-- On a divisor `d` of the modulus coprime to `p`, the explicit local cyclotomic symbol is
`p ^ k`, where `k` is the normalized valuation. -/
theorem unitsMap_cyclotomicSymbol_of_coprime (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime] {d : ℕ}
    (hd : d ∣ m) (hcop : Nat.Coprime p d) (x : ℚ_[p]ˣ) (k : ℤ) (w : ℤ_[p]ˣ)
    (hx : (x : ℚ_[p]) = (p : ℚ_[p]) ^ k * ((w : ℤ_[p]) : ℚ_[p])) :
    ZMod.unitsMap hd (cyclotomicSymbol m p x) = ZMod.unitOfCoprime p hcop ^ k := by
  have hprimary : p ^ padicValNat p m ∥ m := by
    simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
      (Nat.isExactDivisor_primePow (N := m) (p := p))
  have hcop' : Nat.Coprime (p ^ padicValNat p m) d := hcop.pow_left _
  have hdcomp : d ∣ m / p ^ padicValNat p m :=
    (Nat.dvd_div_iff_mul_dvd hprimary.dvd).mpr
      (hcop'.mul_dvd_of_dvd_of_dvd hprimary.dvd hd)
  have hsplit :
      (unitsEquivIntProd ℚ_[p] (padicPrimeUnit p)
        (normalizedValuation_padicPrimeUnit p)).toMulEquiv x =
          (.ofAdd k, padicIntegerUnitToFiltration p w) :=
    unitsEquivIntProd_eq_of_padic_decomposition p x k w hx
  have hmap : ZMod.unitsMap hd =
      (ZMod.unitsMap hdcomp).comp
        (ZMod.unitsMap (Nat.div_dvd_of_dvd hprimary.dvd)) := by
    simpa using
      (ZMod.unitsMap_comp hdcomp (Nat.div_dvd_of_dvd hprimary.dvd)).symm
  rw [hmap, MonoidHom.comp_apply, ← hprimary.unitsEquivProd_apply_snd]
  simp only [cyclotomicSymbol, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    cyclotomicSymbolComponents, MonoidHom.prod_apply, MonoidHom.inv_apply]
  rw [hprimary.unitsEquivProd.apply_symm_apply, hsplit]
  simp only [MonoidHom.coe_fst, zpowersHom_apply, toAdd_ofAdd]
  rw [map_zpow]
  congr 1
  apply Units.ext
  rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast hdcomp]


/-- Modulo a power of `p` dividing `m`, the symbol at `p` of a `p`-adic unit `w` is `w⁻¹`. -/
theorem unitsMap_cyclotomicSymbol_primePow_of_eq_unit (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    {j : ℕ} (hj : p ^ j ∣ m) {x : ℚ_[p]ˣ} {w : ℤ_[p]ˣ}
    (hx : (x : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p])) :
    ZMod.unitsMap hj (cyclotomicSymbol m p x) =
      (Units.map (PadicInt.toZModPow j : ℤ_[p] →+* ZMod (p ^ j)).toMonoidHom w)⁻¹ :=
  unitsMap_cyclotomicSymbol_primePow m p hj x 0 w (by rw [hx, zpow_zero, one_mul])

/-- Modulo a divisor of `m` prime to `p`, the symbol at `p` of a `p`-adic unit is trivial. -/
theorem unitsMap_cyclotomicSymbol_of_coprime_of_eq_unit (m : ℕ) [NeZero m] (p : ℕ)
    [Fact p.Prime] {d : ℕ} (hd : d ∣ m) (hcop : Nat.Coprime p d) {x : ℚ_[p]ˣ} {w : ℤ_[p]ˣ}
    (hx : (x : ℚ_[p]) = ((w : ℤ_[p]) : ℚ_[p])) :
    ZMod.unitsMap hd (cyclotomicSymbol m p x) = 1 := by
  rw [unitsMap_cyclotomicSymbol_of_coprime m p hd hcop x 0 w (by rw [hx, zpow_zero, one_mul]),
    zpow_zero]

/-- Modulo a power of `p` dividing `m`, the symbol of `p` at `p` is trivial. -/
theorem unitsMap_cyclotomicSymbol_self_primePow (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    {j : ℕ} (hj : p ^ j ∣ m) {x : ℚ_[p]ˣ} (hx : (x : ℚ_[p]) = p) :
    ZMod.unitsMap hj (cyclotomicSymbol m p x) = 1 := by
  rw [unitsMap_cyclotomicSymbol_primePow m p hj x 1 1 (by simp [hx]), map_one, inv_one]

/-- Modulo a divisor of `m` prime to `p`, the symbol of `p` at `p` is the class of `p`. -/
theorem unitsMap_cyclotomicSymbol_self_of_coprime (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    {d : ℕ} (hd : d ∣ m) (hcop : Nat.Coprime p d) {x : ℚ_[p]ˣ} (hx : (x : ℚ_[p]) = p) :
    ZMod.unitsMap hd (cyclotomicSymbol m p x) = ZMod.unitOfCoprime p hcop := by
  rw [unitsMap_cyclotomicSymbol_of_coprime m p hd hcop x 1 1 (by simp [hx]), zpow_one]

/-- At a prime `p` not dividing the modulus, the explicit local cyclotomic symbol is `p` raised to
the `p`-adic valuation. -/
theorem cyclotomicSymbol_of_coprime (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    (hcop : Nat.Coprime p m) (x : ℚ_[p]ˣ) :
    cyclotomicSymbol m p x = ZMod.unitOfCoprime p hcop ^ (x : ℚ_[p]).valuation := by
  obtain ⟨w, hw⟩ := Padic.exists_eq_zpow_valuation_mul x.ne_zero
  simpa [ZMod.unitsMap_self] using
    unitsMap_cyclotomicSymbol_of_coprime m p dvd_rfl hcop x _ w hw

/-- **The explicit local cyclotomic symbol is trivial near `1`**: it kills every unit `x` with
`‖x - 1‖ < ‖m‖`, that is, every unit congruent to `1` modulo a higher power of `p` than the one
dividing `m`. -/
theorem cyclotomicSymbol_eq_one_of_norm_sub_one_lt (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    (x : ℚ_[p]ˣ) (hx : ‖(x : ℚ_[p]) - 1‖ < ‖(m : ℚ_[p])‖) :
    cyclotomicSymbol m p x = 1 := by
  have hm : ‖(m : ℚ_[p])‖ = (p : ℝ) ^ (-(padicValNat p m : ℤ)) := by
    rw [Padic.norm_eq_zpow_neg_valuation (Nat.cast_ne_zero.mpr (NeZero.ne m)),
      Padic.valuation_natCast]
  have hx1 : ‖(x : ℚ_[p])‖ = 1 := by
    have := Padic.norm_eq_of_norm_sub_lt_right (z1 := (x : ℚ_[p])) (z2 := 1)
      (hx.trans_le ((IsUltrametricDist.norm_natCast_le_one ℚ_[p] m).trans_eq norm_one.symm))
    simpa using this
  have hw : (x : ℚ_[p]) = (p : ℚ_[p]) ^ (0 : ℤ) * ((PadicInt.mkUnits hx1 : ℤ_[p]) : ℚ_[p]) := by
    rw [zpow_zero, one_mul, PadicInt.mkUnits_eq]
  have hprimary : p ^ padicValNat p m ∥ m := by
    simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
      (Nat.isExactDivisor_primePow (N := m) (p := p))
  have hcop : Nat.Coprime p (m / p ^ padicValNat p m) := by
    simpa [Nat.factorization_def m (Fact.out : p.Prime)] using
      Nat.coprime_ordCompl (Fact.out : p.Prime) (NeZero.ne m)
  apply hprimary.unitsEquivProd.injective
  rw [map_one]
  refine Prod.ext ?_ ?_
  · rw [Nat.IsExactDivisor.unitsEquivProd_apply_fst,
      unitsMap_cyclotomicSymbol_primePow m p hprimary.dvd x 0 _ hw, Prod.fst_one, inv_eq_one]
    apply Units.ext
    simp only [Units.coe_map, Units.val_one, RingHom.toMonoidHom_eq_coe,
      MonoidHom.coe_ofClass]
    apply PadicInt.toZModPow_eq_one_of_norm_sub_one_le
    rw [PadicInt.norm_def, PadicInt.coe_sub, PadicInt.mkUnits_eq, PadicInt.coe_one, ← hm]
    exact hx.le
  · rw [Nat.IsExactDivisor.unitsEquivProd_apply_snd,
      unitsMap_cyclotomicSymbol_of_coprime m p _ hcop x 0 _ hw, zpow_zero, Prod.snd_one]

/-- **Local constancy of the explicit local cyclotomic symbol**: two units `x` and `x'` with
`‖x - x'‖ < ‖m‖ * ‖x'‖` have the same symbol. -/
theorem cyclotomicSymbol_eq_of_norm_sub_lt (m : ℕ) [NeZero m] (p : ℕ) [Fact p.Prime]
    {x x' : ℚ_[p]ˣ} (hx : ‖(x : ℚ_[p]) - x'‖ < ‖(m : ℚ_[p])‖ * ‖(x' : ℚ_[p])‖) :
    cyclotomicSymbol m p x = cyclotomicSymbol m p x' := by
  have hx' : 0 < ‖(x' : ℚ_[p])‖ := norm_pos_iff.mpr x'.ne_zero
  have hsub : (x : ℚ_[p]) * ((x'⁻¹ : ℚ_[p]ˣ) : ℚ_[p]) - 1 =
      ((x : ℚ_[p]) - x') * (x' : ℚ_[p])⁻¹ := by
    rw [Units.val_inv_eq_inv_val, sub_mul, mul_inv_cancel₀ x'.ne_zero]
  have h := cyclotomicSymbol_eq_one_of_norm_sub_one_lt m p (x * x'⁻¹) (by
    rw [Units.val_mul, hsub, norm_mul, norm_inv, ← div_eq_mul_inv, div_lt_iff₀ hx']
    exact hx)
  rw [map_mul, map_inv, mul_inv_eq_one] at h
  exact h

/-- **The explicit symbol of `ℚ(μ_m)/ℚ` at the real place.** It is the sign of a real unit,
viewed as the unit `1` or `-1` modulo `m`. -/
def realCyclotomicSymbol (m : ℕ) : ℝˣ →* (ZMod m)ˣ :=
  (Units.map (Int.castRingHom (ZMod m)).toMonoidHom).comp <|
    (Units.signEquiv ℝ).toMonoidHom.comp (QuotientGroup.mk' (Units.posSubgroup ℝ))

/-- The real cyclotomic symbol of a positive number is `1`. -/
@[simp]
theorem realCyclotomicSymbol_of_pos (m : ℕ) (x : ℝˣ) (hx : 0 < (x : ℝ)) :
    realCyclotomicSymbol m x = 1 := by
  have hs : Units.signEquiv ℝ (QuotientGroup.mk x) = 1 :=
    (Units.signEquiv_mk_eq_one_iff x).mpr hx
  simp [realCyclotomicSymbol, hs]

/-- The real cyclotomic symbol of a negative number is `-1`. -/
@[simp]
theorem realCyclotomicSymbol_of_neg (m : ℕ) (x : ℝˣ) (hx : (x : ℝ) < 0) :
    realCyclotomicSymbol m x = -1 := by
  have hs : Units.signEquiv ℝ (QuotientGroup.mk x) = -1 :=
    (Units.signEquiv_mk_eq_neg_one_iff x).mpr hx
  simpa [realCyclotomicSymbol] using
    congrArg (Units.map (Int.castRingHom (ZMod m)).toMonoidHom) hs

end TauCeti
