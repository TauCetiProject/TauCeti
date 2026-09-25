/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import Mathlib.NumberTheory.Padics.LocalField
import Mathlib.NumberTheory.LegendreSymbol.Basic
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.PowerSubgroup

/-!
# Normalization of the p-adic absolute value

These comparison lemmas let the generic normalized-valuation API interoperate with Mathlib's
concrete p-adic norm and valuation APIs.

## Main results

* `Padic.toAdd_normalizedValuation_eq_valuation` identifies the additive normalized
  valuation with `Padic.valuation`.
* `Padic.natCard_residueField` computes the residue-field cardinality of `ℚ_[p]`.
* `Padic.normalizedAbsoluteValue_eq_nnnorm` identifies the normalized absolute value with
  Mathlib's norm on `ℚ_[p]`.
* `Padic.natCastValuation_eq_padicValNat` identifies the normalized valuation of a natural
  number with `padicValNat`, and `Padic.natCastValuation_self` and
  `Padic.natCastValuation_two` are the two values it takes on the residue prime and on `2`.
* `Padic.not_isSquare_neg_one_of_mod_four_eq_three`: `-1` is nonsquare in `ℚ_[p]` when
  `p ≡ 3 (mod 4)`.

The Padic and residue-field constructions used here are part of Mathlib's upstream
`NumberTheory/Padics` development.
-/

public section

open ValuativeRel IsNonarchimedeanLocalField
open scoped WithZero

variable (p : ℕ) [Fact p.Prime]

namespace Padic

/-- The zero-preserving normalized valuation on `ℚ_[p]` is the inverse of
Mathlib's p-adic valuation. -/
@[simp]
theorem normalizedValuationWithZero_eq_inv_mulValuation (x : ℚ_[p]) :
    TauCeti.normalizedValuationWithZero ℚ_[p] x = (Padic.mulValuation x)⁻¹ := by
  refine Valuation.normalizedValuationWithZero_eq_inv_of_surjective _ (fun z ↦ ?_) x
  obtain ⟨q, hq⟩ := Rat.surjective_padicValuation p z
  exact ⟨q, by simpa [← Padic.comap_mulValuation_eq_padicValuation] using hq⟩

/-- The additive normalized valuation on `ℚ_[p]` is Mathlib's p-adic valuation. -/
@[simp]
theorem toAdd_normalizedValuation_eq_valuation (x : ℚ_[p]ˣ) :
    (TauCeti.normalizedValuation ℚ_[p] x).toAdd = (x : ℚ_[p]).valuation := by
  have h := normalizedValuationWithZero_eq_inv_mulValuation p (x : ℚ_[p])
  rw [TauCeti.normalizedValuationWithZero_coe] at h
  have hcoe (a : Multiplicative ℤ) : (a : ℤᵐ⁰) = WithZero.exp a.toAdd := by
    rw [WithZero.exp_eq_coe_ofAdd, ofAdd_toAdd]
  rw [hcoe, Padic.mulValuation_toFun, ite_eq_right x.ne_zero, ← WithZero.exp_neg, neg_neg] at h
  exact WithZero.exp_injective h

/-- The residue field of `ℚ_[p]` has cardinality `p`. -/
@[simp high] -- Compute the cardinality before `Nat.card_eq_fintype_card` changes its form.
theorem natCard_residueField :
    Nat.card 𝓀[ℚ_[p]] = p := by
  rw [@Nat.card_eq_fintype_card _ (Fintype.ofFinite 𝓀[ℚ_[p]])]
  have h : 𝒪[ℚ_[p]] = PadicInt.subring p := by
    ext x
    rw [Valuation.mem_integer_iff, PadicInt.mem_subring_iff]
    rw [(ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
    simpa using (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt
      (x := (1 : ℚ_[p])) (y := x))).symm
  let e : 𝒪[ℚ_[p]] ≃+* ℤ_[p] := RingEquiv.subringCongr h
  rw [@Fintype.card_congr _ _ (Fintype.ofFinite 𝓀[ℚ_[p]]) inferInstance
    ((IsLocalRing.ResidueField.mapEquiv e).trans PadicInt.residueField).toEquiv, ZMod.card]

/-- The normalized absolute value on `ℚ_[p]` agrees with Mathlib's norm. -/
@[simp]
theorem normalizedAbsoluteValue_eq_nnnorm (x : ℚ_[p]) :
    TauCeti.normalizedAbsoluteValue ℚ_[p] x = ‖x‖₊ := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  apply NNReal.eq
  rw [TauCeti.normalizedAbsoluteValue_apply_ne_zero x hx,
    natCard_residueField p, toAdd_normalizedValuation_eq_valuation]
  simp only [coe_nnnorm]
  simpa using (Padic.norm_eq_zpow_neg_valuation hx).symm

/-- The normalized valuation of a natural number in `ℚ_[p]` is its `p`-adic valuation. -/
@[simp]
theorem natCastValuation_eq_padicValNat (n : ℕ) (hn : (n : ℚ_[p]) ≠ 0) :
    TauCeti.natCastValuation ℚ_[p] n hn = padicValNat p n := by
  have h : ((TauCeti.natCastValuation ℚ_[p] n hn : ℕ) : ℤ) = padicValNat p n := by
    rw [← toAdd_ofAdd ((TauCeti.natCastValuation ℚ_[p] n hn : ℕ) : ℤ),
      ← TauCeti.normalizedValuation_natCast ℚ_[p] n hn,
      toAdd_normalizedValuation_eq_valuation]
    simp
  exact_mod_cast h

/-- The normalized valuation of the residue prime `p` in `ℚ_[p]` is `1`; equivalently, `ℚ_[p]`
is absolutely unramified. -/
theorem natCastValuation_self :
    TauCeti.natCastValuation ℚ_[p] p (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) = 1 := by
  rw [natCastValuation_eq_padicValNat, padicValNat.self (Fact.out : p.Prime).one_lt]

/-- The normalized valuation of `2` in `ℚ_[p]` vanishes for every odd `p`. -/
theorem natCastValuation_two (hp : p ≠ 2) :
    TauCeti.natCastValuation ℚ_[p] 2 (Nat.cast_ne_zero.mpr two_ne_zero) = 0 := by
  rw [natCastValuation_eq_padicValNat]
  exact padicValNat.eq_zero_of_not_dvd fun h ↦
    hp ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h)

/-- If `p ≡ 3 (mod 4)`, then `-1` is not a square in `ℚ_[p]`. Combined with
`TauCeti.anisotropic_binary_one_one_iff`, this shows that the binary form `⟨1, 1⟩` is anisotropic
over `ℚ_[p]` for such primes. -/
theorem not_isSquare_neg_one_of_mod_four_eq_three (hp : p % 4 = 3) :
    ¬ IsSquare (-1 : ℚ_[p]) := by
  intro hs0
  have hs : IsSquare (-1 : ℚ_[p]ˣ) := TauCeti.isSquare_units_val_iff.mp hs0
  have h2 : IsUnit (2 : 𝒪[ℚ_[p]]) :=
    (TauCeti.natCastValuation_eq_zero_iff (K := ℚ_[p]) 2 (by norm_num)).mp
      (natCastValuation_two p (by omega))
  have hsres : IsSquare (-1 : 𝓀[ℚ_[p]]ˣ) := by
    have h := (TauCeti.isSquare_unitsMap_subtype_iff h2 (-1 : 𝒪[ℚ_[p]]ˣ)).mp
    exact (by simpa using h (by simpa using hs))
  have hs' : IsSquare (-1 : 𝓀[ℚ_[p]]) :=
    TauCeti.isSquare_units_val_iff.mpr hsres
  let : Fintype 𝓀[ℚ_[p]] := Fintype.ofFinite _
  have hcard : Fintype.card 𝓀[ℚ_[p]] = p := by
    simpa only [Nat.card_eq_fintype_card] using natCard_residueField p
  exact ((FiniteField.isSquare_neg_one_iff).mp hs') (by simpa [hcard] using hp)

end Padic
