/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicIntegers
public import TauCeti.NumberTheory.LocalField.NatCastValuation
public import Mathlib.NumberTheory.Padics.LocalField
public import TauCeti.NumberTheory.LocalField.Uniformizer
import Mathlib.Algebra.Polynomial.SpecificDegree
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import TauCeti.Algebra.Group.Units.Basic
import TauCeti.NumberTheory.LocalField.PowerSubgroup.Basic

/-!
# Normalization of the p-adic absolute value

These comparison lemmas let the generic normalized-valuation API interoperate with Mathlib's
concrete p-adic norm and valuation APIs.

## Main results

* `Padic.toAdd_normalizedValuation_eq_valuation` identifies the additive normalized
  valuation with `Padic.valuation`.
* `Padic.integerRingEquiv` identifies the ring of integers of `ℚ_[p]` with `ℤ_[p]`.
* `Padic.natCard_residueField` computes the residue-field cardinality of `ℚ_[p]`.
* `Padic.normalizedAbsoluteValue_eq_nnnorm` identifies the normalized absolute value with
  Mathlib's norm on `ℚ_[p]`.
* `Padic.natCastValuation_eq_padicValNat` identifies the normalized valuation of a natural
  number with `padicValNat`, and `Padic.natCastValuation_self` and
  `Padic.natCastValuation_two` are the two values it takes on the residue prime and on `2`.
* `TauCeti.Padic.irreducible_natCast_self` shows that the residue prime is a uniformizer of
  the integer ring, and `TauCeti.Padic.isUniformizer_natCast_self` that it is a uniformizer of
  `ℚ_[p]`.
* `Padic.not_isSquare_neg_one_of_mod_four_eq_three`: `-1` is nonsquare in `ℚ_[p]` when
  `p ≡ 3 (mod 4)`.
* `Padic.not_isSquare_intCast_of_not_isSquare_zmod`: an integer that is not a square modulo a
  power of `p` is not a square in `ℚ_[p]`; `Padic.not_isSquare_five` (`5` in `ℚ_[2]`) and
  `Padic.not_isSquare_neg_three` (`-3` in `ℚ_[5]`) are its two instances.
* `Padic.irreducible_X_sq_add_X_add_one`: `X² + X + 1` is irreducible over `ℚ_[5]`.

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

/-- The ring of integers of `ℚ_[p]` for its valuative relation is Mathlib's subring of elements
of norm at most `1`. -/
theorem integerRing_eq_subring : 𝒪[ℚ_[p]] = PadicInt.subring p := by
  ext x
  rw [Valuation.mem_integer_iff, PadicInt.mem_subring_iff]
  rw [(ValuativeRel.isEquiv (ValuativeRel.valuation ℚ_[p]) Padic.mulValuation).le_one_iff_le_one]
  simpa using (not_congr (Padic.norm_lt_norm_iff_mulValuation_lt
    (x := (1 : ℚ_[p])) (y := x))).symm

/-- The ring of integers of `ℚ_[p]` for its valuative relation is `ℤ_[p]`. -/
noncomputable def integerRingEquiv : 𝒪[ℚ_[p]] ≃+* ℤ_[p] :=
  RingEquiv.subringCongr (integerRing_eq_subring p)

/-- The identification of the ring of integers of `ℚ_[p]` with `ℤ_[p]` is the identity on the
underlying `p`-adic numbers. -/
@[simp]
theorem coe_integerRingEquiv_apply (x : 𝒪[ℚ_[p]]) : ((integerRingEquiv p x : ℤ_[p]) : ℚ_[p]) = x :=
  (rfl)

/-- The inverse identification of `ℤ_[p]` with the ring of integers of `ℚ_[p]` is the identity on
the underlying `p`-adic numbers. -/
@[simp]
theorem coe_integerRingEquiv_symm_apply (x : ℤ_[p]) :
    (((integerRingEquiv p).symm x : 𝒪[ℚ_[p]]) : ℚ_[p]) = x :=
  (rfl)

/-- The residue field of `ℚ_[p]` has cardinality `p`. -/
@[simp high] -- Compute the cardinality before `Nat.card_eq_fintype_card` changes its form.
theorem natCard_residueField :
    Nat.card 𝓀[ℚ_[p]] = p := by
  rw [@Nat.card_eq_fintype_card _ (Fintype.ofFinite 𝓀[ℚ_[p]])]
  rw [@Fintype.card_congr _ _ (Fintype.ofFinite 𝓀[ℚ_[p]]) inferInstance
    ((IsLocalRing.ResidueField.mapEquiv (integerRingEquiv p)).trans
      PadicInt.residueField).toEquiv, ZMod.card]

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

variable {p} in
/-- A square root in `ℚ_[p]` of an integer is a `p`-adic integer, so an integer that is not a
square modulo some power of `p` is not a square in `ℚ_[p]`. -/
theorem not_isSquare_intCast_of_not_isSquare_zmod {a : ℤ} {k : ℕ}
    (h : ¬ IsSquare (a : ZMod (p ^ k))) : ¬ IsSquare (a : ℚ_[p]) := by
  rintro ⟨b, hb⟩
  have hb1 : ‖b‖ ≤ 1 := by
    have : ‖b‖ * ‖b‖ ≤ 1 := by rw [← norm_mul, ← hb]; exact norm_int_le_one a
    nlinarith [norm_nonneg b]
  obtain ⟨c, rfl⟩ : ∃ c : ℤ_[p], (c : ℚ_[p]) = b := ⟨⟨b, hb1⟩, rfl⟩
  have hc : c * c = a := PadicInt.ext (by push_cast; exact hb.symm)
  exact h ⟨PadicInt.toZModPow k c, by rw [← map_mul, hc, map_intCast]⟩

/-- `5` is not a square in `ℚ_[2]`, since no square is `5` modulo `8`. -/
theorem not_isSquare_five : ¬IsSquare (5 : ℚ_[2]) := by
  have h := not_isSquare_intCast_of_not_isSquare_zmod (p := 2) (a := 5) (k := 3)
    (by rintro ⟨x, hx⟩; revert x hx; decide)
  simpa using h

/-- The prime `5`, as a `Fact`, so that `ℚ_[5]` can be written. -/
local instance factPrimeFive : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-- `-3` is not a square in `ℚ_[5]`, since its residue `2` is not a square modulo `5`. -/
theorem not_isSquare_neg_three : ¬ IsSquare (-3 : ℚ_[5]) := by
  have h := not_isSquare_intCast_of_not_isSquare_zmod (p := 5) (a := -3) (k := 1)
    (by rintro ⟨x, hx⟩; revert x hx; decide)
  simpa using h

open Polynomial in
/-- `X² + X + 1` is irreducible over `ℚ_[5]`: a root `r` would make `(2r + 1)² = −3` a square. -/
theorem irreducible_X_sq_add_X_add_one : Irreducible (X ^ 2 + X + 1 : ℚ_[5][X]) := by
  have hdeg : (X ^ 2 + X + 1 : ℚ_[5][X]).natDegree = 2 := by compute_degree!
  have hmonic : (X ^ 2 + X + 1 : ℚ_[5][X]).Monic := by monicity!
  rw [hmonic.irreducible_iff_roots_eq_zero_of_degree_le_three (by omega) (by omega),
    Multiset.eq_zero_iff_forall_notMem]
  intro r hr
  rw [mem_roots hmonic.ne_zero, IsRoot, eval_add, eval_add, eval_pow, eval_X, eval_one] at hr
  exact not_isSquare_neg_three ⟨2 * r + 1, by linear_combination (-4 : ℚ_[5]) * hr⟩

end Padic

namespace TauCeti.Padic

/-- The residue prime `p` is a uniformizer of the integer ring of `ℚ_[p]`. -/
theorem irreducible_natCast_self : Irreducible (p : 𝒪[ℚ_[p]]) := by
  simpa only [map_natCast] using
    (PadicInt.irreducible_p (p := p)).map (_root_.Padic.integerRingEquiv p).symm

/-- The residue prime `p` is a uniformizer of `ℚ_[p]`. -/
theorem isUniformizer_natCast_self :
    IsUniformizer ℚ_[p]
      (Units.mk0 (p : ℚ_[p]) (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)) := by
  rw [isUniformizer_def]
  apply Multiplicative.toAdd.injective
  rw [_root_.Padic.toAdd_normalizedValuation_eq_valuation, Units.val_mk0, _root_.Padic.valuation_p,
    toAdd_ofAdd]

end TauCeti.Padic
