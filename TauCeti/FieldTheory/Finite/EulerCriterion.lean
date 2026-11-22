/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Norm.Defs
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.FieldTheory.Finite.GaloisField
import TauCeti.FieldTheory.Finite.Card
import TauCeti.GroupTheory.SpecificGroups.Cyclic.PowMonoidHom

/-!
# Euler's criterion for `n`-th powers in a finite field

Let `F` be a finite field with `q` elements and `n ∣ q - 1`. A nonzero `a ∈ F` is an `n`-th power
exactly when `a ^ ((q - 1) / n) = 1`. At `n = 2` this is Mathlib's `FiniteField.isSquare_iff`
(in odd characteristic).

In a finite extension `F'/F` of finite fields of degree `d = [F' : F]`, the Euler exponent
factors as `(#F' - 1) / n = ((q - 1) / n) * ((#F' - 1) / (q - 1))`. Since raising to the power
`(#F' - 1) / (q - 1)` is the field norm `Algebra.norm F` (`FiniteField.algebraMap_norm_eq_pow`),
whose restriction to `F` is the `d`-th power map (`Algebra.norm_algebraMap`), we obtain
`a ^ ((#F' - 1) / n) = (a ^ ((q - 1) / n)) ^ d` in `F'`. For a prime `p`, an element `a ∈ F`
therefore becomes a `p`-th power in `F'` if and only if either `a` is already a `p`-th power in `F`
or `p ∣ [F' : F]`. At `p = 2` this gives the squareness criterion: `r ∈ F` is a square in `F'` if
and only if `r` is a square in `F` or `[F' : F]` is even (in all characteristics, including
characteristic two where every element is already a square).

## Main results

* `TauCeti.FiniteField.exists_pow_eq_iff_pow_card_sub_one_div_eq_one`: Euler's criterion for
  `n`-th powers in a finite field.
* `TauCeti.FiniteField.pow_card_div_two_eq_neg_one`: a nonsquare `r` satisfies
  `r ^ (#F / 2) = -1`.
* `TauCeti.FiniteField.algebraMap_pow_card_sub_one_div`: for `n ∣ #F - 1`, raising `a ∈ F` to the
  Euler exponent `(#F' - 1) / n` in a finite extension `F'/F` agrees with raising
  `a ^ ((#F - 1) / n)` to the extension degree `[F' : F]`.
* `TauCeti.FiniteField.exists_pow_eq_algebraMap_iff_pow_finrank_eq_one`: Euler's criterion in a
  finite field extension.
* `TauCeti.FiniteField.norm_eq_one_iff_exists_pow_eq`: in a finite extension `F'/F`, the nonzero
  elements of norm `1` are exactly the `(#F - 1)`-th powers (Hilbert's Theorem 90 for finite
  fields).
* `TauCeti.FiniteField.exists_pow_eq_algebraMap_iff`: for a prime `p`, `a ∈ F` is a `p`-th power
  in `F'` if and only if `a` is a `p`-th power in `F` or `p ∣ [F' : F]`.
* `TauCeti.FiniteField.isSquare_algebraMap_iff` and
  `TauCeti.FiniteField.not_isSquare_algebraMap_iff`: `r ∈ F` is a square in `F'` if and only if
  `r` is a square in `F` or `[F' : F]` is even.
-/

public section

namespace TauCeti.FiniteField

/-- **Euler's criterion in a finite field.** If `n ∣ #F - 1`, then a nonzero `a ∈ F` is an `n`-th
power exactly when `a ^ ((#F - 1) / n) = 1`. -/
theorem exists_pow_eq_iff_pow_card_sub_one_div_eq_one {F : Type*} [Field F] [Finite F] {n : ℕ}
    (hn : n ∣ Nat.card F - 1) {a : F} (ha : a ≠ 0) :
    (∃ b, b ^ n = a) ↔ a ^ ((Nat.card F - 1) / n) = 1 := by
  have hcard : Nat.card Fˣ = Nat.card F - 1 := Nat.card_units _
  have hn0 : n ≠ 0 := by
    rintro rfl
    have := Finite.one_lt_card (α := F)
    have := Nat.eq_zero_of_zero_dvd hn
    omega
  -- Euler's criterion in the cyclic group `Fˣ` of order `#F - 1`.
  have h := IsCyclic.mem_range_powMonoidHom_iff n (Units.mk0 _ ha)
  rw [hcard, Nat.gcd_eq_right hn, ← Units.val_eq_one, Units.val_pow_eq_pow_val, Units.val_mk0] at h
  rw [← h]
  constructor
  · rintro ⟨b, hb⟩
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact ha (by rw [← hb, zero_pow hn0])
    exact ⟨Units.mk0 b hb0, Units.ext (by simp [hb])⟩
  · rintro ⟨b, hb⟩
    exact ⟨b, by simpa using congrArg Units.val hb⟩

/-- **Euler's criterion for a nonsquare.** In a finite field `F`, a nonsquare `r` satisfies
`r ^ (#F / 2) = -1`. -/
theorem pow_card_div_two_eq_neg_one {F : Type*} [Field F] [Finite F] {r : F}
    (hr : ¬IsSquare r) : r ^ (Nat.card F / 2) = -1 := by
  have := Fintype.ofFinite F
  have hF := ringChar_ne_two_of_odd_card (odd_card_of_not_isSquare hr)
  have hr0 : r ≠ 0 := by rintro rfl; exact hr .zero
  rw [Nat.card_eq_fintype_card]
  exact (FiniteField.pow_dichotomy hF hr0).resolve_left
    fun h ↦ hr ((FiniteField.isSquare_iff hF hr0).mpr h)

/-! ### Powers and squares in finite field extensions -/

section Extension

variable {F F' : Type*} [Field F] [Field F'] [Finite F'] [Algebra F F']

/-- In a finite extension `F'/F` of finite fields with `n ∣ #F - 1`, raising `a ∈ F` to the Euler
exponent `(#F' - 1) / n` in `F'` agrees with raising `a ^ ((#F - 1) / n)` to the extension degree
`[F' : F]`. -/
theorem algebraMap_pow_card_sub_one_div {n : ℕ} (hn : n ∣ Nat.card F - 1) (a : F) :
    algebraMap F F' a ^ ((Nat.card F' - 1) / n) =
      algebraMap F F' ((a ^ ((Nat.card F - 1) / n)) ^ Module.finrank F F') := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hq : Nat.card F - 1 ∣ Nat.card F' - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := F')]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  have hdiv : (Nat.card F' - 1) / n =
      (Nat.card F - 1) / n * ((Nat.card F' - 1) / (Nat.card F - 1)) := by
    rw [Nat.div_mul_right_comm hn, Nat.mul_div_cancel' hq]
  rw [hdiv, pow_mul, ← map_pow, ← FiniteField.algebraMap_norm_eq_pow, Algebra.norm_algebraMap]

/-- **Euler's criterion in a finite field extension.** If `n ∣ #F - 1`, then a nonzero element
`a ∈ F` becomes an `n`-th power in a finite extension `F'/F` exactly when
`(a ^ ((#F - 1) / n)) ^ [F' : F] = 1`. -/
theorem exists_pow_eq_algebraMap_iff_pow_finrank_eq_one {n : ℕ} (hn : n ∣ Nat.card F - 1)
    {a : F} (ha : a ≠ 0) :
    (∃ b : F', b ^ n = algebraMap F F' a) ↔
      (a ^ ((Nat.card F - 1) / n)) ^ Module.finrank F F' = 1 := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hn' : n ∣ Nat.card F' - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := F')]
    exact dvd_trans hn (Nat.sub_one_dvd_pow_sub_one _ _)
  rw [exists_pow_eq_iff_pow_card_sub_one_div_eq_one hn'
      ((map_ne_zero_iff _ (algebraMap F F').injective).mpr ha),
    algebraMap_pow_card_sub_one_div hn, map_eq_one_iff _ (algebraMap F F').injective]

/-- **Norm-one elements of a finite field extension.** In a finite extension `F'/F` of finite
fields, a nonzero `a ∈ F'` has norm `1` exactly when it is a `(#F - 1)`-th power. Since
`b ^ (#F - 1) = b ^ #F / b` is the quotient of the Frobenius image of `b` by `b`, this is
Hilbert's Theorem 90 for the cyclic extension `F'/F`; it is Euler's criterion in `F'` at the
exponent `#F - 1`, raising to the power `(#F' - 1) / (#F - 1)` being the norm. -/
theorem norm_eq_one_iff_exists_pow_eq {a : F'} (ha : a ≠ 0) :
    Algebra.norm F a = 1 ↔ ∃ b : F', b ^ (Nat.card F - 1) = a := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Module.Finite F F' := .of_finite
  have hq : Nat.card F - 1 ∣ Nat.card F' - 1 := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := F')]
    exact Nat.sub_one_dvd_pow_sub_one _ _
  rw [exists_pow_eq_iff_pow_card_sub_one_div_eq_one hq ha, ← FiniteField.algebraMap_norm_eq_pow,
    map_eq_one_iff _ (algebraMap F F').injective]

/-- **Criterion for `p`-th powers in a finite field extension.** For a prime `p`, an element
`a ∈ F` becomes a `p`-th power in a finite extension `F'/F` of finite fields if and only if either
`a` is already a `p`-th power in `F` or `p` divides the extension degree `[F' : F]`. -/
theorem exists_pow_eq_algebraMap_iff {p : ℕ} (hp : p.Prime) {a : F} :
    (∃ b : F', b ^ p = algebraMap F F' a) ↔
      (∃ b : F, b ^ p = a) ∨ p ∣ Module.finrank F F' := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  rcases eq_or_ne a 0 with rfl | ha
  · exact iff_of_true ⟨0, by simp [zero_pow hp.ne_zero]⟩ (.inl ⟨0, zero_pow hp.ne_zero⟩)
  by_cases hpq : p ∣ Nat.card F - 1
  · rw [exists_pow_eq_algebraMap_iff_pow_finrank_eq_one hpq ha,
      exists_pow_eq_iff_pow_card_sub_one_div_eq_one hpq ha]
    set ζ := a ^ ((Nat.card F - 1) / p)
    by_cases hζ : ζ = 1
    · simp [hζ]
    · have := Fintype.ofFinite F
      have hζp : ζ ^ p = 1 := by
        rw [← pow_mul, Nat.div_mul_cancel hpq]
        simpa [Nat.card_eq_fintype_card] using FiniteField.pow_card_sub_one_eq_one a ha
      let : Fact p.Prime := ⟨hp⟩
      have hord : orderOf ζ = p := orderOf_eq_prime hζp hζ
      rw [← orderOf_dvd_iff_pow_eq_one, hord, iff_false_intro hζ, false_or]
  · have hcop : (Nat.card Fˣ).Coprime p := by
      rw [Nat.card_units]
      exact (hp.coprime_iff_not_dvd.mpr hpq).symm
    obtain ⟨u, hu⟩ := hcop.pow_left_bijective.surjective (Units.mk0 a ha)
    have hb : (u : F) ^ p = a := by simpa using congrArg Units.val hu
    exact iff_of_true ⟨algebraMap F F' u, by rw [← map_pow, hb]⟩ (.inl ⟨u, hb⟩)

/-- **Squares in a finite field extension.** An element `r ∈ F` becomes a square in a finite
extension `F'/F` of finite fields if and only if either `r` is already a square in `F` or the
extension degree `[F' : F]` is even. -/
theorem isSquare_algebraMap_iff {r : F} :
    IsSquare (algebraMap F F' r) ↔ IsSquare r ∨ Even (Module.finrank F F') := by
  simpa only [isSquare_iff_exists_sq, even_iff_two_dvd, eq_comm] using
    exists_pow_eq_algebraMap_iff (F' := F') Nat.prime_two (a := r)

/-- An element `r ∈ F` stays a nonsquare in a finite extension `F'/F` of finite fields if and only
if `r` is not a square in `F` and the extension degree `[F' : F]` is odd. -/
theorem not_isSquare_algebraMap_iff {r : F} :
    ¬IsSquare (algebraMap F F' r) ↔ ¬IsSquare r ∧ Odd (Module.finrank F F') := by
  rw [isSquare_algebraMap_iff, not_or, Nat.not_even_iff_odd]

end Extension

end TauCeti.FiniteField
