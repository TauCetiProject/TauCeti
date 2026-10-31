/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Generalized Bernoulli numbers

This file defines the generalized Bernoulli numbers attached to a Dirichlet character. For a
character `χ` modulo `N`, the definition is

`Bₙ,χ = Nⁿ⁻¹ ∑ a : ZMod N, χ a * Bₙ(ã / N)`,

where `Bₙ(X)` is the `n`-th Bernoulli polynomial and `ã` is the representative of `a` in
`{1, …, N}` (so the zero residue is represented by `N`). The power of `N` is taken in `ℚ`
before mapping to the coefficient ring. In particular, the definition has the intended factor
`N⁻¹` also when `n = 0`.

The first two degrees are reduced to ordinary character sums. These forms supply the constant
terms used in Eisenstein series with character.

## Main definitions

* `DirichletCharacter.generalizedBernoulli` is the generalized Bernoulli number `Bₙ,χ`.

## Main results

* `DirichletCharacter.generalizedBernoulli_def` is the defining finite-sum formula, which the
  unexposed definition body does not otherwise make available to downstream files.
* `DirichletCharacter.map_generalizedBernoulli` shows compatibility with extension of scalars.
* `DirichletCharacter.generalizedBernoulli_modOne` recovers the positive-first-convention
  Bernoulli numbers at modulus one.
* `DirichletCharacter.generalizedBernoulli_zero` and
  `DirichletCharacter.generalizedBernoulli_one` reduce the first two degrees to character sums.
* `DirichletCharacter.generalizedBernoulli_zero_of_ne_one` gives `B₀,χ = 0` for a nontrivial
  character, while `DirichletCharacter.generalizedBernoulli_zero_one` evaluates the trivial one.
* `DirichletCharacter.generalizedBernoulli_one_of_ne_one` and
  `DirichletCharacter.natCast_mul_generalizedBernoulli_one_of_ne_one` give the two useful forms
  of `B₁,χ` for a nontrivial character.
* `DirichletCharacter.generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg` gives `Bₖ,χ = 0` when
  `k ≠ 1` and the parities of `χ` and `k` differ.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, equation (4.1).

## Provenance

The definition and the degree-zero and degree-one calculations are adapted from the AINTLIB
`FltRegularBernoulli` project (Chris Birkbeck, `github.com/CBirkbeck/AINTLIB`, Apache-2.0), commit
`112d12d95e9c19f0d477b7a687bd49563ab8d07d`, file
`projects/FltRegularBernoulli/BernoulliRegular/BernoulliGeneralized.lean`, declarations
`BernoulliGen`, `BernoulliGen_zero_of_ne_one`, `BernoulliGen_one_of_ne_one`, and
`natCast_mul_BernoulliGen_one_of_ne_one`. This version uses an integer power in `ℚ`, so the
defining formula remains literal in degree zero, and adds scalar compatibility and the
modulus-one calculation.
-/

public section

noncomputable section

open Polynomial

namespace DirichletCharacter

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Bernoulli number `Bₙ,χ` attached to a Dirichlet character `χ` modulo `N`:

`Bₙ,χ = Nⁿ⁻¹ ∑ a : ZMod N, χ a * Bₙ(ã / N)`, where `ã` is the representative
of `a` in `{1, …, N}`.

The scalar `Nⁿ⁻¹` is formed in `ℚ`; this avoids imposing a field structure on the coefficient
ring while retaining the inverse factor in degree zero. -/
def generalizedBernoulli [NeZero N] (χ : DirichletCharacter R N) (n : ℕ) : R :=
  algebraMap ℚ R ((N : ℚ) ^ ((n : ℤ) - 1)) *
    ∑ a : ZMod N, χ a *
      algebraMap ℚ R
        ((Polynomial.bernoulli n).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N))

/-- The defining finite-sum formula for `Bₙ,χ`.

The body of `DirichletCharacter.generalizedBernoulli` is not exposed, so this is the public
characterization of generalized Bernoulli numbers in arbitrary degree. -/
theorem generalizedBernoulli_def [NeZero N] (χ : DirichletCharacter R N) (n : ℕ) :
    χ.generalizedBernoulli n =
      algebraMap ℚ R ((N : ℚ) ^ ((n : ℤ) - 1)) *
        ∑ a : ZMod N, χ a *
          algebraMap ℚ R
            ((Polynomial.bernoulli n).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N)) := by
  rw [generalizedBernoulli]

/-- Generalized Bernoulli numbers commute with extension of the coefficient ring. -/
@[simp]
theorem map_generalizedBernoulli [NeZero N] {S : Type*} [CommRing S] [Algebra ℚ S]
    (χ : DirichletCharacter R N) (f : R →ₐ[ℚ] S) (n : ℕ) :
    f (χ.generalizedBernoulli n) =
      generalizedBernoulli (χ.ringHomComp (f : R →+* S) : DirichletCharacter S N) n := by
  simp only [generalizedBernoulli, map_mul, AlgHom.commutes, map_sum, MulChar.ringHomComp_apply,
    RingHom.coe_coe]

/-- At modulus one, generalized Bernoulli numbers are the images of the positive-first-convention
Bernoulli numbers. Thus degree one is `1 / 2`; in every other degree this agrees with Mathlib's
`bernoulli`. -/
@[simp]
theorem generalizedBernoulli_modOne (χ : DirichletCharacter R 1) (n : ℕ) :
    χ.generalizedBernoulli n = algebraMap ℚ R (_root_.bernoulli' n) := by
  rw [χ.level_one, generalizedBernoulli]
  rw [← Finset.singleton_eq_univ (0 : ZMod 1), Finset.sum_singleton]
  have hzero : (0 : ZMod 1) = 1 := Subsingleton.elim _ _
  have hchar : (1 : DirichletCharacter R 1) (0 : ZMod 1) = 1 := by
    rw [hzero, map_one]
  rw [hchar, one_mul]
  simp [Polynomial.bernoulli_eval_one]

/-- The zeroth generalized Bernoulli number is `N⁻¹` times the sum of the character values. -/
theorem generalizedBernoulli_zero [NeZero N] (χ : DirichletCharacter R N) :
    χ.generalizedBernoulli 0 =
      algebraMap ℚ R (N : ℚ)⁻¹ * ∑ a : ZMod N, χ a := by
  rw [generalizedBernoulli]
  norm_num [Polynomial.bernoulli_zero]

/-- The zeroth generalized Bernoulli number of a nontrivial character is zero. -/
@[simp]
theorem generalizedBernoulli_zero_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) : χ.generalizedBernoulli 0 = 0 := by
  rw [generalizedBernoulli_zero, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

/-- The zeroth generalized Bernoulli number of the trivial character is `N⁻¹` times the number
of units modulo `N`. -/
@[simp]
theorem generalizedBernoulli_zero_one [NeZero N] :
    (1 : DirichletCharacter R N).generalizedBernoulli 0 =
      algebraMap ℚ R (N : ℚ)⁻¹ * (Nat.totient N : R) := by
  rw [generalizedBernoulli_zero, MulChar.sum_one_eq_card_units,
    ZMod.card_units_eq_totient]

/-- The first generalized Bernoulli number is a difference of two character sums, obtained from
`B₁(X) = X - 1 / 2`. -/
theorem generalizedBernoulli_one [NeZero N] (χ : DirichletCharacter R N) :
    χ.generalizedBernoulli 1 =
      (∑ a : ZMod N, χ a *
        algebraMap ℚ R (((if a = 0 then N else a.val : ℕ) : ℚ) / N)) -
        algebraMap ℚ R (2⁻¹ : ℚ) * ∑ a : ZMod N, χ a := by
  rw [generalizedBernoulli]
  have hExp : ((1 : ℕ) : ℤ) - 1 = 0 := by norm_num
  rw [hExp, zpow_zero, map_one, one_mul, Polynomial.bernoulli_one]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]
  rw [Finset.mul_sum]
  exact congrArg₂ (· - ·) rfl (Finset.sum_congr rfl fun a _ ↦ mul_comm _ _)

/-- For a nontrivial character, `B₁,χ` is the character-weighted sum of the rational residues
`a / N`; the constant term of the first Bernoulli polynomial cancels. -/
theorem generalizedBernoulli_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    χ.generalizedBernoulli 1 =
      ∑ a : ZMod N, χ a * algebraMap ℚ R ((a.val : ℚ) / N) := by
  have hN : N ≠ 1 := fun hN ↦ hχ (χ.level_one' hN)
  rw [generalizedBernoulli_one, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases ha : a = 0
  · simp [ha, χ.map_zero' hN]
  · simp [ha]

/-- Clearing the denominator in the degree-one formula gives
`N * B₁,χ = ∑ a, χ(a) * a`. -/
theorem natCast_mul_generalizedBernoulli_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    (N : R) * χ.generalizedBernoulli 1 = ∑ a : ZMod N, χ a * (a.val : R) := by
  rw [generalizedBernoulli_one_of_ne_one hχ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  rw [← map_natCast (algebraMap ℚ R) N, mul_left_comm, ← map_mul,
    mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N)), map_natCast]

/-- The generalized Bernoulli number `Bₖ,χ` vanishes when `k ≠ 1` and
`χ (-1) = -(-1) ^ k`. -/
@[simp]
theorem generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg [NeZero N]
    {χ : DirichletCharacter R N} {k : ℕ} (hk : k ≠ 1) (hχ : χ (-1) = -(-1) ^ k) :
    χ.generalizedBernoulli k = 0 := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  -- `β a` is the Bernoulli factor `Bₖ(ã / N)` of the residue `a`
  set β : ZMod N → ℚ := fun a ↦
    (Polynomial.bernoulli k).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N) with hβ
  -- Reflection `a ↦ -a` multiplies each summand by `χ (-1) * (-1) ^ k = -1`.
  -- At the zero residue, `Bₖ(0) = Bₖ(1)` because `k ≠ 1`.
  -- Thus `β (-a) = (-1) ^ k * β a` also at zero.
  have hβneg (a : ZMod N) : β (-a) = (-1) ^ k * β a := by
    by_cases ha : a = 0
    · subst a
      simp only [hβ, neg_zero, ↓reduceIte]
      rw [div_self hN, ← bernoulli_eval_one_sub, sub_self, bernoulli_eval_zero,
        bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one hk]
    · have : NeZero a := ⟨ha⟩
      simp only [hβ, neg_eq_zero, ha, ↓reduceIte]
      rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub a.val_le, sub_div, div_self hN,
        bernoulli_eval_one_sub]
  -- so each summand `χ a * β a` is odd in `a`
  have hneg (a : ZMod N) :
      χ (-a) * algebraMap ℚ R (β (-a)) = -(χ a * algebraMap ℚ R (β a)) := by
    have hχa : χ (-a) = -(-1) ^ k * χ a := by rw [neg_eq_neg_one_mul a, map_mul, hχ]
    have hsq : ((-1 : R) ^ k) * (-1) ^ k = 1 := by rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
    rw [hχa, hβneg, map_mul, map_pow, map_neg, map_one]
    linear_combination (-(χ a * algebraMap ℚ R (β a))) * hsq
  have hS : ∑ a, χ a * algebraMap ℚ R (β a) = 0 := by
    have h := Equiv.sum_comp (Equiv.neg (ZMod N)) fun a ↦ χ a * algebraMap ℚ R (β a)
    simp only [Equiv.neg_apply, hneg, Finset.sum_neg_distrib] at h
    -- `R` is a `ℚ`-algebra, so `-S = S` forces `S = 0`
    have h2 : (2 : R) * ∑ a, χ a * algebraMap ℚ R (β a) = 0 := by linear_combination -h
    rw [← one_mul (∑ a, _), ← map_one (algebraMap ℚ R), ← inv_mul_cancel₀ (two_ne_zero' ℚ),
      map_mul, map_ofNat, mul_assoc, h2, mul_zero]
  rw [generalizedBernoulli_def]
  exact (congrArg (_ * ·) hS).trans (mul_zero _)

end DirichletCharacter
