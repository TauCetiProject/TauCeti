/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.BernoulliPolynomials
public import Mathlib.NumberTheory.DirichletCharacter.Basic
import TauCeti.Data.ZMod.Count

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
  of `B₁,χ` for a nontrivial character, and
  `DirichletCharacter.natCast_mul_generalizedBernoulli_one_of_dvd` computes it from the
  representatives modulo any multiple of the modulus.
* `DirichletCharacter.generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg` gives `Bₖ,χ = 0` when
  the parities of `χ` and `k` differ, except for `k = 1` at modulus one.

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
  rw [χ.level_one, generalizedBernoulli_def, Fintype.sum_subsingleton _ 1, map_one, one_mul]
  simp [Subsingleton.elim (1 : ZMod 1) 0, Polynomial.bernoulli_eval_one]

/-- The zeroth generalized Bernoulli number is `N⁻¹` times the sum of the character values. -/
theorem generalizedBernoulli_zero [NeZero N] (χ : DirichletCharacter R N) :
    χ.generalizedBernoulli 0 =
      algebraMap ℚ R (N : ℚ)⁻¹ * ∑ a : ZMod N, χ a := by
  simp [generalizedBernoulli_def]

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
  simp only [generalizedBernoulli_def, Nat.cast_one, sub_self, zpow_zero, map_one, one_mul,
    Polynomial.bernoulli_one, eval_sub, eval_X, eval_C, map_sub, mul_sub,
    Finset.sum_sub_distrib, Finset.sum_mul, mul_comm (algebraMap ℚ R 2⁻¹)]

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
    mul_div_cancel₀ _ (NeZero.ne _), map_natCast]

/-- **`B₁,χ` from the representatives modulo a multiple of the modulus.** For a nontrivial
character `χ ≠ 1` modulo `N ∣ M`, the sum of `χ(a mod N) a` over the representatives `0 ≤ a < M`
is `M B₁,χ`: each block of `N` consecutive representatives contributes `N B₁,χ`, since the shift
by a multiple of `N` contributes `∑_a χ(a) = 0`, which uses `χ ≠ 1`. At `M = N` this is
`natCast_mul_generalizedBernoulli_one_of_ne_one`. -/
theorem natCast_mul_generalizedBernoulli_one_of_dvd [IsDomain R] [NeZero N] {M : ℕ} [NeZero M]
    (hNM : N ∣ M) {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    (M : R) * χ.generalizedBernoulli 1 = ∑ a : ZMod M, χ (a.val : ZMod N) * (a.val : R) := by
  have hB : (N : R) * χ.generalizedBernoulli 1 = ∑ i ∈ Finset.range N, χ i * (i : R) := by
    rw [natCast_mul_generalizedBernoulli_one_of_ne_one hχ,
      ← ZMod.sum_val_eq_sum_range (fun i ↦ χ i * (i : R))]
    simp
  have hsum : ∑ i ∈ Finset.range N, χ i = 0 := by
    rw [← ZMod.sum_val_eq_sum_range (fun i ↦ χ i)]
    simpa using MulChar.sum_eq_zero_of_ne_one hχ
  rw [ZMod.sum_val_eq_sum_range (fun i ↦ χ i * (i : R))]
  obtain ⟨L, rfl⟩ := hNM
  have key (k : ℕ) : ∑ i ∈ Finset.range (N * k), χ i * (i : R) =
      (N * k : ℕ) * χ.generalizedBernoulli 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Nat.mul_succ, Finset.sum_range_add, ih]
      simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, zero_add, mul_add,
        Finset.sum_add_distrib, ← hB]
      rw [← Finset.sum_mul, hsum]
      ring
  exact (key L).symm

/-- The generalized Bernoulli number `Bₖ,χ` vanishes when `χ (-1) = -(-1) ^ k`, unless `k = 1`
and `N = 1`. That exception is genuine: by `generalizedBernoulli_modOne`, `B₁,χ = 1 / 2` for the
character modulo one. -/
@[simp]
theorem generalizedBernoulli_eq_zero_of_apply_neg_one_eq_neg [NeZero N]
    {χ : DirichletCharacter R N} {k : ℕ} (hk : k ≠ 1 ∨ N ≠ 1) (hχ : χ (-1) = -(-1) ^ k) :
    χ.generalizedBernoulli k = 0 := by
  have hN : (N : ℚ) ≠ 0 := NeZero.ne _
  -- `β a` is the Bernoulli factor `Bₖ(ã / N)` of the residue `a`
  set β : ZMod N → ℚ := fun a ↦
    (Polynomial.bernoulli k).eval (((if a = 0 then N else a.val : ℕ) : ℚ) / N) with hβ
  -- Reflection `a ↦ -a` multiplies `β a` by `(-1) ^ k`: for `a ≠ 0` by
  -- `Bₖ(1 - x) = (-1) ^ k * Bₖ(x)`, and at `a = 0` because `Bₖ(0) = Bₖ(1)` when `k ≠ 1`.
  have hβneg (a : ZMod N) (ha : a ≠ 0 ∨ k ≠ 1) : β (-a) = (-1) ^ k * β a := by
    rcases eq_or_ne a 0 with rfl | ha'
    · simp only [hβ, neg_zero, ↓reduceIte]
      rw [div_self hN, ← bernoulli_eval_one_sub, sub_self, bernoulli_eval_zero,
        bernoulli_eval_one, bernoulli_eq_bernoulli'_of_ne_one (ha.resolve_left (by simp))]
    · have : NeZero a := ⟨ha'⟩
      simp only [hβ, neg_eq_zero, ha', ↓reduceIte]
      rw [ZMod.val_neg_of_ne_zero, Nat.cast_sub a.val_le, sub_div, div_self hN,
        bernoulli_eval_one_sub]
  -- Hence each summand `χ a * β a` is odd in `a`, since `χ (-1) * (-1) ^ k = -1`. In the
  -- remaining case `a = 0`, `k = 1`, the summand vanishes because `N ≠ 1` gives `χ 0 = 0`.
  have hodd : Function.Odd fun a ↦ χ a * algebraMap ℚ R (β a) := by
    intro a
    by_cases ha : a ≠ 0 ∨ k ≠ 1
    · dsimp only
      rw [hβneg a ha, neg_eq_neg_one_mul a, map_mul, hχ]
      rcases neg_one_pow_eq_or R k with h | h <;> simp [h]
    · obtain ⟨rfl, rfl⟩ : a = 0 ∧ k = 1 := by tauto
      simp [χ.map_zero' (hk.resolve_left (by simp))]
  -- `R` is a `ℚ`-module, so the sum of the odd function vanishes
  have : HasUniqueDiv R := .of_module_rat R
  rw [generalizedBernoulli_def]
  exact mul_eq_zero_of_right _ hodd.sum_eq_zero

end DirichletCharacter
