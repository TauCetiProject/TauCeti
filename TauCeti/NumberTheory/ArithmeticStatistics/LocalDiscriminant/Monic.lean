/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.ZMod.Defs
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff
import Mathlib.FieldTheory.Perfect
import TauCeti.RingTheory.Polynomial.Monic.Squarefree
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Local discriminant proportions of monic polynomials

For a prime `p`, the `p`-adic valuation of the discriminant of a monic integer polynomial
`x ^ n + a₁ x ^ (n - 1) + ⋯ + aₙ` is, as far as the values `0, …, j` are concerned, a function of
the coefficients modulo `p ^ (j + 1)`. The proportion `ν_j(n, p)` of coefficient tuples modulo
`p ^ (j + 1)` whose discriminant has valuation exactly `j` is therefore the normalized `p`-adic
Haar measure of the set of monic polynomials over `ℤ_p` with discriminant of valuation `j`. These
are the local factors of the densities of monic polynomials with squarefree, or nearly squarefree,
discriminant: `ν₀(n, p) + ν₁(n, p)` is the probability that `p ^ 2` does not divide the
discriminant.

This file defines `ν_j(n, p)` as an exact finite proportion and computes it in valuation zero.
A discriminant is prime to `p` exactly when the reduction modulo `p` is separable, that is,
squarefree over the perfect field `𝔽_p`. Counting monic squarefree polynomials over `𝔽_p`
(`Polynomial.ncard_monicSquarefreePolysOfDegree`) gives `ν₀(n, p) = 1 - 1/p` in every degree
`n ≥ 2`. In degrees `0` and `1` the discriminant is `1`, so `ν₀ = 1` and `ν_j = 0` for `j ≥ 1`.

## Main definitions

* `TauCeti.monicProportion n p j`: the proportion `ν_j(n, p)` of tuples `c` of `n` residues
  modulo `p ^ (j + 1)` such that `p ^ j` divides the discriminant of the monic polynomial with
  lower coefficients the canonical lifts of `c`, and `p ^ (j + 1)` does not.

## Main results

* `TauCeti.discr_monicOfCoeff_modEq`: congruent integral coefficient tuples have congruent
  discriminants, so `TauCeti.dvd_discr_monicOfCoeff_val_iff` lets any integral lift of the residues
  compute the condition defining `ν_j(n, p)`.
* `TauCeti.monicProportion_nonneg`, `TauCeti.monicProportion_le_one`: it is a proportion.
* `TauCeti.monicProportion_of_le_one`: in degrees `0` and `1` it is `1` for `j = 0` and `0` for
  `j ≥ 1`, at every modulus `p > 1`.
* `TauCeti.monicProportion_zero_eq_one_sub_inv`: for a prime `p` and `n ≥ 2`,
  `ν₀(n, p) = 1 - 1/p`.

## Implementation notes

The coefficient tuple `c : Fin n → ZMod (p ^ (j + 1))` is read through
`TauCeti.Polynomial.monicOfCoeff`, which indexes coefficients by the power of `x`. A proportion
does not depend on how the coefficient slots are ordered, so this agrees with the descending
convention `x ^ n + a₁ x ^ (n - 1) + ⋯ + aₙ`.

## References

* A. Ash, J. Brakenhoff and T. Zarrabi, *Equality of polynomial and field discriminants*,
  Experiment. Math. 16 (2007), §2 and §6 (Propositions 6.4 and 6.7).
* M. Bhargava, A. Shankar and X. Wang, *Squarefree values of polynomial discriminants I*,
  Invent. Math. 228 (2022), §1.
-/

public section

open Polynomial

namespace TauCeti

/-- The proportion `ν_j(n, p)` of tuples `c` of `n` residues modulo `p ^ (j + 1)` for which the
discriminant of the monic integer polynomial with lower coefficients the canonical lifts
`(c i).val` is divisible by `p ^ j` but not by `p ^ (j + 1)`. For a prime `p` it is the
probability that a monic polynomial of degree `n` over `ℤ_p` has discriminant of valuation
exactly `j`. -/
noncomputable def monicProportion (n : ℕ) (p : ℕ+) (j : ℕ) : ℝ :=
  Nat.card {c : Fin n → ZMod ((p : ℕ) ^ (j + 1)) //
      (p : ℤ) ^ j ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr ∧
        ¬ (p : ℤ) ^ (j + 1) ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr} /
    (p : ℝ) ^ ((j + 1) * n)

/-- `ν_j(n, p)` is the number of residue tuples modulo `p ^ (j + 1)` whose canonically lifted
discriminant has valuation exactly `j`, divided by the number `p ^ ((j + 1) * n)` of all tuples. -/
theorem monicProportion_def (n : ℕ) (p : ℕ+) (j : ℕ) :
    monicProportion n p j =
      Nat.card {c : Fin n → ZMod ((p : ℕ) ^ (j + 1)) //
          (p : ℤ) ^ j ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr ∧
            ¬ (p : ℤ) ^ (j + 1) ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr} /
        (p : ℝ) ^ ((j + 1) * n) :=
  (rfl)

variable {n : ℕ}

/-- Integral coefficient tuples that are congruent modulo `m` give monic polynomials whose
discriminants are congruent modulo `m`. -/
theorem discr_monicOfCoeff_modEq {m : ℕ} {c d : Fin n → ℤ} (h : ∀ i, c i ≡ d i [ZMOD m]) :
    (Polynomial.monicOfCoeff c).discr ≡ (Polynomial.monicOfCoeff d).discr [ZMOD m] := by
  have hcd : (fun i ↦ Int.castRingHom (ZMod m) (c i)) = fun i ↦ Int.castRingHom (ZMod m) (d i) :=
    funext fun i ↦ (ZMod.intCast_eq_intCast_iff _ _ _).mpr (h i)
  have := congrArg (fun c ↦ (Polynomial.monicOfCoeff c).discr) hcd
  rw [← Polynomial.map_monicOfCoeff, ← Polynomial.map_monicOfCoeff,
    (Polynomial.monic_monicOfCoeff c).discr_map, (Polynomial.monic_monicOfCoeff d).discr_map,
    eq_intCast, eq_intCast] at this
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

/-- Divisibility of the discriminant by a divisor `k` of the modulus `m` can be tested on any
integral lift of a residue tuple: in particular on the canonical lifts used by
`TauCeti.monicProportion`. -/
theorem dvd_discr_monicOfCoeff_val_iff {m k : ℕ} [NeZero m] (hk : k ∣ m) (a : Fin n → ZMod m)
    {c : Fin n → ℤ} (hc : ∀ i, (c i : ZMod m) = a i) :
    (k : ℤ) ∣ (Polynomial.monicOfCoeff fun i ↦ ((a i).val : ℤ)).discr ↔
      (k : ℤ) ∣ (Polynomial.monicOfCoeff c).discr := by
  have h := discr_monicOfCoeff_modEq (m := m) (c := fun i ↦ ((a i).val : ℤ)) (d := c) fun i ↦ by
    rw [← ZMod.intCast_eq_intCast_iff, hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero,
    h.of_dvd (Int.natCast_dvd_natCast.mpr hk)]

/-- The proportion `ν_j(n, p)` is nonnegative. -/
theorem monicProportion_nonneg (n : ℕ) (p : ℕ+) (j : ℕ) : 0 ≤ monicProportion n p j := by
  rw [monicProportion_def]
  positivity

/-- The proportion `ν_j(n, p)` is at most one: there are `p ^ ((j + 1) * n)` tuples of `n` residues
modulo `p ^ (j + 1)`. -/
theorem monicProportion_le_one (n : ℕ) (p : ℕ+) (j : ℕ) : monicProportion n p j ≤ 1 := by
  rw [monicProportion_def]
  refine div_le_one_of_le₀ ?_ (by positivity)
  calc (Nat.card {c : Fin n → ZMod ((p : ℕ) ^ (j + 1)) // _} : ℝ)
      ≤ Nat.card (Fin n → ZMod ((p : ℕ) ^ (j + 1))) := by
        exact_mod_cast Finite.card_subtype_le _
    _ = (p : ℝ) ^ ((j + 1) * n) := by
        rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
        push_cast
        ring

/-- In degrees `0` and `1` the discriminant is `1`, so at every modulus `p > 1` the proportion
`ν_j(n, p)` is `1` in valuation `j = 0` and `0` in every valuation `j ≥ 1`. -/
theorem monicProportion_of_le_one (hn : n ≤ 1) {p : ℕ+} (hp : p ≠ 1) (j : ℕ) :
    monicProportion n p j = if j = 0 then 1 else 0 := by
  -- A monic polynomial of degree at most one has discriminant `1`.
  have hdiscr (c : Fin n → ℤ) : (Polynomial.monicOfCoeff c).discr = 1 := by
    interval_cases n
    · obtain rfl : c = fun i : Fin 0 ↦ (1 : ℤ[X]).coeff i := Subsingleton.elim _ _
      rw [Polynomial.monicOfCoeff_coeff monic_one natDegree_one, ← C_1, discr_C]
    · exact discr_of_degree_eq_one <| by
        rw [degree_eq_natDegree (Polynomial.monic_monicOfCoeff c).ne_zero,
          Polynomial.natDegree_monicOfCoeff, Nat.cast_one]
  have hdvd (k : ℕ) : (p : ℤ) ^ k ∣ 1 ↔ k = 0 := by
    rw [← Nat.cast_pow, ← Nat.cast_one, Int.natCast_dvd_natCast, Nat.dvd_one, Nat.pow_eq_one]
    simp [hp]
  rw [monicProportion_def]
  simp only [hdiscr, hdvd, Nat.add_one_ne_zero, not_false_eq_true,
    and_true]
  split_ifs with hj
  · subst hj
    simp
  · simp [hj]

/-- **The unit-discriminant proportion.** For a prime `p` and `n ≥ 2`, a proportion
`ν₀(n, p) = 1 - 1/p` of the monic polynomials of degree `n` over `ℤ_p` have discriminant prime to
`p`: these are the polynomials whose reduction modulo `p` is squarefree, and over `𝔽_p` there are
`p ^ n - p ^ (n - 1)` monic squarefree polynomials of degree `n`. -/
theorem monicProportion_zero_eq_one_sub_inv (hn : 2 ≤ n) {p : ℕ+} (hp : (p : ℕ).Prime) :
    monicProportion n p 0 = 1 - 1 / (p : ℝ) := by
  have := Fact.mk hp
  have hiff (c : Fin n → ZMod (p : ℕ)) :
      ((p : ℤ) ^ 0 ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr ∧
        ¬ (p : ℤ) ∣ (Polynomial.monicOfCoeff fun i ↦ ((c i).val : ℤ)).discr) ↔
        Squarefree (Polynomial.monicOfCoeff c) := by
    rw [pow_zero, ← (Polynomial.monic_monicOfCoeff _).separable_map_zmod_iff_not_dvd_discr,
      Polynomial.map_monicOfCoeff, ← PerfectField.separable_iff_squarefree]
    simp
  have hcard : Nat.card {c : Fin n → ZMod (p : ℕ) // Squarefree (Polynomial.monicOfCoeff c)} =
      (p : ℕ) ^ n - (p : ℕ) ^ (n - 1) := by
    have h := ncard_monicSquarefreePolysOfDegree (ZMod (p : ℕ)) hn
    rw [Nat.card_zmod] at h
    rw [← Polynomial.ncard_setOf_monic_natDegree_eq_and, ← h]
    congr 1
    ext f
    simp only [Set.mem_ofPred_eq, mem_monicSquarefreePolysOfDegree_iff]
    tauto
  rw [monicProportion_def]
  rw [zero_add, pow_one, pow_one, Nat.card_congr (Equiv.subtypeEquivRight hiff), hcard, one_mul,
    Nat.cast_sub (Nat.pow_le_pow_right hp.pos (Nat.sub_le n 1))]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (by omega : 1 ≤ n)
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  rw [Nat.add_sub_cancel]
  push_cast
  field_simp
  ring

end TauCeti
