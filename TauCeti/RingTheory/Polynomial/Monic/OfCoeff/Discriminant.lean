/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Polynomial.Resultant.Basic
public import TauCeti.RingTheory.Polynomial.Monic.OfCoeff.Basic
import TauCeti.RingTheory.Polynomial.Resultant.Discriminant

/-!
# Discriminants of monic polynomials with congruent coefficients

The discriminant of a monic polynomial commutes with base change
(`Polynomial.Monic.discr_map`). Reducing modulo `m`, the discriminant of the monic integer
polynomial `TauCeti.Polynomial.monicOfCoeff c` therefore depends only on the residues of the
coefficients `c` modulo `m`.

## Main results

* `TauCeti.Polynomial.discr_monicOfCoeff_modEq`: integral coefficient tuples that are congruent
  modulo `m` give monic polynomials with congruent discriminants.
* `TauCeti.Polynomial.dvd_discr_monicOfCoeff_val_iff`: divisibility of the discriminant by a
  divisor of `m` can be tested on any integral lift of a residue tuple modulo `m`, in particular
  on the canonical lifts `(a i).val`.
-/

public section

open Polynomial

namespace TauCeti.Polynomial

variable {n : ℕ}

/-- Integral coefficient tuples that are congruent modulo `m` give monic polynomials whose
discriminants are congruent modulo `m`. -/
theorem discr_monicOfCoeff_modEq {m : ℕ} {c d : Fin n → ℤ} (h : ∀ i, c i ≡ d i [ZMOD m]) :
    (monicOfCoeff c).discr ≡ (monicOfCoeff d).discr [ZMOD m] := by
  have hcd : (fun i ↦ Int.castRingHom (ZMod m) (c i)) = fun i ↦ Int.castRingHom (ZMod m) (d i) :=
    funext fun i ↦ (ZMod.intCast_eq_intCast_iff _ _ _).mpr (h i)
  have := congrArg (fun c ↦ (monicOfCoeff c).discr) hcd
  rw [← map_monicOfCoeff, ← map_monicOfCoeff, (monic_monicOfCoeff c).discr_map,
    (monic_monicOfCoeff d).discr_map, eq_intCast, eq_intCast] at this
  exact (ZMod.intCast_eq_intCast_iff _ _ _).mp this

/-- Divisibility of the discriminant by a divisor `k` of the modulus `m` can be tested on any
integral lift of a residue tuple, in particular on the canonical lifts `(a i).val`. -/
theorem dvd_discr_monicOfCoeff_val_iff {m k : ℕ} [NeZero m] (hk : k ∣ m) (a : Fin n → ZMod m)
    {c : Fin n → ℤ} (hc : ∀ i, (c i : ZMod m) = a i) :
    (k : ℤ) ∣ (monicOfCoeff fun i ↦ ((a i).val : ℤ)).discr ↔ (k : ℤ) ∣ (monicOfCoeff c).discr := by
  have h := discr_monicOfCoeff_modEq (m := m) (c := fun i ↦ ((a i).val : ℤ)) (d := c) fun i ↦ by
    rw [← ZMod.intCast_eq_intCast_iff, hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  rw [Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero,
    h.of_dvd (Int.natCast_dvd_natCast.mpr hk)]

end TauCeti.Polynomial
