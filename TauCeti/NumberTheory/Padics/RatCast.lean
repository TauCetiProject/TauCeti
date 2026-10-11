/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import TauCeti.Data.Nat.Prime.Basic
import Mathlib.NumberTheory.Padics.PadicIntegers

/-!
# Rational numbers at almost every prime

A rational number has only finitely many primes dividing its numerator or its denominator. Hence
its image in `ℚ_[p]` is a `p`-adic integer at all but finitely many primes `p`, and a nonzero
rational number is a `p`-adic unit at all but finitely many primes. These are the statements that
make a rational object, such as a rational basis or a rational isometry, integral in every
completion outside a finite set of primes. Conversely, a rational number that is a `p`-adic integer
at every prime is an integer.

## Main results

* `Rat.eventually_not_dvd_den`: almost every prime is coprime to the denominator.
* `Padic.eventually_norm_rat_le_one`: a rational number is `p`-adically integral at almost every
  prime.
* `Padic.eventually_norm_rat_eq_one`: a nonzero rational number has `p`-adic norm one at almost
  every prime.
* `Padic.forall_norm_rat_le_one_iff_den_eq_one`: a rational number is an integer exactly when it
  is a `p`-adic integer at every prime.
-/

public section

open Filter

/-- All but finitely many primes do not divide the denominator of a rational number. -/
theorem Rat.eventually_not_dvd_den (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, ¬ (p : ℕ) ∣ q.den := by
  refine eventually_cofinite.mpr
    (((Set.finite_Iic q.den).preimage Subtype.val_injective.injOn).subset fun p hp ↦ ?_)
  exact Nat.le_of_dvd q.den_pos (not_not.mp hp)

namespace Padic

/-- A rational number is a `p`-adic integer at all but finitely many primes `p`. -/
theorem eventually_norm_rat_le_one (q : ℚ) :
    ∀ᶠ p : Nat.Primes in cofinite, ‖(q : ℚ_[p])‖ ≤ 1 := by
  filter_upwards [q.eventually_not_dvd_den] with p hp
  exact norm_rat_le_one hp

/-- A nonzero rational number is a `p`-adic unit at all but finitely many primes `p`. -/
theorem eventually_norm_rat_eq_one {q : ℚ} (hq : q ≠ 0) :
    ∀ᶠ p : Nat.Primes in cofinite, ‖(q : ℚ_[p])‖ = 1 := by
  filter_upwards [eventually_norm_rat_le_one q, eventually_norm_rat_le_one q⁻¹] with p hp hp'
  have hpos : 0 < ‖(q : ℚ_[p])‖ := norm_pos_iff.mpr (Rat.cast_ne_zero.mpr hq)
  rw [Rat.cast_inv, norm_inv] at hp'
  exact le_antisymm hp ((inv_le_one₀ hpos).mp hp')

/-- A rational number is an integer, that is, has denominator one, exactly when it is a `p`-adic
integer at every prime `p`. -/
theorem forall_norm_rat_le_one_iff_den_eq_one {q : ℚ} :
    (∀ p : Nat.Primes, ‖(q : ℚ_[p])‖ ≤ 1) ↔ q.den = 1 := by
  refine ⟨fun h ↦ ?_, fun h p ↦ norm_rat_le_one (by rw [h]; exact p.prop.not_dvd_one)⟩
  by_contra hq
  -- A prime dividing the denominator makes the denominator a non-unit in `ℤ_[p]`.
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hq
  let : Fact p.Prime := ⟨hp⟩
  have hlt := (PadicInt.norm_int_lt_one_iff_dvd (p := p) q.den).mpr
    (Int.natCast_dvd_natCast.mpr hpd)
  rw [Int.cast_natCast] at hlt
  exact hlt.ne ((PadicInt.isUnit_iff).mp (PadicInt.isUnit_den q (h ⟨p, hp⟩)))

end Padic
