/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
public import Mathlib.SetTheory.Cardinal.Finite
import TauCeti.Data.Nat.Totient.PrimeSupport
import TauCeti.Data.ZMod.PrincipalUnits

/-!
# Fibers of unit reduction without new prime factors

If `t` does not introduce new prime factors into `q * t`, every unit modulo `q` has exactly
`t` lifts modulo `q * t`. The kernel-cardinality formula for `ZMod.unitsMap` then reduces to a
totient cancellation. This counts lifts in every reduced residue class, not just the class of one.
-/

public section

namespace ZMod

/-- Reduction from units modulo `m` to units modulo `q` has `m / q` lifts of each unit when
all prime factors of `m` already divide `q`. -/
theorem natCard_unitsMap_fiber_eq_of_primeFactors_subset {m q : ℕ} [NeZero m]
    (hd : q ∣ m) (h : m.primeFactors ⊆ q.primeFactors) (a : (ZMod q)ˣ) :
    Nat.card {u // unitsMap hd u = a} = m / q := by
  obtain ⟨t, rfl⟩ := hd
  have hq : q ≠ 0 := left_ne_zero_of_mul (NeZero.ne (q * t))
  have ht := Nat.primeFactors_mono (dvd_mul_left t q) (NeZero.ne (q * t))
  have hc := card_ker_unitsMap_mul_totient (dvd_mul_right q t)
  rw [Nat.totient_mul_of_primeFactors_subset (ht.trans h), mul_comm q.totient] at hc
  rw [Nat.mul_div_cancel_left _ hq.bot_lt]
  exact (Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective
    (unitsMap_surjective (dvd_mul_right q t)) a)).trans
      (Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hq.bot_lt) hc)

end ZMod
