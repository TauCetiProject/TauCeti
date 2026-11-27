/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Units
import TauCeti.Data.Nat.Totient
import TauCeti.Data.ZMod.PrincipalUnits

/-!
# Fibers of unit reduction with unchanged prime factors

Passing from `ℤ/(nk)` to `ℤ/n` gives exactly `k` unit lifts of each unit provided `n * k ≠ 0`
and `k` introduces no new prime factors. The fibers are cosets of the kernel, whose cardinality
is the ratio of the two totients.
-/

public section

namespace ZMod

/-- If `m ≠ 0`, `n ∣ m`, and `m` and `n` have the same prime factors, each unit modulo `n`
has exactly `m / n` unit lifts modulo `m`. -/
theorem card_unitsMap_fiber_of_primeFactors_subset {m n : ℕ} [NeZero m] (hmn : n ∣ m)
    (hs : m.primeFactors ⊆ n.primeFactors) (u : (ZMod n)ˣ) :
    Nat.card {v : (ZMod m)ˣ // unitsMap hmn v = u} = m / n := by
  obtain ⟨k, rfl⟩ := hmn
  have hmn : n ∣ n * k := dvd_mul_right n k
  have hn : 0 < n := Nat.pos_of_dvd_of_pos hmn (NeZero.pos (n * k))
  have hk : k.primeFactors ⊆ n.primeFactors :=
    (Nat.primeFactors_mono (dvd_mul_left k n) (NeZero.ne (n * k))).trans hs
  have h := card_ker_unitsMap_mul_totient hmn
  rw [Nat.totient_mul_of_primeFactors_subset hk] at h
  rw [Nat.mul_div_cancel_left _ hn]
  calc
    _ = Nat.card (unitsMap hmn).ker :=
      Nat.card_congr (MonoidHom.fiberEquivKerOfSurjective (unitsMap_surjective hmn) u)
    _ = k := Nat.eq_of_mul_eq_mul_right (Nat.totient_pos.mpr hn) h

end ZMod
