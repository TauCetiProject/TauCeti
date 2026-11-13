/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.Data.Nat.Factorization.Induction

/-!
# Square multiples modulo `n` are detected at prime powers

An integer `x` is congruent to `y z²` modulo a nonzero `n` for some residue `z` exactly when it is
so modulo every prime power dividing `n`. The residues found modulo the coprime prime-power
factors of `n` glue by the Chinese remainder theorem.

This is the form in which square classes of residues are compared: for instance two triangular
binary forms `sxy + cy²` and `sxy + c'y²` lie in one genus exactly when `c'` is a square multiple
of `c` modulo `s`, and the local computation produces this congruence one prime power at a time.

## Main results

* `ZMod.exists_intCast_eq_mul_sq_iff`: `x ≡ y z² (mod n)` is solvable exactly when it is solvable
  modulo every prime power dividing `n`.
-/

public section

namespace ZMod

/-- **Square multiples modulo `n` are detected at prime powers.** For `n ≠ 0`, an integer `x` is
congruent to `y z²` modulo `n` for some residue `z` exactly when the same holds modulo every prime
power dividing `n`. -/
theorem exists_intCast_eq_mul_sq_iff {n : ℕ} (hn : n ≠ 0) (x y : ℤ) :
    (∃ z : ZMod n, (x : ZMod n) = y * z ^ 2) ↔
      ∀ p k : ℕ, p.Prime → p ^ k ∣ n → ∃ z : ZMod (p ^ k), (x : ZMod (p ^ k)) = y * z ^ 2 := by
  constructor
  · rintro ⟨z, hz⟩ p k _ hd
    refine ⟨ZMod.castHom hd _ z, ?_⟩
    simpa only [map_intCast, map_mul, map_pow] using
      congrArg (ZMod.castHom hd (ZMod (p ^ k))) hz
  · intro h
    induction n using Nat.recOnPosPrimePosCoprime with
    | prime_pow p k hp _ => exact h p k hp dvd_rfl
    | zero => exact absurd rfl hn
    | one => exact ⟨0, Subsingleton.elim _ _⟩
    | coprime a b ha hb hab iha ihb =>
      obtain ⟨u, hu⟩ := iha (by omega) fun p k hp hd ↦ h p k hp (hd.mul_right b)
      obtain ⟨v, hv⟩ := ihb (by omega) fun p k hp hd ↦ h p k hp (hd.mul_left a)
      refine ⟨(ZMod.chineseRemainder hab).symm (u, v), ?_⟩
      apply (ZMod.chineseRemainder hab).injective
      simp only [map_intCast, map_mul, map_pow, RingEquiv.apply_symm_apply]
      ext <;> simp [hu, hv]

end ZMod
