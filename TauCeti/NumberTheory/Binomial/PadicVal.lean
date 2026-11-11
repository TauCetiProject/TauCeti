/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Binomial coefficients modulo a prime and `p`-adic valuation

The binomial coefficient at `p ^ v_p(e)` stays nonzero modulo `p` when its upper argument is
any natural number congruent to nonzero `e` modulo a sufficiently large power of `p`.
-/

public section

namespace TauCeti

section Binomial

variable {p : ℕ} [Fact p.Prime]

/-- If `K` exceeds `v_p(e)` for nonzero `e`, then for every natural number `n` congruent to
`e` modulo `p ^ K`, the binomial coefficient `n.choose (p ^ v_p(e))` is nonzero modulo `p`. -/
theorem natCast_choose_pow_padicValInt_ne_zero_of_modEq {e : ℤ} (he : e ≠ 0) {K : ℕ}
    (hK : padicValInt p e < K) {n : ℕ} (hn : (n : ℤ) ≡ e [ZMOD (p : ℤ) ^ K]) :
    ((n.choose (p ^ padicValInt p e) : ℕ) : ZMod p) ≠ 0 := by
  set v := padicValInt p e
  have hdvd (k : ℕ) (hk : k ≤ K) : p ^ k ∣ n ↔ (p : ℤ) ^ k ∣ e := by
    exact_mod_cast (hn.of_dvd (pow_dvd_pow _ hk)).dvd_iff
  obtain ⟨m, rfl⟩ := (hdvd v hK.le).2 (padicValInt_dvd e)
  have hpm : ¬ p ∣ m := fun h ↦ by
    have := (hdvd (v + 1) hK).1 (pow_succ p v ▸ mul_dvd_mul_left _ h)
    rw [padicValInt_dvd_iff] at this
    omega
  have := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := v) (a := m) (b := 1)
  rw [mul_one, Nat.choose_one_right] at this
  rwa [(ZMod.natCast_eq_natCast_iff _ _ _).2 this, Ne, ZMod.natCast_eq_zero_iff]

end Binomial

end TauCeti
