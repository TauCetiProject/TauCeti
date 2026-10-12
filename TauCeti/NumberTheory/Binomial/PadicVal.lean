/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Binomial coefficients modulo a prime and `p`-adic valuation

The binomial coefficient at `p ^ v_p(e)` stays nonzero modulo `p` when its upper argument is
the canonical natural-number residue of nonzero `e` modulo a sufficiently large power of `p`.
-/

public section

namespace TauCeti

section Binomial

variable {p : ℕ} [hp : Fact p.Prime]

/-- If `K` exceeds `v_p(e)`, then the binomial coefficient with upper argument
`(e % p ^ K).toNat` and lower argument `p ^ v_p(e)` is nonzero modulo `p`. -/
theorem choose_emod_ne_zero {e : ℤ} (he : e ≠ 0) {K : ℕ} (hK : padicValInt p e < K) :
    (((e % (p ^ K : ℕ)).toNat.choose (p ^ padicValInt p e) : ℕ) : ZMod p) ≠ 0 := by
  set v := padicValInt p e
  set n := (e % (p ^ K : ℕ)).toNat
  have hn : (n : ℤ) = e % (p ^ K : ℕ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg _ (Nat.cast_ne_zero.2 (pow_pos hp.out.pos _).ne'))
  have hdvd : ∀ k ≤ K, ((p ^ k : ℕ) ∣ n ↔ (p : ℤ) ^ k ∣ e) := fun k hk ↦ by
    rw [← Int.natCast_dvd_natCast, hn, Int.dvd_iff_emod_eq_zero, Int.dvd_iff_emod_eq_zero,
      Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.2 (Nat.pow_dvd_pow p hk))]
    simp
  obtain ⟨m, hm⟩ := (hdvd v hK.le).2 (padicValInt_dvd e)
  have hpm : ¬ p ∣ m := fun ⟨c, hc⟩ ↦ by
    have := (hdvd (v + 1) hK).1 ⟨c, by rw [hm, hc, pow_succ, mul_assoc]⟩
    rw [padicValInt_dvd_iff] at this
    omega
  have hmod := Choose.choose_pow_mul_pow_mul_modEq_choose_nat (p := p) (k := v) (a := m) (b := 1)
  rw [mul_one, Nat.choose_one_right] at hmod
  rw [hm, (ZMod.natCast_eq_natCast_iff _ _ _).2 hmod, Ne, ZMod.natCast_eq_zero_iff]
  exact hpm

end Binomial

end TauCeti
