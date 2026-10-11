/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Orders of residues modulo prime powers

Let `ℓ` be a prime and `a > 1` a natural number. The multiplicative order of `a` modulo `ℓ ^ r`
has unbounded `ℓ`-adic valuation as `r` grows: for every `j`, the power `ℓ ^ j` divides it for all
large `r` (`ZMod.eventually_pow_dvd_orderOf_natCast`).

When `ℓ ∣ a` the residue of `a` is not a unit and its order is `0` from `r = 1` on. Otherwise the
order divides `φ(ℓ ^ r) = ℓ ^ (r - 1) (ℓ - 1)`, so if `ℓ ^ j` did not divide it, it would divide
the number `ℓ ^ (j - 1) (ℓ - 1)`, which does not depend on `r`; then `ℓ ^ r` would divide the
positive number `a ^ (ℓ ^ (j - 1) (ℓ - 1)) - 1` for every `r`, which is absurd.

For the residue `a = 𝔑𝔭` of a prime `𝔭 ∤ ℓ` of a number field, this order is the residue degree
of `𝔭` in the cyclotomic extension of level `ℓ ^ r`, so the statement says that these residue
degrees become divisible by any given power of `ℓ` along the cyclotomic tower.

## Main results

* `ZMod.orderOf_natCast_dvd_orderOf_natCast`: for `m ∣ n`, the order of `a` modulo `m` divides its
  order modulo `n`.
* `ZMod.eventually_pow_dvd_orderOf_natCast`: for every `j`, `ℓ ^ j` divides the order of `a`
  modulo `ℓ ^ r` for all large `r`.
-/

public section

namespace ZMod

/-- For `m ∣ n`, the order of a natural number `a` modulo `m` divides its order modulo `n`, since
reduction modulo `m` is a ring homomorphism `ZMod n →+* ZMod m`. -/
theorem orderOf_natCast_dvd_orderOf_natCast {m n : ℕ} (h : m ∣ n) (a : ℕ) :
    orderOf (a : ZMod m) ∣ orderOf (a : ZMod n) := by
  simpa using orderOf_map_dvd (ZMod.castHom h (ZMod m)).toMonoidHom (a : ZMod n)

/-- For a prime `ℓ` and a natural number `a > 1`, every power `ℓ ^ j` divides the multiplicative
order of `a` modulo `ℓ ^ r` for all large `r`. -/
theorem eventually_pow_dvd_orderOf_natCast {ℓ : ℕ} (hℓ : ℓ.Prime) {a : ℕ} (ha : 1 < a) (j : ℕ) :
    ∀ᶠ r in Filter.atTop, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ r)) := by
  -- The order modulo `ℓ ^ r` divides the order modulo `ℓ ^ r'` for `r ≤ r'`, so one level
  -- suffices.
  suffices h : ∃ R, ℓ ^ j ∣ orderOf (a : ZMod (ℓ ^ R)) by
    obtain ⟨R, hR⟩ := h
    exact Filter.eventually_atTop.2 ⟨R, fun r hr =>
      hR.trans (orderOf_natCast_dvd_orderOf_natCast (pow_dvd_pow ℓ hr) a)⟩
  by_cases hdvd : ℓ ∣ a
  · -- The residue of `a` modulo `ℓ` is `0`, of order `0`.
    have : Fact (1 < ℓ ^ 1) := ⟨by simpa using hℓ.one_lt⟩
    refine ⟨1, ?_⟩
    rw [(ZMod.natCast_eq_zero_iff a (ℓ ^ 1)).2 (by simpa using hdvd), orderOf_zero]
    exact dvd_zero _
  -- Otherwise the order modulo `ℓ ^ r` divides `φ (ℓ ^ r)`; the level `r = a ^ B`, with
  -- `B = ℓ ^ (j - 1) * (ℓ - 1)`, is too large for `a ^ B ≡ 1 (mod ℓ ^ r)`.
  set B := ℓ ^ (j - 1) * (ℓ - 1) with hB_def
  have hB : 0 < B := Nat.mul_pos (pow_pos hℓ.pos _) (Nat.sub_pos_of_lt hℓ.one_lt)
  have haB : 0 < a ^ B - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hB.ne' ha)
  set r := a ^ B with hr_def
  have hr : 0 < r := pow_pos (by omega) B
  refine ⟨r, ?_⟩
  have : NeZero (ℓ ^ r) := ⟨pow_ne_zero r hℓ.ne_zero⟩
  have hcop : a.Coprime (ℓ ^ r) :=
    Nat.Coprime.pow_right r (Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).2 hdvd))
  set o := orderOf (a : ZMod (ℓ ^ r)) with ho_def
  have hoφ : o ∣ ℓ ^ (r - 1) * (ℓ - 1) := by
    rw [ho_def, ← ZMod.coe_unitOfCoprime a hcop, orderOf_units, ← Nat.totient_prime_pow hℓ hr,
      ← ZMod.card_units_eq_totient]
    exact orderOf_dvd_card
  have ho : o ≠ 0 := by
    rw [ho_def, ← ZMod.coe_unitOfCoprime a hcop, orderOf_units]
    exact (orderOf_pos _).ne'
  by_contra hnot
  -- Write `o = ℓ ^ e * t` with `ℓ ∤ t`; then `e < j` and `t ∣ ℓ - 1`, so `o ∣ B`.
  obtain ⟨e, t, ht, hot⟩ := Nat.exists_eq_pow_mul_and_not_dvd ho ℓ hℓ.ne_one
  have he : e < j := by
    by_contra hje
    exact hnot (hot ▸ (pow_dvd_pow ℓ (not_lt.1 hje)).trans (dvd_mul_right _ _))
  have htcop : t.Coprime (ℓ ^ (r - 1)) :=
    Nat.Coprime.pow_right _ (Nat.Coprime.symm ((hℓ.coprime_iff_not_dvd).2 ht))
  have hoB : o ∣ B := by
    rw [hot, hB_def]
    exact mul_dvd_mul (pow_dvd_pow ℓ (by omega))
      (htcop.dvd_of_dvd_mul_left ((dvd_mul_left t (ℓ ^ e)).trans (hot ▸ hoφ)))
  -- Hence `ℓ ^ r ∣ a ^ B - 1`, which is positive and smaller than `r < ℓ ^ r`.
  have hpow : ((a ^ B : ℕ) : ZMod (ℓ ^ r)) = ((1 : ℕ) : ZMod (ℓ ^ r)) := by
    rw [Nat.cast_pow, Nat.cast_one]
    exact orderOf_dvd_iff_pow_eq_one.1 hoB
  have hdvd' : ℓ ^ r ∣ a ^ B - 1 :=
    (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ (by omega))).1
      ((ZMod.natCast_eq_natCast_iff _ _ _).1 hpow).symm
  have hlt : r < ℓ ^ r := Nat.lt_pow_self hℓ.one_lt
  have := Nat.le_of_dvd haB hdvd'
  omega

end ZMod
