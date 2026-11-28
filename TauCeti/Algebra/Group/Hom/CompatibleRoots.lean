/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Rat.Defs

import Mathlib.Data.Int.Cast.Lemmas
import TauCeti.Data.Rat.NumDenDvd

/-!
# Homomorphisms from `ℚ` attached to compatible systems of roots

A family `z : ℕ+ → G` in a group is a *compatible system of roots* when `z (m * n) ^ m = z n`
for all positive `m` and `n`: each `z (m * n)` is an `m`-th root of `z n`, so that `z n` plays the
role of `1 / n`. Such a family defines a homomorphism `Multiplicative ℚ →* G` sending `k / n` to
`z n ^ k`. It is defined by `q ↦ z q.den ^ q.num`, and compatibility shows that every other
representation `q = k / n` gives the same value, which makes it multiplicative.

This is the construction behind the character of rational exponents
`TauCeti.PrimeToPTateModule.ratChar` of a compatible family of roots of unity.

## Main definitions

* `TauCeti.ratHomOfCompatibleRoots z hz`: the homomorphism `Multiplicative ℚ →* G` sending
  `k / n` to `z n ^ k`, for a compatible system of roots `z`.

## Main results

* `TauCeti.ratHomOfCompatibleRoots_ofAdd_eq_zpow`: `ratHomOfCompatibleRoots z hz` sends `q` to
  `z n ^ k` whenever `q = k / n`.
* `TauCeti.ratHomOfCompatibleRoots_ofAdd_intCast_div`: it sends `k / n` to `z n ^ k`.
* `TauCeti.eq_ratHomOfCompatibleRoots`: it is the only homomorphism sending `1 / n` to `z n` for
  every `n`.
-/

public section

open Multiplicative

namespace TauCeti

variable {G : Type*} [Group G] (z : ℕ+ → G) (hz : ∀ m n : ℕ+, z (m * n) ^ (m : ℕ) = z n)

include hz in
/-- `z q.den ^ q.num = z n ^ k` whenever `q = k / n`, by compatibility of the roots. -/
private theorem zpow_den_num_eq_zpow (n : ℕ+) {q : ℚ} {k : ℤ} (h : (k : ℚ) = q * (n : ℕ)) :
    z ⟨q.den, q.den_pos⟩ ^ q.num = z n ^ k := by
  obtain ⟨c, hc⟩ : q.den ∣ (n : ℕ) := Int.natCast_dvd_natCast.mp
    (Rat.den_dvd_of_intCast_eq_mul_intCast q (by rw [h, Int.cast_natCast]))
  have hc0 : 0 < c := Nat.pos_of_mul_pos_left (hc ▸ n.pos)
  have hn : n = c.toPNat hc0 * q.den.toPNat q.den_pos :=
    PNat.eq (by rw [PNat.mul_coe]; exact hc.trans (mul_comm _ _))
  have hk : k = c * q.num := by
    have : (k : ℚ) = c * q.num := by
      rw [h, hc, Nat.cast_mul, ← mul_assoc, Rat.mul_den_eq_num, mul_comm]
    exact_mod_cast this
  rw [hk, hn, zpow_mul, zpow_natCast]
  exact congrArg (· ^ q.num) (hz (c.toPNat hc0) (q.den.toPNat q.den_pos)).symm

/-- The homomorphism `Multiplicative ℚ →* G` attached to a compatible system of roots `z`, that
is `z (m * n) ^ m = z n`: it sends `k / n` to `z n ^ k`
(`TauCeti.ratHomOfCompatibleRoots_ofAdd_eq_zpow`), and is defined by `q ↦ z q.den ^ q.num`. Its
body is exposed so that this value is a definitional equation in importing modules
(`TauCeti.ratHomOfCompatibleRoots_ofAdd`). -/
@[expose] def ratHomOfCompatibleRoots : Multiplicative ℚ →* G where
  toFun q := z ⟨q.toAdd.den, q.toAdd.den_pos⟩ ^ q.toAdd.num
  map_one' := by simp
  map_mul' q r := by
    -- Compute all three values at the common level `q.den * r.den`.
    set a := q.toAdd
    set b := r.toAdd
    let N : ℕ+ := ⟨a.den * b.den, Nat.mul_pos a.den_pos b.den_pos⟩
    have ha : ((a.num * b.den : ℤ) : ℚ) = a * (N : ℕ) := by
      push_cast [N, PNat.mk_coe]
      rw [← mul_assoc, Rat.mul_den_eq_num]
    have hb : ((b.num * a.den : ℤ) : ℚ) = b * (N : ℕ) := by
      push_cast [N, PNat.mk_coe]
      rw [mul_left_comm, Rat.mul_den_eq_num, mul_comm]
    rw [toAdd_mul, zpow_den_num_eq_zpow z hz N ha, zpow_den_num_eq_zpow z hz N hb,
      zpow_den_num_eq_zpow z hz N (k := a.num * b.den + b.num * a.den)
        (by rw [Int.cast_add, ha, hb, add_mul]), zpow_add]

/-- `ratHomOfCompatibleRoots z hz` sends `q` to `z q.den ^ q.num`. -/
theorem ratHomOfCompatibleRoots_ofAdd (q : ℚ) :
    ratHomOfCompatibleRoots z hz (ofAdd q) = z ⟨q.den, q.den_pos⟩ ^ q.num :=
  (rfl)

/-- `ratHomOfCompatibleRoots z hz` sends `q` to `z n ^ k` whenever `q = k / n`. -/
theorem ratHomOfCompatibleRoots_ofAdd_eq_zpow (n : ℕ+) {q : ℚ} {k : ℤ}
    (h : (k : ℚ) = q * (n : ℕ)) : ratHomOfCompatibleRoots z hz (ofAdd q) = z n ^ k :=
  zpow_den_num_eq_zpow z hz n h

/-- `ratHomOfCompatibleRoots z hz` sends `k / n` to `z n ^ k`. -/
@[simp]
theorem ratHomOfCompatibleRoots_ofAdd_intCast_div (n : ℕ+) (k : ℤ) :
    ratHomOfCompatibleRoots z hz (ofAdd ((k : ℚ) / (n : ℕ))) = z n ^ k :=
  ratHomOfCompatibleRoots_ofAdd_eq_zpow z hz n
    (div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr n.ne_zero)).symm

/-- `ratHomOfCompatibleRoots z hz` is the only homomorphism `Multiplicative ℚ →* G` sending
`1 / n` to `z n` for every positive `n`. -/
theorem eq_ratHomOfCompatibleRoots {f : Multiplicative ℚ →* G}
    (hf : ∀ n : ℕ+, f (ofAdd ((1 : ℚ) / (n : ℕ))) = z n) : f = ratHomOfCompatibleRoots z hz := by
  refine MonoidHom.ext fun q ↦ ?_
  -- Write `q = q.num • (1 / q.den)` and use that `f` commutes with integer powers.
  have hq : q = ofAdd (q.toAdd.num • ((1 : ℚ) / q.toAdd.den)) := by
    rw [zsmul_eq_mul, mul_one_div, Rat.num_div_den, ofAdd_toAdd]
  conv_lhs => rw [hq, ofAdd_zsmul, map_zpow]
  exact congrArg (· ^ q.toAdd.num) (hf ⟨q.toAdd.den, q.toAdd.den_pos⟩)

end TauCeti
