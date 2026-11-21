/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Nilpotent.Basic

/-!
# Nilpotence of `p` modulo a power of `p`

In `ℤ/p^n` the element `p` is nilpotent, since `p ^ n = 0`. Consequently a multiple `p c` plus a
unit is a unit, and in a nontrivial `ℤ/p^n` a multiple `p c` is never a unit. No primality of `p`
is needed. For `p = 2` these say that the units of `ℤ/2^{k+1}` are exactly the odd elements
(`TauCeti.Data.ZMod.Two`).

## Main results

* `ZMod.isNilpotent_natCast_self_pow`: `p` is nilpotent in `ℤ/p^n`.
* `ZMod.isUnit_natCast_mul_add`: `p c + u` is a unit in `ℤ/p^n` when `u` is.
* `ZMod.not_isUnit_natCast_mul`: `p c` is not a unit in a nontrivial `ℤ/p^n`.
* `ZMod.natCast_self_pow_ne_zero`: `p ≠ 0` in `ℤ/p^n` for `1 < p` and `1 < n`.
* `ZMod.span_pow_eq_zero`: `(p) ^ e = 0` in `ZMod (p ^ e)`.
* `ZMod.isNilpotent_span_natCast`: `IsNilpotent (Ideal.span {(p : ZMod (p ^ e))})`.
-/

public section

namespace ZMod

variable {p n : ℕ}

/-- **`p` is nilpotent modulo a power of `p`**: `p ^ n = 0` in `ℤ/p^n`. -/
theorem isNilpotent_natCast_self_pow : IsNilpotent (p : ZMod (p ^ n)) :=
  ⟨n, by exact_mod_cast ZMod.natCast_self (p ^ n)⟩

/-- A multiple of `p` plus a unit is a unit in `ℤ/p^n`. -/
theorem isUnit_natCast_mul_add {c u : ZMod (p ^ n)} (hu : IsUnit u) : IsUnit (p * c + u) :=
  ((Commute.all _ c).isNilpotent_mul_right isNilpotent_natCast_self_pow).isUnit_add_right_of_commute
    hu (Commute.all _ _)

/-- A multiple of `p` is not a unit in a nontrivial `ℤ/p^n`. -/
theorem not_isUnit_natCast_mul [Nontrivial (ZMod (p ^ n))] (c : ZMod (p ^ n)) :
    ¬ IsUnit ((p : ZMod (p ^ n)) * c) :=
  fun h ↦ h.not_isNilpotent ((Commute.all _ c).isNilpotent_mul_right isNilpotent_natCast_self_pow)

/-- `p` is nonzero modulo `p ^ n` when `1 < p` and `1 < n`. -/
theorem natCast_self_pow_ne_zero (hp : 1 < p) (hn : 1 < n) : (p : ZMod (p ^ n)) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have : n ≤ 1 := (Nat.pow_dvd_pow_iff_le_right hp).mp (by rwa [pow_one])
  omega

/-- In `ZMod (p ^ e)`, the `e`-th power of the principal ideal `(p)` vanishes. -/
theorem span_pow_eq_zero (p e : ℕ) : (Ideal.span {(p : ZMod (p ^ e))}) ^ e = 0 := by
  rw [Ideal.span_singleton_pow, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot,
    ← Nat.cast_pow, ZMod.natCast_self]

/-- In `ZMod (p ^ e)`, the principal ideal `(p)` is nilpotent in the ordinary sense. -/
theorem isNilpotent_span_natCast (p e : ℕ) : IsNilpotent (Ideal.span {(p : ZMod (p ^ e))}) :=
  ⟨e, span_pow_eq_zero p e⟩

end ZMod
