/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Idempotent

/-!
# Spectral idempotents of an element with a commuting partial inverse

Let `C` and `b` be commuting elements of a ring `A` with `C ^ (h + 1) * b = C ^ h`, that is,
`C ^ h * (C * b - 1) = 0`. Then `p = (C * b) ^ h` is an idempotent, `E = 1 - p` is an idempotent
killed by `C ^ h`, and `w = b * p` inverts `C` on the complementary summand:

`C * w = w * C = 1 - E`, `E * w = w * E = 0`.

So `C` is invertible in the corner `p A p` and nilpotent of order at most `h` in `E A E`. In the
language of Drazin, `w` is the pseudo-inverse of `C` and `E` its spectral idempotent. For a
compact operator `u` and a good zero `a` of its Fredholm determinant, `C = 1 - a • u` and `b`
the normalised Hasse derivative of the Fredholm resolvent at `a` satisfy the hypothesis, and `E`
is the Riesz projector onto the generalised eigenspace `ker C ^ h`.

The splitting is unique: two idempotents `E₁`, `E₂`, killed by `C ^ h`, such that `C` is
invertible modulo each of them (`C * wᵢ = wᵢ * C = 1 - Eᵢ`), are equal
(`IsIdempotentElem.eq_of_pow_mul_eq_zero`).

## Main results

* `TauCeti.pow_mul_mul_pow_of_pow_succ_mul_eq`: `C ^ h * (C * b) ^ n = C ^ h` for every `n`.
* `Commute.isIdempotentElem_mul_pow_of_pow_succ_mul_eq`: `(C * b) ^ h` is idempotent.
* `Commute.mul_mul_mul_pow_of_pow_succ_mul_eq`,
  `Commute.mul_mul_pow_mul_of_pow_succ_mul_eq`: `C * (b * (C * b) ^ h) = (C * b) ^ h` and
  `b * (C * b) ^ h * C = (C * b) ^ h`.
* `IsIdempotentElem.one_sub_eq_pow_mul_pow`: if `C ^ h * E = 0` and `C * w = w * C = 1 - E` for an
  idempotent `E`, then `1 - E = C ^ h * w ^ h`.
* `IsIdempotentElem.eq_of_pow_mul_eq_zero`: uniqueness of the splitting.

## References

* M. P. Drazin, *Pseudo-inverses in associative rings and semigroups*, Amer. Math. Monthly **65**
  (1958), 506–514.
* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §7.
-/

public section

section Monoid

variable {M : Type*} [Monoid M] {C b : M} {h : ℕ}

namespace TauCeti

/-- If `C ^ (h + 1) * b = C ^ h`, then `C ^ h * (C * b) ^ n = C ^ h` for every `n`. -/
theorem pow_mul_mul_pow_of_pow_succ_mul_eq (hb : C ^ (h + 1) * b = C ^ h) (n : ℕ) :
    C ^ h * (C * b) ^ n = C ^ h := by
  induction n with
  | zero => rw [pow_zero, mul_one]
  | succ n ih => rw [pow_succ', ← mul_assoc, ← mul_assoc, ← pow_succ, hb, ih]

end TauCeti

namespace Commute

variable (hCb : Commute C b) (hb : C ^ (h + 1) * b = C ^ h)
include hCb hb

/-- If `C` and `b` commute and `C ^ (h + 1) * b = C ^ h`, then
`(C * b) ^ (h + n) = (C * b) ^ h` for every `n`. -/
theorem mul_pow_add_of_pow_succ_mul_eq (n : ℕ) : (C * b) ^ (h + n) = (C * b) ^ h := by
  rw [pow_add, hCb.mul_pow, (hCb.pow_pow h h).eq, mul_assoc,
    TauCeti.pow_mul_mul_pow_of_pow_succ_mul_eq hb, ← (hCb.pow_pow h h).eq, ← hCb.mul_pow]

/-- If `C` and `b` commute and `C ^ (h + 1) * b = C ^ h`, then `(C * b) ^ h` is idempotent. -/
theorem isIdempotentElem_mul_pow_of_pow_succ_mul_eq : IsIdempotentElem ((C * b) ^ h) := by
  rw [IsIdempotentElem, ← pow_add, hCb.mul_pow_add_of_pow_succ_mul_eq hb]

/-- If `C` and `b` commute and `C ^ (h + 1) * b = C ^ h`, then `w = b * (C * b) ^ h` satisfies
`C * w = (C * b) ^ h`. -/
theorem mul_mul_mul_pow_of_pow_succ_mul_eq : C * (b * (C * b) ^ h) = (C * b) ^ h := by
  rw [← mul_assoc, ← pow_succ', ← hCb.mul_pow_add_of_pow_succ_mul_eq hb 1]

/-- If `C` and `b` commute and `C ^ (h + 1) * b = C ^ h`, then `w = b * (C * b) ^ h` satisfies
`w * C = (C * b) ^ h`. -/
theorem mul_mul_pow_mul_of_pow_succ_mul_eq : b * (C * b) ^ h * C = (C * b) ^ h := by
  rw [mul_assoc, ← (((Commute.refl C).mul_right hCb).pow_right h).eq, ← mul_assoc, ← hCb.eq,
    mul_assoc, hCb.mul_mul_mul_pow_of_pow_succ_mul_eq hb]

end Commute

end Monoid

namespace IsIdempotentElem

variable {A : Type*} [Ring A] {C E w : A} {h : ℕ}

/-- Let `E` be an idempotent with `C ^ h * E = 0`, and let `w` invert `C` modulo `E`:
`C * w = w * C = 1 - E`. Then `1 - E = C ^ h * w ^ h`. -/
theorem one_sub_eq_pow_mul_pow (he : IsIdempotentElem E) (hz : C ^ h * E = 0)
    (hw : C * w = 1 - E) (hw' : w * C = 1 - E) : 1 - E = C ^ h * w ^ h := by
  cases h with
  | zero =>
    rw [pow_zero, one_mul] at hz
    rw [hz, pow_zero, pow_zero, one_mul, sub_zero]
  | succ h =>
    have hCw : Commute C w := hw.trans hw'.symm
    rw [← hCw.mul_pow, hw, he.one_sub.pow_succ_eq]

/-- **Uniqueness of the spectral splitting.** Let `E₁` and `E₂` be idempotents killed by `C ^ h`,
such that `C` is invertible modulo each of them: `C * wᵢ = wᵢ * C = 1 - Eᵢ`. Then `E₁ = E₂`. -/
theorem eq_of_pow_mul_eq_zero {E₁ E₂ w₁ w₂ : A} (he₁ : IsIdempotentElem E₁)
    (he₂ : IsIdempotentElem E₂) (hz₁ : C ^ h * E₁ = 0) (hz₂ : C ^ h * E₂ = 0)
    (hw₁ : C * w₁ = 1 - E₁) (hw₁' : w₁ * C = 1 - E₁) (hw₂ : C * w₂ = 1 - E₂)
    (hw₂' : w₂ * C = 1 - E₂) : E₁ = E₂ := by
  -- `1 - E₁ = w₁ ^ h * C ^ h` kills `E₂`, and `1 - E₂ = C ^ h * w₂ ^ h` is killed by `E₁`, which
  -- commutes with `C` because `C (1 - E₁) = C w₁ C = (1 - E₁) C`.
  have hCw₁ : Commute C w₁ := hw₁.trans hw₁'.symm
  have hCE₁ : Commute C E₁ := by
    have h1 : Commute C (1 - E₁) := hw₁' ▸ hCw₁.mul_right (Commute.refl C)
    simpa using (Commute.one_right C).sub_right h1
  have h₁ : (1 - E₁) * E₂ = 0 := by
    rw [he₁.one_sub_eq_pow_mul_pow hz₁ hw₁ hw₁', (hCw₁.pow_pow h h).eq, mul_assoc, hz₂,
      mul_zero]
  have h₂ : E₁ * (1 - E₂) = 0 := by
    rw [he₂.one_sub_eq_pow_mul_pow hz₂ hw₂ hw₂', ← mul_assoc, ← (hCE₁.pow_left h).eq, hz₁,
      zero_mul]
  rw [sub_mul, one_mul, sub_eq_zero] at h₁
  rw [mul_sub, mul_one, sub_eq_zero] at h₂
  rw [h₂, ← h₁]

end IsIdempotentElem
