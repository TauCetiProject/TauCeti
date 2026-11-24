/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Algebra.Ring.Idempotent
import Mathlib.Tactic.NoncommRing

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
* `IsIdempotentElem.isUnit_add_mul_one_sub`: `E + C * (1 - E)` is a unit when
  `C * w = w * C = 1 - E`.
* `IsIdempotentElem.isUnit_one_add_sub_one_smul`: `1 + (x - 1) • E` is a unit when `IsUnit x`.
* `IsIdempotentElem.one_sub_eq_pow_mul_pow`: if `C ^ h * E = 0` and `C * w = w * C = 1 - E` for an
  idempotent `E`, then `1 - E = C ^ h * w ^ h`.
* `IsIdempotentElem.eq_of_pow_mul_eq_zero`: uniqueness of the splitting.
* `RingHom.map_mul_eq_one_sub_and_mul_eq_zero`, `RingHom.exists_mul_eq_one_sub_map`: transport of
  a complementary inverse along a ring homomorphism.

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

/-- Replacing one block of a split operator by the identity gives a unit when the
complementary block is invertible.
The inverse is `E + (1 - E) * w`, where `C * w = w * C = 1 - E`. -/
theorem isUnit_add_mul_one_sub (he : IsIdempotentElem E)
    (hw : C * w = 1 - E) (hw' : w * C = 1 - E) :
    IsUnit (E + C * (1 - E)) := by
  have hCE : Commute C E := by
    have hCw : Commute C w := hw.trans hw'.symm
    have h1 : Commute C (1 - E) := hw' ▸ hCw.mul_right (Commute.refl C)
    simpa using (Commute.one_right C).sub_right h1
  have hEw : E * ((1 - E) * w) = 0 := by
    simp [← mul_assoc, mul_sub, he.eq]
  have hwE : (1 - E) * w * E = 0 := by
    rw [← hw', mul_assoc w C w, hw, mul_assoc]
    simp [sub_mul, he.eq]
  have hcompE : C * (1 - E) * E = 0 := by
    simp [mul_assoc, sub_mul, he.eq]
  have hcompw : C * (1 - E) * ((1 - E) * w) = 1 - E := by
    rw [← mul_assoc, mul_assoc C (1 - E) (1 - E), he.one_sub.eq,
      ((Commute.one_right C).sub_right hCE).eq, mul_assoc, hw, he.one_sub.eq]
  have hEcomp : E * (C * (1 - E)) = 0 := by
    rw [← mul_assoc, ← hCE.eq, mul_assoc]
    simp [mul_sub, he.eq]
  have hwcomp : (1 - E) * w * (C * (1 - E)) = 1 - E := by
    rw [mul_assoc, ← mul_assoc w C, hw', he.one_sub.eq, he.one_sub.eq]
  refine isUnit_iff_exists.mpr ⟨E + (1 - E) * w, ?_, ?_⟩
  · simp [mul_add, add_mul, he.eq, hEw, hcompE, hcompw]
  · simp [mul_add, add_mul, he.eq, hwE, hEcomp, hwcomp]

/-- Scaling an idempotent block `E` by a unit `x` preserves invertibility:
`1 + (x - 1) • E` is a unit with inverse `1 + (Ring.inverse x - 1) • E`. -/
theorem isUnit_one_add_sub_one_smul {R : Type*} [Ring R] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] (he : IsIdempotentElem E)
    {x : R} (hx : IsUnit x) : IsUnit (1 + (x - 1) • E) := by
  have hmul (a b : R) (hba : b * a = 1) : (1 + (a - 1) • E) * (1 + (b - 1) • E) = 1 := by
    have hcoeff : a - 1 + (b - 1 + (b - 1) * (a - 1)) = 0 := by
      calc a - 1 + (b - 1 + (b - 1) * (a - 1)) = b * a - 1 := by noncomm_ring
        _ = 0 := sub_eq_zero.mpr hba
    simp only [add_mul, mul_add, one_mul, mul_one, mul_smul_comm, smul_mul_assoc, smul_add,
      smul_smul, he.eq, add_assoc]
    simp only [← add_smul, hcoeff, zero_smul, add_zero]
  exact isUnit_iff_exists.mpr ⟨1 + (Ring.inverse x - 1) • E,
    hmul _ _ (Ring.inverse_mul_cancel _ hx), hmul _ _ (Ring.mul_inverse_cancel _ hx)⟩

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

namespace RingHom

/-- Transporting complementary-inverse equations along a ring homomorphism `Φ`. -/
theorem map_mul_eq_one_sub_and_mul_eq_zero {A B : Type*} [Ring A] [Ring B] (Φ : A →+* B)
    {C E w : A} {C' : B} (hC : Φ C = C')
    (hw₁ : C * w = 1 - E) (hw₂ : w * C = 1 - E) (hw₃ : E * w = 0) (hw₄ : w * E = 0) :
    C' * Φ w = 1 - Φ E ∧ Φ w * C' = 1 - Φ E ∧ Φ E * Φ w = 0 ∧ Φ w * Φ E = 0 :=
  ⟨by rw [← hC, ← map_mul, hw₁, map_sub, map_one],
   by rw [← hC, ← map_mul, hw₂, map_sub, map_one],
   by rw [← map_mul, hw₃, map_zero],
   by rw [← map_mul, hw₄, map_zero]⟩

/-- Transporting an existential complementary inverse with a side predicate along a ring
homomorphism `Φ`. -/
theorem exists_mul_eq_one_sub_map {A B : Type*} [Ring A] [Ring B] (Φ : A →+* B)
    {C E : A} {C' : B} (hC : Φ C = C') {P : A → Prop} {Q : B → Prop}
    (hw : ∃ w : A, C * w = 1 - E ∧ w * C = 1 - E ∧ E * w = 0 ∧ w * E = 0 ∧ P w)
    (hPQ : ∀ {v : A}, P v → Q (Φ v)) :
    ∃ w' : B, C' * w' = 1 - Φ E ∧ w' * C' = 1 - Φ E ∧ Φ E * w' = 0 ∧ w' * Φ E = 0 ∧ Q w' := by
  obtain ⟨w, hw₁, hw₂, hw₃, hw₄, hwP⟩ := hw
  have h := Φ.map_mul_eq_one_sub_and_mul_eq_zero hC hw₁ hw₂ hw₃ hw₄
  exact ⟨Φ w, h.1, h.2.1, h.2.2.1, h.2.2.2, hPQ hwP⟩

end RingHom
