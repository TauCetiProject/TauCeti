/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultant lemmas

Mathlib evaluates the resultant against the linear polynomial `X - C x` on either side
(`Polynomial.resultant_X_sub_C_left`, `Polynomial.resultant_X_sub_C_right`). This file records the
companion for the *reversed* polynomial `C x - X`, which is the shape that arises as `x - θ` in
`AdjoinRoot f`: the answer is `f.eval x`, with **no sign**.

The file also normalizes bounded resultants with a monic left argument. This makes the resultant
independent of the chosen valid right degree bound, as needed when comparing resultant-based
discriminant formulas that use different bounds. In the same spirit, it extends Mathlib's
multiplicativity of the resultant in its left argument from actual degrees to arbitrary valid
degree bounds.

That absence is the point. `C x - X` is `C (-1) * (X - C x)`, which contributes `(-1) ^ m`, and
`resultant_X_sub_C_right` contributes another `(-1) ^ m`, so the two cancel.

## Main results

* `Polynomial.resultant_C_sub_X_right`
* `Polynomial.resultant_mul_left_of_natDegree_le`: multiplicativity of the resultant in its left
  argument, for arbitrary valid degree bounds of the two factors.
* `Polynomial.Monic.resultant_of_le`: for a monic left argument, the resultant is independent of
  the valid degree bound supplied for the right argument.

## Provenance

Adapted from Michael Stoll's `EllipticCurves`
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0) at commit
`66889eada51a74c2f5dfb7fb5909b0b5a0a2d96e`, `EllipticCurves/Mathlib/Basic.lean` line 615, where
it is a Mathlib-bound prerequisite of the explicit `2`-descent.
-/

public section

namespace Polynomial

variable {R : Type*} [CommRing R]

/-- The resultant of `f` with the reversed linear polynomial `C x - X` is `f.eval x`. Note the
absence of a sign: `C x - X` is `-(X - C x)`, and the two signs cancel. -/
@[simp]
theorem resultant_C_sub_X_right (f : R[X]) (x : R) (m : ℕ) (hm : f.natDegree ≤ m) :
    f.resultant (C x - X) m 1 = f.eval x := by
  -- `C x - X` is `X - C x` scaled by the constant `-1`
  have hneg : C x - X = C (-1 : R) * (X - C x) := by simp
  rw [hneg, resultant_C_mul_right, resultant_X_sub_C_right f m x hm, ← mul_assoc, ← pow_add,
    ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]

/-- `Res(f₁ * f₂, g) = Res(f₁, g) * Res(f₂, g)` for arbitrary valid degree bounds `m₁`, `m₂` of the
two factors, the product being given the bound `m₁ + m₂`. Unlike `Polynomial.resultant_mul_left`,
the bounds need not be the actual degrees. -/
theorem resultant_mul_left_of_natDegree_le {f₁ f₂ g : R[X]} {m₁ m₂ n : ℕ}
    (h₁ : f₁.natDegree ≤ m₁) (h₂ : f₂.natDegree ≤ m₂) (hg : g.natDegree ≤ n) :
    (f₁ * f₂).resultant g (m₁ + m₂) n = f₁.resultant g m₁ n * f₂.resultant g m₂ n := by
  obtain ⟨k₁, rfl⟩ := Nat.exists_eq_add_of_le h₁
  obtain ⟨k₂, rfl⟩ := Nat.exists_eq_add_of_le h₂
  rw [show f₁.natDegree + k₁ + (f₂.natDegree + k₂) = f₁.natDegree + f₂.natDegree + (k₁ + k₂) by
      ring, resultant_add_left_deg _ _ _ _ _ natDegree_mul_le, resultant_mul_left _ _ _ _ hg,
    resultant_add_left_deg _ _ _ _ _ le_rfl, resultant_add_left_deg _ _ _ _ _ le_rfl]
  ring

end Polynomial

namespace TauCeti

open Polynomial

variable {R : Type*} [CommRing R]

/-- For monic `f`, `f.resultant g` does not depend on which valid upper bound is supplied for the
degree of `g`. -/
theorem _root_.Polynomial.Monic.resultant_of_le {f g : R[X]} (hf : f.Monic) {n : ℕ}
    (hn : g.natDegree ≤ n) : f.resultant g f.natDegree n = f.resultant g := by
  have hn' : n = g.natDegree + (n - g.natDegree) :=
    (Nat.add_sub_cancel' hn).symm
  conv_lhs => rw [hn']
  rw [Polynomial.resultant_add_right_deg _ _ _ _ _ le_rfl, Polynomial.coeff_natDegree,
    hf.leadingCoeff, one_pow, one_mul]

end TauCeti
