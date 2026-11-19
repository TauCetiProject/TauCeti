/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum
import TauCeti.Algebra.Polynomial.Expand

/-!
# Expanded Hasse derivatives in prime and composite characteristic

The low-order derivatives of polynomials in `X^q` vanish when `q` is a power of the
prime characteristic. Over `ZMod 4`, the second Hasse derivative of `X⁴` is nonzero,
so characteristic four cannot replace the prime-characteristic hypothesis.
-/

public section

open Polynomial

/-- In characteristic two, the first Hasse derivative acts on the cofactor `X`. -/
example : hasseDeriv 1 (expand (ZMod 2) 2 X * X) = (X ^ 2 : (ZMod 2)[X]) := by
  simpa using (hasseDeriv_expand_mul (p := 2) (e := 1) (k := 1) (by decide)
    (X : (ZMod 2)[X]) X)

/-- Below order three, the Hasse derivatives of the expanded `X` vanish in characteristic three.
-/
example : hasseDeriv 1 (expand (ZMod 3) 3 X) = 0 ∧
    hasseDeriv 2 (expand (ZMod 3) 3 X) = 0 := by
  exact ⟨hasseDeriv_expand_eq_zero (p := 3) (e := 1) (by decide) X,
    hasseDeriv_expand_eq_zero (p := 3) (e := 1) (by decide) X⟩

/-- Characteristic four is insufficient: the second Hasse jet is `2X²`, while differentiating
only the cofactor `1` would give zero. -/
example : hasseDeriv 2 (expand (ZMod 4) 4 X) = C 2 * X ^ 2 ∧
    hasseDeriv 2 (expand (ZMod 4) 4 X) ≠ 0 ∧
    expand (ZMod 4) 4 X * hasseDeriv 2 1 = 0 := by
  have hchoose : (Nat.choose 4 2 : ZMod 4) = 2 := by decide
  have hjet : hasseDeriv 2 (expand (ZMod 4) 4 X) = monomial 2 (2 : ZMod 4) := by
    simp [expand_X, X_pow_eq_monomial, hasseDeriv_monomial, hchoose]
  simp only [hjet]
  simpa [C_mul_X_pow_eq_monomial, hasseDeriv_apply_one] using
    (by decide : (2 : ZMod 4) ≠ 0)
