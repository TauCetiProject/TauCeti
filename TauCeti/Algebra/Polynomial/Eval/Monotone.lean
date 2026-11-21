/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Monotonicity of polynomial evaluation

Evaluation is monotone when addition and multiplication are monotone in every argument.
This includes natural coefficients and natural evaluation points.
-/

public section

namespace Polynomial

variable {R : Type*} [Semiring R] {a b : R}

/-- Evaluation of a polynomial is monotone if addition and multiplication are monotone in each
argument, as in a canonically ordered semiring such as `ℕ`. -/
@[gcongr]
theorem eval_le_eval [Preorder R] [AddLeftMono R] [MulLeftMono R] [MulRightMono R]
    (p : R[X]) (hab : a ≤ b) : p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa using add_le_add hp hq
  | monomial n c => simpa using mul_le_mul_right (pow_le_pow_left' hab n) c


end Polynomial
