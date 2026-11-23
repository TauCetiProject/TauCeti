/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Algebra.Ring.Pi

/-!
# Polynomial evaluation over products

Polynomial evaluation commutes with projection to each coordinate of a product of
semirings. This lets coordinatewise arguments use `Polynomial.eval_map_apply`
without folding function application back into a ring homomorphism.
-/

public section

namespace Polynomial

/-- Evaluating a polynomial over a product commutes with projection to a coordinate. -/
@[simp] theorem eval_map_evalRingHom {ι : Type*} {R : ι → Type*}
    [∀ i, Semiring (R i)] (p : (∀ i, R i)[X]) (x : ∀ i, R i) (i : ι) :
    (p.map (Pi.evalRingHom R i)).eval (x i) = p.eval x i := by
  simpa only [Pi.evalRingHom_apply] using p.eval_map_apply (Pi.evalRingHom R i) x

end Polynomial
