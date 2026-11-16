/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Distribution.DerivNotation

/-!
# Transferring iterated directional derivatives across a pairing

If a pairing `f` moves a single directional derivative from its first argument to its second at
the cost of a sign, `f (∂_v x) y = -f x (∂_v y)`, then it moves an iterated derivative of order
`n` across with sign `(-1)^n`, the directions being applied in reverse order. This is the common
induction behind the duality formulas for iterated derivatives of distributions and tempered
distributions.

## Main results

* `LineDeriv.pairing_iteratedLineDerivOp`:
  `f (∂^m x) y = (-1)^n • f x (∂^m' y)`, with the directions `m'` of `m` in reverse order.
-/

public section

namespace LineDeriv

open scoped LineDeriv

variable {R V E F M : Type*} [Ring R] [AddCommGroup M] [Module R M]
  [LineDeriv V E E] [LineDeriv V F F]

/-- **Iterated derivatives across a pairing.** If `f` transfers one directional derivative from
its first argument to its second with a sign, it transfers an iterated derivative of order `n`
with sign `(-1)^n`, the directions being applied in reverse order. -/
theorem pairing_iteratedLineDerivOp (f : E → F → M)
    (hf : ∀ (v : V) (x : E) (y : F), f (∂_{v} x) y = -f x (∂_{v} y)) {n : ℕ} (m : Fin n → V)
    (x : E) (y : F) :
    f (∂^{m} x) y = (-1 : R) ^ n • f x (∂^{m ∘ Fin.rev} y) := by
  induction n generalizing y with
  | zero => simp
  | succ n ih =>
    rw [iteratedLineDerivOp_succ_left, hf, ih, iteratedLineDerivOp_succ_right, pow_succ,
      mul_smul, neg_one_smul, ← smul_neg]
    simp [Fin.init_def, Fin.tail_def, Function.comp_def, Fin.rev_castSucc]

end LineDeriv
