/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.EMetricSpace.Lipschitz
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Normed.MulAction

/-!
# Lipschitz constants of multiplication and commutators in seminormed rings

In a nonunital seminormed ring `A`, left and right multiplication by a fixed element `a : A` are
`‖a‖₊`-Lipschitz (`TauCeti.lipschitzWith_mul_left` and `TauCeti.lipschitzWith_mul_right`),
specializing `lipschitzWith_smul` via `NonUnitalSeminormedRing.isBoundedSMul` and
`NonUnitalSeminormedRing.isBoundedSMulOpposite` (and dual to `antilipschitzWith_mul_left` and
`antilipschitzWith_mul_right` for strictly multiplicative norms). Subtracting the two gives
`(2 * ‖a‖₊)`- and `(2 * ‖b‖₊)`-Lipschitz bounds for the commutator maps `b ↦ a * b - b * a` and
`a ↦ a * b - b * a` (`TauCeti.lipschitzWith_commutator_left` and
`TauCeti.lipschitzWith_commutator_right`).
-/

public section

open scoped NNReal

namespace TauCeti

variable {A : Type*} [NonUnitalSeminormedRing A]

/-- Left multiplication `(a * ·)` in a seminormed ring is `‖a‖₊`-Lipschitz. -/
theorem lipschitzWith_mul_left (a : A) : LipschitzWith ‖a‖₊ (a * ·) := by
  rw [show (a * ·) = (a • ·) from funext fun b => (smul_eq_mul a b).symm]
  exact lipschitzWith_smul a

/-- Right multiplication `(· * a)` in a seminormed ring is `‖a‖₊`-Lipschitz. -/
theorem lipschitzWith_mul_right (a : A) : LipschitzWith ‖a‖₊ (· * a) := by
  rw [← MulOpposite.nnNorm_op a, show (· * a) = (MulOpposite.op a • ·) from
    funext fun b => (MulOpposite.smul_eq_mul_unop (MulOpposite.op a) b).symm]
  exact lipschitzWith_smul (MulOpposite.op a)

/-- Taking the commutator `b ↦ a * b - b * a` with a fixed left factor `a` in a seminormed ring is
`(2 * ‖a‖₊)`-Lipschitz. -/
theorem lipschitzWith_commutator_left (a : A) :
    LipschitzWith (2 * ‖a‖₊) (fun b => a * b - b * a) :=
  two_mul ‖a‖₊ ▸ (lipschitzWith_mul_left a).sub (lipschitzWith_mul_right a)

/-- Taking the commutator `a ↦ a * b - b * a` with a fixed right factor `b` in a seminormed ring is
`(2 * ‖b‖₊)`-Lipschitz. -/
theorem lipschitzWith_commutator_right (b : A) :
    LipschitzWith (2 * ‖b‖₊) (fun a => a * b - b * a) :=
  two_mul ‖b‖₊ ▸ (lipschitzWith_mul_right b).sub (lipschitzWith_mul_left b)

end TauCeti
