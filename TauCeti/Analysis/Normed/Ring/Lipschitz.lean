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
import TauCeti.Topology.MetricSpace.Equicontinuity

/-!
# Lipschitz constants of multiplication and commutators in seminormed rings

In a nonunital seminormed ring `A`, left and right multiplication by a fixed element `a : A` are
`‖a‖₊`-Lipschitz (`TauCeti.lipschitzWith_mul_left` and `TauCeti.lipschitzWith_mul_right`),
specializing `lipschitzWith_smul` via `NonUnitalSeminormedRing.isBoundedSMul` and
`NonUnitalSeminormedRing.isBoundedSMulOpposite` (and dual to `antilipschitzWith_mul_left` and
`antilipschitzWith_mul_right` for strictly multiplicative norms). Subtracting the two gives
`(2 * ‖a‖₊)`- and `(2 * ‖b‖₊)`-Lipschitz bounds for the commutator maps `b ↦ a * b - b * a` and
`a ↦ a * b - b * a` (`TauCeti.lipschitzWith_commutator_left` and
`TauCeti.lipschitzWith_commutator_right`). Along any filter eventually contained in the closed unit
ball, left and right multiplication are eventually `1`-Lipschitz
(`TauCeti.eventually_lipschitzWith_mul_left` and `TauCeti.eventually_lipschitzWith_mul_right`), and
the commutator maps `a ↦ e * a - a * e` are eventually `2`-Lipschitz
(`TauCeti.eventually_lipschitzWith_commutator_left`), so commutator convergence to `0` extends from
a dense subset to all of `A` (`TauCeti.tendsto_commutator_of_dense`).
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

variable {A : Type*} [NonUnitalSeminormedRing A]

/-- Left multiplication `(a * ·)` in a seminormed ring is `‖a‖₊`-Lipschitz. -/
theorem lipschitzWith_mul_left (a : A) : LipschitzWith ‖a‖₊ (a * ·) := fun x y => by
  simpa only [smul_eq_mul] using lipschitzWith_smul a x y

/-- Right multiplication `(· * a)` in a seminormed ring is `‖a‖₊`-Lipschitz. -/
theorem lipschitzWith_mul_right (a : A) : LipschitzWith ‖a‖₊ (· * a) := fun x y => by
  simpa only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, MulOpposite.nnNorm_op] using
    lipschitzWith_smul (MulOpposite.op a) x y

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

/-- If elements along a filter `l` eventually satisfy `‖e‖ ≤ 1`, then the left-multiplication maps
`(e * ·)` are eventually `1`-Lipschitz along `l`. -/
theorem eventually_lipschitzWith_mul_left {l : Filter A} (hnorm : ∀ᶠ e in l, ‖e‖ ≤ 1) :
    ∀ᶠ e in l, LipschitzWith 1 (e * ·) :=
  hnorm.mono fun e he => (lipschitzWith_mul_left e).weaken (by exact_mod_cast he)

/-- If elements along a filter `l` eventually satisfy `‖e‖ ≤ 1`, then the right-multiplication maps
`(· * e)` are eventually `1`-Lipschitz along `l`. -/
theorem eventually_lipschitzWith_mul_right {l : Filter A} (hnorm : ∀ᶠ e in l, ‖e‖ ≤ 1) :
    ∀ᶠ e in l, LipschitzWith 1 (· * e) :=
  hnorm.mono fun e he => (lipschitzWith_mul_right e).weaken (by exact_mod_cast he)

/-- If elements along a filter `l` eventually satisfy `‖e‖ ≤ 1`, then the commutator maps
`a ↦ e * a - a * e` are eventually `2`-Lipschitz along `l`. -/
theorem eventually_lipschitzWith_commutator_left {l : Filter A}
    (hnorm : ∀ᶠ e in l, ‖e‖ ≤ 1) :
    ∀ᶠ e in l, LipschitzWith 2 (fun a => e * a - a * e) :=
  hnorm.mono fun e he =>
    (lipschitzWith_commutator_left e).weaken (mul_le_of_le_one_right zero_le (by exact_mod_cast he))

/-- If elements along a filter `l` eventually satisfy `‖e‖ ≤ 1` and commutators `e * a - a * e`
tend to `0` for `a` in a dense subset `sA` of `A`, then `e * a - a * e → 0` for every `a : A`. -/
theorem tendsto_commutator_of_dense {l : Filter A} (hnorm : ∀ᶠ e in l, ‖e‖ ≤ 1)
    {sA : Set A} (hsA : Dense sA)
    (hcomm : ∀ a ∈ sA, Tendsto (fun e => e * a - a * e) l (𝓝 0)) (a : A) :
    Tendsto (fun e => e * a - a * e) l (𝓝 0) :=
  tendsto_of_mem_closure_of_lipschitzWith
    (eventually_lipschitzWith_commutator_left hnorm)
    continuousWithinAt_const hcomm (hsA a)

end TauCeti
