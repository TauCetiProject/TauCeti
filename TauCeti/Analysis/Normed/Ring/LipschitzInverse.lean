/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Algebra.Ring.Invertible

/-!
# Lipschitz families of inverses in a seminormed ring

By the resolvent identity `a⁻¹ - b⁻¹ = a⁻¹ (b - a) b⁻¹` (`Ring.inverse_sub_inverse`), inversion is
Lipschitz on the units whose inverses are uniformly bounded, so inverting a Lipschitz family of such
units gives a Lipschitz family. For continuous linear operators this applies to the inverse Jacobian
`DΦ(x)⁻¹` of a map with Lipschitz derivative, as needed for coefficients transformed by a change of
variables.

## Main results

* `Ring.lipschitzOnWith_inverse`: `Ring.inverse` is `M²`-Lipschitz on the units whose inverses
  have norm at most `M`.
* `LipschitzOnWith.inverse`: if `f` is `K`-Lipschitz on `s` with unit values whose
  inverses have norm at most `M`, then `x ↦ (f x)⁻¹` is `M² K`-Lipschitz on `s`.
-/

public section

open scoped NNReal

variable {R : Type*} [SeminormedRing R]

namespace Ring

/-- `Ring.inverse` is `M²`-Lipschitz on the units whose inverses have norm at most `M`. -/
theorem lipschitzOnWith_inverse (M : ℝ≥0) :
    LipschitzOnWith (M ^ 2) (Ring.inverse : R → R) {a | IsUnit a ∧ ‖Ring.inverse a‖ ≤ M} := by
  refine LipschitzOnWith.of_dist_le_mul fun a ha b hb ↦ ?_
  rw [dist_eq_norm, Ring.inverse_sub_inverse (iff_of_true ha.1 hb.1), dist_eq_norm', NNReal.coe_pow]
  calc _ ≤ ‖Ring.inverse a‖ * ‖b - a‖ * ‖Ring.inverse b‖ := norm_mul₃_le
    _ ≤ M * ‖b - a‖ * M := by gcongr; exacts [ha.2, hb.2]
    _ = _ := by ring

end Ring

namespace LipschitzOnWith

/-- If `f` is `K`-Lipschitz on `s` with unit values whose inverses have norm at most `M`, then
`x ↦ (f x)⁻¹` is `M² K`-Lipschitz on `s`. -/
theorem inverse {X : Type*} [PseudoEMetricSpace X] {f : X → R} {s : Set X}
    {K M : ℝ≥0} (hf : LipschitzOnWith K f s) (hunit : ∀ x ∈ s, IsUnit (f x))
    (hM : ∀ x ∈ s, ‖Ring.inverse (f x)‖ ≤ M) :
    LipschitzOnWith (M ^ 2 * K) (fun x ↦ Ring.inverse (f x)) s :=
  (Ring.lipschitzOnWith_inverse M).comp hf fun x hx ↦ ⟨hunit x hx, hM x hx⟩

end LipschitzOnWith
