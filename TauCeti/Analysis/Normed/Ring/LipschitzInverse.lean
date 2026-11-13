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
# Lipschitz families of inverses in a normed ring

By the resolvent identity `a⁻¹ - b⁻¹ = a⁻¹ (b - a) b⁻¹` (`Ring.inverse_sub_inverse`), inverting a
Lipschitz family of units whose inverses are uniformly bounded gives a Lipschitz family. For
continuous linear operators this applies to the inverse Jacobian `DΦ(x)⁻¹` of a map with Lipschitz
derivative, as needed for coefficients transformed by a change of variables.

## Main results

* `LipschitzOnWith.inverse`: if `f` is `K`-Lipschitz on `s` with unit values whose
  inverses have norm at most `M`, then `x ↦ (f x)⁻¹` is `M² K`-Lipschitz on `s`.
-/

public section

open scoped NNReal

namespace LipschitzOnWith

variable {R : Type*} [NormedRing R]

/-- If `f` is `K`-Lipschitz on `s` with unit values whose inverses have norm at most `M`, then
`x ↦ (f x)⁻¹` is `M² K`-Lipschitz on `s`. -/
theorem inverse {X : Type*} [PseudoMetricSpace X] {f : X → R} {s : Set X}
    {K M : ℝ≥0} (hf : LipschitzOnWith K f s) (hunit : ∀ x ∈ s, IsUnit (f x))
    (hM : ∀ x ∈ s, ‖Ring.inverse (f x)‖ ≤ M) :
    LipschitzOnWith (M ^ 2 * K) (fun x ↦ Ring.inverse (f x)) s := by
  refine LipschitzOnWith.of_dist_le_mul fun x hx y hy ↦ ?_
  rw [dist_eq_norm, Ring.inverse_sub_inverse (iff_of_true (hunit x hx) (hunit y hy))]
  have hd : ‖f y - f x‖ ≤ K * dist x y := by
    rw [← dist_eq_norm, dist_comm x y]
    exact hf.dist_le_mul y hy x hx
  calc _ ≤ ‖Ring.inverse (f x)‖ * ‖f y - f x‖ * ‖Ring.inverse (f y)‖ := norm_mul₃_le
    _ ≤ M * (K * dist x y) * M := by
        gcongr
        exacts [hM x hx, hM y hy]
    _ = (M ^ 2 * K : ℝ≥0) * dist x y := by push_cast; ring

end LipschitzOnWith
