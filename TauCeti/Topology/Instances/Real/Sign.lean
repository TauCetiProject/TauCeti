/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Real.Sign
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-!
# Local constancy of the real sign

Away from the origin the real sign function is locally constant
(`Real.eventually_sign_eq_nhds`): near a negative point it is `-1`, near a positive point `1`.
Mathlib's `continuousAt_sign_of_ne_zero` is the corresponding fact for `SignType.sign`.
-/

public section

open Set Filter Topology

namespace Real

/-- Away from the origin the real sign function is locally constant. -/
theorem eventually_sign_eq_nhds {x : ℝ} (hx : x ≠ 0) : ∀ᶠ y in 𝓝 x, sign y = sign x := by
  rcases hx.lt_or_gt with h | h
  · filter_upwards [Iio_mem_nhds h] with y hy
    rw [sign_of_neg hy, sign_of_neg h]
  · filter_upwards [Ioi_mem_nhds h] with y hy
    rw [sign_of_pos hy, sign_of_pos h]

end Real
