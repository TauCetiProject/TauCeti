/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic

/-!
# Actions of groups with zero

The scalar rescaling identity `TauCeti.div_mul_smul_smul_cancel_left` cancels a nonzero factor
in the denominator against a scalar action, including when the remaining denominator is zero.
-/

public section

namespace TauCeti

/-- Rescaling `k • v` by `a / (k * b)` is rescaling `v` by `a / b`. -/
theorem div_mul_smul_smul_cancel_left {K M : Type*} [GroupWithZero K] [MulAction K M]
    {k : K} (hk : k ≠ 0) (a b : K) (v : M) :
    (a / (k * b)) • k • v = (a / b) • v := by
  rw [smul_smul, div_mul_eq_div_div_swap, div_mul_cancel₀ _ hk]

end TauCeti
