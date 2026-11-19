/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

/-!
# A common small radius

Two positive radii and a positive gap admit a common smaller positive radius whose double
square fits in the gap (`TauCeti.exists_pos_lt_lt_two_mul_sq_lt`).
-/

public section

open Filter Topology

namespace TauCeti

/-- Two positive radii and a positive gap admit a common smaller positive radius whose double
square fits in the gap. -/
theorem exists_pos_lt_lt_two_mul_sq_lt {R₀ R₁ d : ℝ} (hR₀ : 0 < R₀) (hR₁ : 0 < R₁) (hd : 0 < d) :
    ∃ r, (r < R₀ ∧ r < R₁ ∧ 2 * r ^ 2 < d) ∧ 0 < r :=
  (((gt_mem_nhds hR₀).and ((gt_mem_nhds hR₁).and
    ((by fun_prop : Continuous fun r : ℝ ↦ 2 * r ^ 2).tendsto 0 |>.eventually_lt_const
      (by simpa using hd)))).filter_mono nhdsWithin_le_nhds |>.and
    self_mem_nhdsWithin).exists (f := 𝓝[>] (0 : ℝ))

end TauCeti
