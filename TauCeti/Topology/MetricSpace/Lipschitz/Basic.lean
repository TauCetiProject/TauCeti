/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Normed.MulAction

/-!
# Lipschitz real and scalar-valued functions

This file collects basic operations on `LipschitzWith` functions, including division by a scalar
constant in a normed division ring and the shifted positive part `t ↦ max (t - k) 0` on `ℝ`.

## Main results

* `LipschitzWith.div_const`: dividing a `K`-Lipschitz map into a normed division ring by a scalar
  `c` is `(K / ‖c‖₊)`-Lipschitz.
* `TauCeti.lipschitzWith_max_sub_const_zero`: the shifted positive part is `1`-Lipschitz.
-/

public section

open scoped NNReal

namespace TauCeti

/-- Dividing a `K`-Lipschitz map into a normed division ring by a constant `c` gives a
`(K / ‖c‖₊)`-Lipschitz map. -/
theorem _root_.LipschitzWith.div_const {α 𝕜 : Type*} [PseudoEMetricSpace α] [NormedDivisionRing 𝕜]
    {K : ℝ≥0} {f : α → 𝕜} (hf : LipschitzWith K f) (c : 𝕜) :
    LipschitzWith (K / ‖c‖₊) (fun x ↦ f x / c) := by
  simpa only [Function.comp_def, MulOpposite.nnNorm_op, nnNorm_inv, MulOpposite.smul_eq_mul_unop,
    MulOpposite.unop_op, ← div_eq_mul_inv, inv_mul_eq_div] using
    (lipschitzWith_smul (MulOpposite.op c⁻¹)).comp hf

/-- The shifted positive part `t ↦ max (t - k) 0` is `1`-Lipschitz on the real line. -/
theorem lipschitzWith_max_sub_const_zero (k : ℝ) : LipschitzWith 1 (fun t : ℝ => max (t - k) 0) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    simpa only [NNReal.coe_one, one_mul, Real.dist_eq, sub_sub_sub_cancel_right] using
      abs_max_sub_max_le_abs (x - k) (y - k) 0

end TauCeti
