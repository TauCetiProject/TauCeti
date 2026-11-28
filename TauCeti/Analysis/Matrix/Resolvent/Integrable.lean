/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.Resolvent.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn

import TauCeti.Analysis.Matrix.L2OpNorm

/-!
# Integrability of Hermitian resolvent traces

At a fixed nonreal spectral parameter, the resolvent norm bound gives integrability of the
trace for continuous Hermitian families under finite measures.
-/

public section

open MeasureTheory Matrix
open scoped Matrix.Norms.L2Operator

/-- At a fixed nonreal spectral parameter, the resolvent trace of a continuous Hermitian
family is integrable with respect to any finite measure. -/
theorem Continuous.integrable_trace_inv_sub_smul_one {X n 𝕜 : Type*}
    [Fintype n] [DecidableEq n] [RCLike 𝕜] [TopologicalSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] {ρ : Measure X} [IsFiniteMeasure ρ]
    {H : X → Matrix n n 𝕜} (hc : Continuous H) (hH : ∀ x, (H x).IsHermitian)
    {z : 𝕜} (hz : RCLike.im z ≠ 0) : Integrable (fun x ↦ (H x - z • 1)⁻¹.trace) ρ := by
  refine Integrable.of_bound (hc.matrix_inv_sub_smul_one hH hz).matrix_trace.aestronglyMeasurable
    (Fintype.card n * |RCLike.im z|⁻¹) (ae_of_all _ fun x ↦ ?_)
  exact (norm_trace_le_card_mul_l2_opNorm _).trans
    (mul_le_mul_of_nonneg_left ((hH x).l2_opNorm_inv_sub_smul_one_le hz) (by positivity))
