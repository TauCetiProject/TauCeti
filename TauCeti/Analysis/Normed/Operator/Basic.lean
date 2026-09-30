/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.SpecificLimits.Normed
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Basic facts about bounded operators

This file records a shared uniform-bound lemma for continuous linear maps. It lets an evaluation
`T i (g i)` pass to the limit when the operators `T i` are eventually uniformly bounded, their
values at the limiting argument converge, and the arguments `g i` converge. In particular, it
supplies the common continuity step for
`StronglyContinuousSemigroup.tendsto_realOperator_apply` and
`StronglyContinuousGroup.tendsto_apply`.

It also records the Neumann-series criterion in the form of Mathlib's
`ContinuousLinearMap.IsInvertible`: on a Banach space, `id - T` is invertible when `‖T‖ < 1`.
This is how the linearization of a contraction's fixed-point equation is shown to be invertible
when the implicit function theorem is applied to it.
-/

public section

open scoped Topology
open Filter

namespace TauCeti

variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]


/-- If `T i` is eventually uniformly bounded, `T i z` tends to `w`, and `g i` tends to `z`, then
the moving evaluations `T i (g i)` tend to `w`. -/
theorem _root_.ContinuousLinearMap.tendsto_apply_of_eventually_norm_le {ι : Type*} {l : Filter ι}
    {T : ι → X →L[𝕜] Y} {C : ℝ} {g : ι → X} {z : X} {w : Y}
    (hT : ∀ᶠ i in l, ‖T i‖ ≤ C) (hz : Tendsto (fun i => T i z) l (𝓝 w))
    (hg : Tendsto g l (𝓝 z)) : Tendsto (fun i => T i (g i)) l (𝓝 w) := by
  have hmove : Tendsto (fun i => T i (g i - z)) l (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun i => C * ‖g i - z‖) ?_ ?_
    · filter_upwards [hT] with i hi
      exact (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _))
    · simpa using (tendsto_iff_norm_sub_tendsto_zero.mp hg).const_mul C
  have hsplit : ∀ i, T i (g i) = T i (g i - z) + T i z := fun i => by
    rw [← ContinuousLinearMap.map_add, sub_add_cancel]
  simpa using (hmove.add hz).congr fun i => (hsplit i).symm

/-- **The Neumann series criterion.** On a Banach space, the identity minus an operator of norm
less than `1` is invertible. -/
theorem _root_.ContinuousLinearMap.isInvertible_id_sub_of_norm_lt_one [CompleteSpace X]
    {T : X →L[𝕜] X} (hT : ‖T‖ < 1) : (ContinuousLinearMap.id 𝕜 X - T).IsInvertible := by
  obtain ⟨u, hu⟩ := isUnit_one_sub_of_norm_lt_one hT
  rw [← ContinuousLinearMap.one_def, ← hu]
  exact .of_inverse (g := (u⁻¹ : Units _)) (by rw [← ContinuousLinearMap.mul_def, u.mul_inv,
    ContinuousLinearMap.one_def]) (by rw [← ContinuousLinearMap.mul_def, u.inv_mul,
    ContinuousLinearMap.one_def])

end TauCeti

end
