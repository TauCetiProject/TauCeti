/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Compatible additive group norms

Two additive group norms bounded by constant multiples of one another induce the same
uniformity. `AddGroupNorm.toNormedAddCommGroupOfUniformity` installs a new norm while retaining
the original uniformity and topology definitionally. In particular, existing completeness
and continuity proofs remain usable. This construction is shared by adapted and rounded norms.
-/

public section

open scoped NNReal Uniformity

namespace AddGroupNorm

variable {M : Type*} [NormedAddCommGroup M]

/-- An additive group norm bounded-equivalent to the original norm induces its uniformity. -/
theorem uniformity_eq_of_le (N : AddGroupNorm M) {C D : ℝ≥0}
    (h₁ : ∀ x, N x ≤ C * ‖x‖) (h₂ : ∀ x, ‖x‖ ≤ D * N x) :
    𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace := by
  let g := ‹NormedAddCommGroup M›
  let n := N.toNormedAddCommGroup
  -- Keep the original norm implicit and name the second metric explicitly.
  let := g
  have hd (x y : M) : @dist M n.toDist x y = N (-x + y) := rfl
  have hf : @UniformContinuous M M g.toUniformSpace n.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M g.toPseudoEMetricSpace n.toPseudoEMetricSpace C id
    apply @LipschitzWith.of_dist_le_mul M M g.toPseudoMetricSpace n.toPseudoMetricSpace C id
    intro x y
    simpa only [id_eq, hd, dist_eq_norm_neg_add] using h₁ (-x + y)
  have hg : @UniformContinuous M M n.toUniformSpace g.toUniformSpace id := by
    apply @LipschitzWith.uniformContinuous M M n.toPseudoEMetricSpace g.toPseudoEMetricSpace D id
    apply @LipschitzWith.of_dist_le_mul M M n.toPseudoMetricSpace g.toPseudoMetricSpace D id
    intro x y
    simpa only [id_eq, hd, dist_eq_norm_neg_add] using h₂ (-x + y)
  apply le_antisymm
  · intro s hs
    exact @uniformContinuous_def M M g.toUniformSpace n.toUniformSpace id |>.mp hf s hs
  · intro s hs
    exact @uniformContinuous_def M M n.toUniformSpace g.toUniformSpace id |>.mp hg s hs

/-- Install an additive group norm with the original uniformity and topology retained
definitionally. Thus completeness and continuity are unchanged. -/
noncomputable abbrev toNormedAddCommGroupOfUniformity (N : AddGroupNorm M)
    (h : 𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace) : NormedAddCommGroup M :=
  { N.toNormedAddCommGroup with
    toMetricSpace := N.toNormedAddCommGroup.toMetricSpace.replaceUniformity h }

/-- The compatible structure has the specified additive group norm. -/
@[simp]
theorem norm_toNormedAddCommGroupOfUniformity (N : AddGroupNorm M)
    (h : 𝓤 M = @uniformity M N.toNormedAddCommGroup.toUniformSpace) (x : M) :
    @norm M (N.toNormedAddCommGroupOfUniformity h).toNorm x = N x := (rfl)

end AddGroupNorm
