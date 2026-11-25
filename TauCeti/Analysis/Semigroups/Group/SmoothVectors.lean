/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Semigroups.Generator.SmoothVectors
public import TauCeti.Analysis.Semigroups.Group.Basic

/-!
# Smooth vectors of a strongly continuous group

For a C₀-group `U` on a real Banach space, a vector `x` is a smooth vector of the forward
semigroup `U.toSemigroup` (it lies in every iterated domain of the generator) exactly when its
two-sided orbit `t ↦ U t x` is a smooth map `ℝ → X`. Smoothness of the forward orbit on `[0, ∞)`
propagates to all of `ℝ`: on `(s, ∞)` the orbit is `t ↦ U s (U (t - s) x)`, the forward orbit
translated by `s` followed by the continuous linear map `U s`.

## Main results

* `TauCeti.Semigroups.StronglyContinuousGroup.isSmoothVector_toSemigroup_iff_contDiff`: smooth
  vectors of the forward semigroup are the vectors with a smooth two-sided orbit.
-/

public section

noncomputable section

open Set
open scoped ContDiff Topology

namespace TauCeti.Semigroups.StronglyContinuousGroup

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Smooth vectors of a C₀-group.** A vector is a smooth vector of the forward semigroup of a
C₀-group exactly when its two-sided orbit `t ↦ U t x` is smooth on `ℝ`. -/
theorem isSmoothVector_toSemigroup_iff_contDiff (U : StronglyContinuousGroup X) (x : X) :
    U.toSemigroup.IsSmoothVector x ↔ ContDiff ℝ ∞ fun t : ℝ => U t x := by
  rw [StronglyContinuousSemigroup.isSmoothVector_iff_contDiffOn_realOperator]
  have heq : EqOn (fun t : ℝ => U.toSemigroup.realOperator t x) (fun t => U t x) (Ici 0) :=
    fun t ht => by simp only [U.toSemigroup_realOperator_of_nonneg (mem_Ici.mp ht)]
  rw [contDiffOn_congr heq]
  refine ⟨fun h => contDiff_iff_contDiffAt.mpr fun t₀ => ?_, fun h => h.contDiffOn⟩
  -- On `(t₀ - 1, ∞)` the orbit is the forward orbit translated by `t₀ - 1`, followed by
  -- `U (t₀ - 1)`.
  have htr : ContDiffOn ℝ ∞ (fun t : ℝ => U (t₀ - 1) (U (t - (t₀ - 1)) x)) (Ioi (t₀ - 1)) :=
    (U (t₀ - 1)).contDiff.comp_contDiffOn <| h.comp (contDiff_id.sub contDiff_const).contDiffOn
      fun t ht => sub_nonneg.mpr (le_of_lt ht)
  refine (htr.congr fun t _ => ?_).contDiffAt (Ioi_mem_nhds (by linarith))
  rw [← U.map_add_apply, add_sub_cancel]

end TauCeti.Semigroups.StronglyContinuousGroup
