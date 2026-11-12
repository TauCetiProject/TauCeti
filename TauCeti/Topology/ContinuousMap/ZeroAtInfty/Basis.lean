/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Discrete
public import Mathlib.Analysis.Normed.Module.Bases

/-!
# The coordinate basis of `c₀`

On a discrete index type `ι`, the unit coordinate vectors form an unconditional Schauder
basis of `C₀(ι, 𝕜)`. The coordinates are evaluations, and each finite projection retains
the selected coordinates and has norm at most one. These projections give finite-rank
contractive approximations of the identity.

The construction uses `ZeroAtInftyContinuousMap.hasSum_smul_single_one`, the coordinate
expansion in the native space of continuous functions vanishing at infinity. No completeness
or countability hypothesis is needed.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapter 1.
-/

public section

open scoped ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {ι 𝕜 : Type*} [DecidableEq ι] [TopologicalSpace ι] [DiscreteTopology ι]
  [NontriviallyNormedField 𝕜]

/-- The unit coordinate vectors are an unconditional Schauder basis of `c₀` on a discrete
index type. -/
noncomputable def unconditionalBasis : UnconditionalSchauderBasis ι 𝕜 C₀(ι, 𝕜) where
  basis i := single i 1
  coord := evalCLM 𝕜
  ortho i j := by simp [Pi.single_apply]
  expansion x := by simpa only [evalCLM_apply] using hasSum_smul_single_one x

/-- The basis vectors are the unit coordinate vectors. -/
@[simp]
theorem unconditionalBasis_apply (i : ι) :
    unconditionalBasis (𝕜 := 𝕜) i = single i 1 := (rfl)

/-- The coordinate functionals of the coordinate basis are evaluation maps. -/
@[simp]
theorem unconditionalBasis_coord (i : ι) :
    (unconditionalBasis (𝕜 := 𝕜)).coord i = evalCLM 𝕜 i := (rfl)

/-- A finite basis projection retains precisely its selected coordinates. -/
theorem unconditionalBasis_proj_apply (s : Finset ι) (x : C₀(ι, 𝕜)) (i : ι) :
    unconditionalBasis.proj s x i = if i ∈ s then x i else 0 := by
  classical
  rw [GeneralSchauderBasis.proj_apply]
  simpa only [unconditionalBasis_coord, evalCLM_apply, unconditionalBasis_apply,
    smul_single_one] using sum_single_apply x s i

/-- All finite coordinate projections of `c₀` are contractions. -/
theorem norm_unconditionalBasis_proj_le (s : Finset ι) :
    ‖(unconditionalBasis (𝕜 := 𝕜)).proj s‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x ↦ ?_
  rw [one_mul]
  refine (norm_le (norm_nonneg x)).2 fun i ↦ ?_
  rw [unconditionalBasis_proj_apply]
  split_ifs
  · exact norm_coe_le_norm x i
  · simp

end ZeroAtInftyContinuousMap
