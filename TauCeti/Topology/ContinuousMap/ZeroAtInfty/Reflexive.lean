/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.Basis
public import TauCeti.Analysis.Normed.Lp.Dual
public import TauCeti.Analysis.Normed.Module.Bases.Basic
public import TauCeti.Analysis.Normed.Module.Bases.Reflexive
public import TauCeti.Topology.Algebra.Module.WeakSpace
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Basis
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Dual

/-!
# `c₀` is not reflexive

Over real or complex scalars, on an infinite discrete index type `ι`, the space `C₀(ι, 𝕜)` of
families vanishing at infinity is not reflexive. Through the duality `C₀(ι, 𝕜)* = ℓ¹`, summing the
coordinates of a functional is a continuous functional on the dual. It takes the value `1` on
every coordinate evaluation, so it is not evaluation at an element of `C₀(ι, 𝕜)`.

The unit coordinate vectors tend to zero weakly, but not in norm, along the cofinite filter: every
functional on `C₀(ι, 𝕜)` has summable coordinate values, while every coordinate vector has norm
`1`. For `ι = ℕ` the coordinate basis is shrinking, since its coordinate functionals correspond to
the unit vectors of `ℓ¹`. By James's basis criterion it is therefore not boundedly complete.

## Main results

* `ZeroAtInftyContinuousMap.not_surjective_inclusionInDoubleDual`: `c₀` is not reflexive.
* `ZeroAtInftyContinuousMap.tendsto_toWeakSpace_single_one_cofinite`: the unit coordinate vectors
  are weakly null.
* `ZeroAtInftyContinuousMap.not_tendsto_single_cofinite` (in `ZeroAtInfty.Discrete`): they are
  not norm null.
* `ZeroAtInftyContinuousMap.isShrinking_toSchauderBasis_unconditionalBasis` and
  `ZeroAtInftyContinuousMap.not_isBoundedlyComplete_toSchauderBasis_unconditionalBasis`: the
  coordinate basis of `c₀` is shrinking but not boundedly complete.

## References

* F. Albiac and N. J. Kalton, *Topics in Banach Space Theory*, Chapters 1 and 3.
* R. E. Megginson, *An Introduction to Banach Space Theory*, §4.4.
-/

public section

noncomputable section

open Filter Function NormedSpace Set Topology
open scoped ENNReal ZeroAtInfty

namespace ZeroAtInftyContinuousMap

variable {𝕜 ι : Type*} [TopologicalSpace ι] [DiscreteTopology ι]

variable [RCLike 𝕜]

/-- The unit coordinate vectors of `C₀(ι, 𝕜)` tend weakly to zero along the cofinite filter. -/
theorem tendsto_toWeakSpace_single_one_cofinite [DecidableEq ι] :
    Tendsto (fun i : ι ↦ toWeakSpace 𝕜 C₀(ι, 𝕜) (single i 1)) cofinite
      (𝓝 (toWeakSpace 𝕜 C₀(ι, 𝕜) 0)) := by
  refine TauCeti.tendsto_toWeakSpace_iff_forall_eval_tendsto.2 fun Λ ↦ ?_
  simpa [← dualEquiv_symm_apply] using
    (lp.memℓp ((dualEquiv 𝕜 ι).symm Λ)).summable_of_one.tendsto_cofinite_zero

/-- On an infinite discrete index type, `C₀(ι, 𝕜)` is not reflexive. -/
theorem not_surjective_inclusionInDoubleDual [Infinite ι] :
    ¬ Surjective (inclusionInDoubleDual 𝕜 C₀(ι, 𝕜)) := by
  classical
  -- The functional `Λ ↦ ∑' i, Λ (single i 1)` takes the value `1` on every evaluation.
  let Φ : StrongDual 𝕜 (StrongDual 𝕜 C₀(ι, 𝕜)) :=
    (lp.dualOneEquiv 𝕜 ι 1).comp (dualEquiv 𝕜 ι).symm.toContinuousLinearEquiv.toContinuousLinearMap
  rintro hJ
  obtain ⟨f, hf⟩ := hJ Φ
  have hone (i : ι) : f i = 1 := by
    simpa [Φ, lp.infty_coeFn_one] using congrArg (fun Ψ ↦ Ψ (evalCLM 𝕜 i)) hf
  have hlim := f.tendsto_cofinite
  rw [(funext hone : ⇑f = fun _ ↦ 1)] at hlim
  exact one_ne_zero (tendsto_const_nhds_iff.1 hlim)

/-- The coordinate basis of `c₀` is shrinking: the coordinate evaluations span a dense subspace
of the dual. -/
theorem isShrinking_toSchauderBasis_unconditionalBasis :
    (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜)).toSchauderBasis.IsShrinking := by
  -- Under `C₀(ℕ, 𝕜)* = ℓ¹` the coordinate evaluations are the coordinate basis of `ℓ¹`.
  have hrange : range (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜)).toSchauderBasis.coord =
      dualEquiv 𝕜 ℕ '' range (lp.unconditionalBasis (ι := ℕ) (𝕜 := 𝕜) ENNReal.one_ne_top) := by
    rw [← range_comp]
    congr 1
    ext1 i
    simp [← dualEquiv_symm_evalCLM]
  rw [SchauderBasis.isShrinking_iff, ← Submodule.dense_iff_topologicalClosure_eq_top, hrange]
  exact ((dualEquiv 𝕜 ℕ).surjective.denseRange.dense_image (dualEquiv 𝕜 ℕ).continuous
    (GeneralSchauderBasis.dense_span _)).mono
    (Submodule.image_span_subset_span (dualEquiv 𝕜 ℕ).toLinearEquiv.toLinearMap _)

/-- The coordinate basis of `c₀` is not boundedly complete. -/
theorem not_isBoundedlyComplete_toSchauderBasis_unconditionalBasis :
    ¬ (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜)).toSchauderBasis.IsBoundedlyComplete := fun h ↦
  -- A shrinking and boundedly complete basis would make `c₀` reflexive.
  not_surjective_inclusionInDoubleDual <| (unconditionalBasis (ι := ℕ) (𝕜 := 𝕜)).toSchauderBasis
    |>.surjective_inclusionInDoubleDual_of_isShrinking_of_isBoundedlyComplete
      isShrinking_toSchauderBasis_unconditionalBasis h

end ZeroAtInftyContinuousMap
