/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Basic
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The actual tangent map of closed-ball inclusion

Closed-ball charts are restrictions of inversion charts. Their inverse derivatives are
invertible even at the sphere, giving the actual inclusion a tangent equivalence everywhere.
-/

public section

noncomputable section

open Set Metric EuclideanGeometry
open scoped Manifold ContDiff InnerProductSpace

namespace TauCeti

variable {n : ℕ} [NeZero n] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = n)]

private theorem exists_subtypeValClosedBallTangentEquiv (x : closedBall (0 : V) 1) :
    ∃ e : TangentSpace (𝓡∂ n) x ≃L[ℝ] V,
      e.toContinuousLinearMap =
        (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : V)).toContinuousLinearMap.comp
          (mfderiv (𝓡∂ n) 𝓘(ℝ, V) Subtype.val x) := by
  obtain ⟨φ, hφ, hchart⟩ := exists_chartAt_closedBall_eq (n := n) x
  let z := extChartAt (𝓡∂ n) x x
  let c : EuclideanSpace ℝ (Fin n) := -EuclideanSpace.single 0 1
  have hzrange : z ∈ range (𝓡∂ n) := extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hz0 : 0 ≤ z 0 := by
    simpa only [range_modelWithCornersEuclideanHalfSpace, mem_ofPred_eq] using hzrange
  have hzc : z ≠ c := by
    intro he
    have hc0 : c 0 = -1 := by simp [c]
    rw [he, hc0] at hz0
    norm_num at hz0
  let L := (inversionFDerivEquiv c z √2 (by positivity) hzc).trans
    φ.symm.toContinuousLinearEquiv
  have hd : HasFDerivAt (fun y ↦ φ.symm (inversion c √2 y)) L.toContinuousLinearMap z :=
    φ.symm.toContinuousLinearEquiv.hasFDerivAt.comp z
      (hasFDerivAt_inversionFDerivEquiv c z √2 (by positivity) hzc)
  have heq : EqOn (Subtype.val ∘ (extChartAt (𝓡∂ n) x).symm)
      (fun y ↦ φ.symm (inversion c √2 y)) (range (𝓡∂ n)) := by
    intro y hy
    rw [range_modelWithCornersEuclideanHalfSpace] at hy
    simp [hchart, extChartAt, c, modelWithCornersEuclideanHalfSpace_symm_apply_of_le hy,
      closedBallChart_symm_apply_coe]
  have hdiff := (contMDiff_subtypeVal_closedBall (n := n) (k := 1)).mdifferentiable one_ne_zero x
  refine ⟨(tangentSpaceCastModel (𝓡∂ n) x).trans L, ?_⟩
  rw [hdiff.mfderiv]
  -- The normed-target tangent casts cancel, leaving composition with the source tangent cast.
  change L.toContinuousLinearMap.comp (tangentSpaceCastModel (𝓡∂ n) x).toContinuousLinearMap = _
  have hfw : fderivWithin ℝ (writtenInExtChartAt (𝓡∂ n) 𝓘(ℝ, V) x Subtype.val)
      (range (𝓡∂ n)) z = L.toContinuousLinearMap := by
    rw [writtenInExtChartAt, extChartAt_model_space_eq_id]
    simp only [PartialEquiv.refl_coe, Function.id_comp]
    exact ((hd.hasFDerivWithinAt.congr heq (heq hzrange)).fderivWithin
      ((𝓡∂ n).uniqueDiffOn z hzrange))
  rw [hfw]
  ext v
  rfl

/-- The actual inclusion derivative of a closed unit ball is an invertible tangent map,
including at every point of its sphere boundary. -/
def subtypeValClosedBallTangentEquiv (x : closedBall (0 : V) 1) :
    TangentSpace (𝓡∂ n) x ≃L[ℝ] V :=
  (exists_subtypeValClosedBallTangentEquiv (n := n) x).choose

/-- The tangent equivalence is precisely the actual inclusion derivative after the canonical
normed-model tangent identification. -/
@[simp] theorem subtypeValClosedBallTangentEquiv_toContinuousLinearMap (x : closedBall (0 : V) 1) :
    (subtypeValClosedBallTangentEquiv (n := n) x).toContinuousLinearMap =
      (NormedSpace.fromTangentSpace (𝕜 := ℝ) (x : V)).toContinuousLinearMap.comp
        (mfderiv (𝓡∂ n) 𝓘(ℝ, V) Subtype.val x) :=
  (exists_subtypeValClosedBallTangentEquiv (n := n) x).choose_spec

end TauCeti
