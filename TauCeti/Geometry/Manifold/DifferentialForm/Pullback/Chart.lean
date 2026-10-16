/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.ExtDeriv
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Analysis.Calculus.ContDiff.ContinuousAlternatingMap

/-!
# Coordinate expressions of actual manifold pullback

The coordinate expression of a pullback uses the within-range derivative of the map composed
with the inverse source chart. This is the actual manifold chain rule, including boundary
points, and supplies the coefficient transport used in interval and product comparisons.
-/

public section

noncomputable section

open Set
open scoped Manifold Topology

namespace TauCeti.RoughForm

variable {E H M E' H' M' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- The actual pullback's coefficient in a preferred source chart is obtained from the
within-range derivative of the composite with its inverse chart. -/
theorem inChartAt_mpullback (ω : RoughForm I' M' F k) (f : M → M') (α : M) {z : E}
    (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I I' f ((extChartAt I α).symm z)) :
    (mpullback I I' f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        (mfderivWithin 𝓘(ℝ, E) I' (f ∘ (extChartAt I α).symm) (range I) z) := by
  have hd := mfderiv_comp_mfderivWithin (I := 𝓘(ℝ, E)) (I' := I) (I'' := I') z hf
    (mdifferentiableWithinAt_extChartAt_symm hz)
    (I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range α hz)
      |>.uniqueMDiffWithinAt)
  ext v
  rw [inChartAt_apply, mpullback_apply]
  have he := congrArg (fun L : E →L[ℝ] TangentSpace I' (f ((extChartAt I α).symm z)) ↦
    ω (f ((extChartAt I α).symm z)) (fun i ↦ L (v i))) hd
  exact he.symm

end TauCeti.RoughForm

namespace TauCeti.RoughForm

variable {E H M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- For a model-valued map, actual pullback coefficients use its ordinary within-range
Fréchet derivative, with the canonical model tangent identification made explicit. -/
theorem inChartAt_mpullback_modelSpace (ω : RoughForm 𝓘(ℝ, X) X F k) (f : M → X)
    (α : M) {z : E} (hz : z ∈ (extChartAt I α).target)
    (hf : MDifferentiableAt I 𝓘(ℝ, X) f ((extChartAt I α).symm z)) :
    (mpullback I 𝓘(ℝ, X) f ω).inChartAt α z =
      (ω (f ((extChartAt I α).symm z))).compContinuousLinearMap
        ((NormedSpace.fromTangentSpace (𝕜 := ℝ)
          (f ((extChartAt I α).symm z))).symm.toContinuousLinearMap.comp
          (fderivWithin ℝ (f ∘ (extChartAt I α).symm) (range I) z)) := by
  rw [inChartAt_mpullback ω f α hz hf, mfderivWithin_eq_fderivWithin]
  rfl

end TauCeti.RoughForm

namespace TauCeti

variable {E H M X F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

/-- Pullback of a Cn form on a normed model along a C(n+1) manifold map is Cn, in every degree.
Regularity follows from the actual coordinate chain rule and regularity of its derivative. -/
theorem IsSmoothForm.mpullback_modelSpace {n : WithTop ℕ∞} {ω : RoughForm 𝓘(ℝ, X) X F k}
    (hω : IsSmoothForm 𝓘(ℝ, X) n ω) {f : M → X}
    (hf : ContMDiff I 𝓘(ℝ, X) (n + 1) f) :
    IsSmoothForm I n (mpullback I 𝓘(ℝ, X) f ω) := by
  apply IsSmoothForm.of_contDiffWithinAt_inChartAt_self
  intro x
  let T := f ∘ (extChartAt I x).symm
  have hx : extChartAt I x x ∈ range I :=
    extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hT : ContDiffWithinAt ℝ (n + 1) T (range I) (extChartAt I x x) := by
    have hc := (contMDiffAt_iff.mp (hf x)).2
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp] using hc
  have hcoord : ContDiffAt ℝ n (ω.inChartAt (f x)) (f x) := by
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      modelWithCornersSelf_coe, range_id, contDiffWithinAt_univ, id_eq] using
      hω.contDiffWithinAt_inChartAt_self (f x)
  have hC : ContDiffWithinAt ℝ n (ω.inChartAt (f x) ∘ T) (range I)
      (extChartAt I x x) := by
    apply hcoord.comp_contDiffWithinAt_of_eq (extChartAt I x x)
      (hT.of_le (by simp))
    simp only [T, Function.comp_apply, extChartAt_to_inv]
  have hD : ContDiffWithinAt ℝ n (fderivWithin ℝ T (range I)) (range I)
      (extChartAt I x x) := hT.fderivWithin_right I.uniqueDiffOn (by simp) hx
  have hp := ((ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (ι := Fin k) (G := F) n).comp_contDiffWithinAt hD).clm_apply hC
  have heq : (mpullback I 𝓘(ℝ, X) f ω).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      fun z ↦ (ω.inChartAt (f x) (T z)).compContinuousLinearMap
        (fderivWithin ℝ T (range I) z) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with z hz
    rw [RoughForm.inChartAt_mpullback_modelSpace ω f x hz
      ((hf _).mdifferentiableAt (by simp)), RoughForm.inChartAt_modelSpace]
    rfl
  exact hp.congr_of_eventuallyEq heq (heq.self_of_nhdsWithin hx)

end TauCeti
