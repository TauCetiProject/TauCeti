/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Green.Comparison.ExteriorDerivative
public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Chart

/-!
# Coordinate area for pulled-back planar circulation forms

For a real C² map into the complex plane, the exterior derivative of its actual pulled-back
circulation form is curl times its actual pulled-back area form. The calculation uses derivatives
within the model range, so it includes smooth boundary and corner points.
-/

public section

noncomputable section

open Set Filter
open scoped Manifold Topology

namespace TauCeti.Green

attribute [local instance] Complex.finrank_real_complex_fact

private theorem extDeriv_manifoldOneForm_inChartAt {P Q : ℂ → ℝ} {z : ℂ}
    (hP : DifferentiableAt ℝ P z) (hQ : DifferentiableAt ℝ Q z) :
    extDeriv ((manifoldOneForm P Q).inChartAt z) z =
      curl P Q z • Complex.orientation.volumeFormL := by
  have h := DifferentiableAt.mextDeriv_manifoldOneForm_eq_smul_area hP hQ
  rw [mextDeriv_def, extChartAt_model_space_eq_id] at h
  simp only [modelWithCornersSelf_coe, range_id, PartialEquiv.refl_coe, id_eq,
    extDerivWithin_univ] at h
  rw [← RoughForm.inChartAt_extChartAt_self manifoldAreaForm z,
    manifoldAreaForm_inChartAt] at h
  exact h

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 2 M]

/-- The actual exterior derivative of a pulled-back planar circulation form is the coordinate
curl times the actual pulled-back area form, including at boundary and corner points. -/
theorem _root_.ContMDiff.mextDeriv_mpullback_manifoldOneForm_apply {f : M → ℂ} {P Q : ℂ → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) 2 f) (x : M)
    (hP : DifferentiableAt ℝ P (f x)) (hQ : DifferentiableAt ℝ Q (f x)) :
    mextDeriv (mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) x =
      curl P Q (f x) • mpullback I 𝓘(ℝ, ℂ) f manifoldAreaForm x := by
  let T := f ∘ (extChartAt I x).symm
  let z := extChartAt I x x
  have hz : z ∈ range I := extChartAt_target_subset_range x (mem_extChartAt_target x)
  have hT : ContDiffWithinAt ℝ 2 T (range I) z := by
    have hc := (contMDiffAt_iff.mp (hf x)).2
    simpa only [extChartAt_model_space_eq_id, PartialEquiv.refl_coe, Function.id_comp]
      using hc
  have heq : (mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)).inChartAt x =ᶠ[𝓝[range I] z]
      fun y ↦ ((manifoldOneForm P Q).inChartAt (f x) (T y)).compContinuousLinearMap
        (fderivWithin ℝ T (range I) y) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin (I := I) x] with y hy
    rw [RoughForm.inChartAt_mpullback_modelSpace _ f x hy
      ((hf _).mdifferentiableAt (by norm_num)), RoughForm.inChartAt_modelSpace]
    rfl
  have hTx : T z = f x := by simp only [T, z, Function.comp_apply, extChartAt_to_inv]
  have hω : DifferentiableWithinAt ℝ ((manifoldOneForm P Q).inChartAt (f x))
      univ (T z) := by
    rw [hTx]
    exact (differentiableAt_manifoldOneForm_inChartAt (f x) hP hQ).differentiableWithinAt
  have hd := extDerivWithin_pullback (f := T) (x := z) hω
    hT (by norm_num : minSmoothness ℝ 2 ≤ (2 : WithTop ℕ∞)) I.uniqueDiffOn
    (I.range_subset_closure_interior hz) hz (mapsTo_univ T (range I))
  rw [mextDeriv_def, heq.extDerivWithin_eq_of_mem hz, hd, extDerivWithin_univ, hTx,
    extDeriv_manifoldOneForm_inChartAt hP hQ]
  rw [← RoughForm.inChartAt_extChartAt_self
    (mpullback I 𝓘(ℝ, ℂ) f manifoldAreaForm) x,
    RoughForm.inChartAt_mpullback_modelSpace _ f x (mem_extChartAt_target x)
      ((hf _).mdifferentiableAt (by norm_num))]
  ext v
  -- Evaluate the composed alternating maps on v and identify the model tangent fiber with ℂ.
  change curl P Q (f x) • Complex.orientation.volumeFormL
      (fun i ↦ fderivWithin ℝ T (range I) z (v i)) =
    curl P Q (f x) • manifoldAreaForm (f ((extChartAt I x).symm (extChartAt I x x)))
      (fun i ↦ (NormedSpace.fromTangentSpace (𝕜 := ℝ)
        (f ((extChartAt I x).symm (extChartAt I x x)))).symm
          (fderivWithin ℝ T (range I) z (v i)))
  rw [manifoldAreaForm_apply]
  simp only [ContinuousLinearEquiv.apply_symm_apply]

/-- The coordinate-area identity for the entire pulled-back form. Differentiability is needed
only at points of the map's image; no regularity outside that image is assumed. -/
theorem _root_.ContMDiff.mextDeriv_mpullback_manifoldOneForm {f : M → ℂ} {P Q : ℂ → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℂ) 2 f)
    (hP : ∀ x, DifferentiableAt ℝ P (f x)) (hQ : ∀ x, DifferentiableAt ℝ Q (f x)) :
    mextDeriv (mpullback I 𝓘(ℝ, ℂ) f (manifoldOneForm P Q)) =
      fun x ↦ curl P Q (f x) • mpullback I 𝓘(ℝ, ℂ) f manifoldAreaForm x := by
  funext x
  exact ContMDiff.mextDeriv_mpullback_manifoldOneForm_apply hf x (hP x) (hQ x)

end TauCeti.Green
