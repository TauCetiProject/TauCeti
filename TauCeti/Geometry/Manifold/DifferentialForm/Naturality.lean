/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity

/-!
# Naturality of the exterior derivative on manifolds

Exterior differentiation commutes with pullback by a twice continuously differentiable map.
The proof reads both sides in preferred extended charts and applies the corresponding flat
naturality theorem.  A local coordinate comparison identifies manifold pullback with flat
pullback by `writtenInExtChartAt`.

The coordinate comparison follows the chart-transport pattern used for vector fields in
Mathlib's `Geometry.Manifold.VectorField.LieBracket`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Proposition 14.26.
-/

public section

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 2 M] [IsManifold I' 2 M'] {k : ℕ}

private theorem RoughForm.inChartAt_mpullback_eventuallyEq
    {f : M → M'} (hf : ContMDiff I I' 2 f) (phi : RoughForm I' M' F k) (x : M) :
    (mpullback I I' f phi).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      fun z ↦ (phi.inChartAt (f x) (writtenInExtChartAt I I' x f z)).compContinuousLinearMap
        (fderivWithin ℝ (writtenInExtChartAt I I' x f) (range I) z) := by
  let g : E → E' := writtenInExtChartAt I I' x f
  have htarget : (f ∘ (extChartAt I x).symm) ⁻¹' (extChartAt I' (f x)).source ∈
      𝓝[range I] (extChartAt I x x) := by
    apply hf.continuous.continuousAt.comp
      (continuousAt_extChartAt_symm'' (mem_extChartAt_target x))
      |>.continuousWithinAt.preimage_mem_nhdsWithin
    simpa only [Function.comp_apply, extChartAt_to_inv] using
      extChartAt_source_mem_nhds (I := I') (f x)
  filter_upwards [extChartAt_target_mem_nhdsWithin x, htarget] with z hz h'fz
  let y : M := (extChartAt I x).symm z
  have hfy : f y ∈ (extChartAt I' (f x)).source := h'fz
  have hgz : g z = extChartAt I' (f x) (f y) := by
    rfl
  have hgzt : g z ∈ (extChartAt I' (f x)).target := by
    rw [hgz]
    exact (extChartAt I' (f x)).map_source hfy
  have hsource : MDifferentiableWithinAt (modelWithCornersSelf ℝ E) I
      (extChartAt I x).symm (range I) z :=
    mdifferentiableWithinAt_extChartAt_symm hz
  have hf_y : MDifferentiableAt I I' f y := (hf y).mdifferentiableAt two_ne_zero
  have hchart : MDifferentiableAt I' (modelWithCornersSelf ℝ E')
      (extChartAt I' (f x)) (f y) :=
    mdifferentiableAt_extChartAt (by simpa using hfy)
  have hg : MDifferentiableWithinAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E') g (range I) z := by
    simpa only [g, writtenInExtChartAt, Function.comp_assoc] using
      hchart.comp_mdifferentiableWithinAt z (hf_y.comp_mdifferentiableWithinAt z hsource)
  have htargetInv : MDifferentiableWithinAt (modelWithCornersSelf ℝ E') I'
      (extChartAt I' (f x)).symm (range I') (g z) :=
    mdifferentiableWithinAt_extChartAt_symm hgzt
  have hlocalSource : (f ∘ (extChartAt I x).symm) ⁻¹'
      (extChartAt I' (f x)).source ∈ 𝓝[range I] z := by
    apply hf.continuous.continuousAt.comp (continuousAt_extChartAt_symm'' hz)
      |>.continuousWithinAt.preimage_mem_nhdsWithin
    exact extChartAt_source_mem_nhds' hfy
  have hpreTarget : g ⁻¹' (extChartAt I' (f x)).target ∈ 𝓝[range I] z := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hz, hlocalSource] with w hw hfw
    exact writtenInExtChartAt_mapsTo ⟨hw, hfw⟩
  have hpre : g ⁻¹' range I' ∈ 𝓝[range I] z :=
    mem_of_superset hpreTarget (preimage_mono (extChartAt_target_subset_range (f x)))
  have hu : UniqueMDiffWithinAt (modelWithCornersSelf ℝ E) (range I) z := by
    rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
    exact I.uniqueDiffOn.uniqueDiffWithinAt (extChartAt_target_subset_range x hz)
  have hleft : (extChartAt I' (f x)).symm ∘ g =ᶠ[𝓝[range I] z]
      f ∘ (extChartAt I x).symm := by
    filter_upwards [hpreTarget, hlocalSource] with w hw hfw
    -- Expose the named coordinate map so the chart inverse law rewrites its value.
    change (extChartAt I' (f x)).symm (g w) = f ((extChartAt I x).symm w)
    have hgw : g w = extChartAt I' (f x) (f ((extChartAt I x).symm w)) := rfl
    rw [hgw]
    exact (extChartAt I' (f x)).left_inv hfw
  have hleft_z : ((extChartAt I' (f x)).symm ∘ g) z =
      (f ∘ (extChartAt I x).symm) z := by
    simpa only [Function.comp_apply, hgz] using (extChartAt I' (f x)).left_inv hfy
  have hcompTarget :
      mfderivWithin (modelWithCornersSelf ℝ E) I'
          ((extChartAt I' (f x)).symm ∘ g) (range I) z =
        (mfderivWithin (modelWithCornersSelf ℝ E') I'
          (extChartAt I' (f x)).symm (range I') (g z)).comp
          (mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E')
            g (range I) z) :=
    mfderivWithin_comp_of_preimage_mem_nhdsWithin_of_eq
      (I := modelWithCornersSelf ℝ E) (I' := modelWithCornersSelf ℝ E') (I'' := I')
      (f := g) (g := (extChartAt I' (f x)).symm) (s := range I) (u := range I')
      (x := z) (y := g z) htargetInv hg hpre hu rfl
  have hcompSource :
      mfderivWithin (modelWithCornersSelf ℝ E) I'
          (f ∘ (extChartAt I x).symm) (range I) z =
        (mfderiv I I' f y).comp
          (mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I x).symm (range I) z) := by
    simpa only [y] using mfderiv_comp_mfderivWithin z hf_y hsource
      hu
  have hderiv' :
      (mfderiv I I' f y).comp
          (mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I x).symm (range I) z) =
        (mfderivWithin (modelWithCornersSelf ℝ E') I'
          (extChartAt I' (f x)).symm (range I') (g z)).comp
          (mfderivWithin (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E')
            g (range I) z) := by
    rw [← hcompTarget, ← hcompSource]
    exact (hleft.mfderivWithin_eq hleft_z).symm
  have hderiv :
      (mfderiv I I' f y).comp
          (mfderivWithin (modelWithCornersSelf ℝ E) I
            (extChartAt I x).symm (range I) z) =
        (mfderivWithin (modelWithCornersSelf ℝ E') I'
          (extChartAt I' (f x)).symm (range I') (g z)).comp
          (fderivWithin ℝ g (range I) z) := by
    have hflat : mfderivWithin (modelWithCornersSelf ℝ E)
        (modelWithCornersSelf ℝ E') g (range I) z = fderivWithin ℝ g (range I) z :=
      mfderivWithin_eq_fderivWithin
    exact hderiv'.trans (congrArg
      (fun L ↦ (mfderivWithin (modelWithCornersSelf ℝ E') I'
        (extChartAt I' (f x)).symm (range I') (g z)).comp L) hflat)
  ext v
  simp only [RoughForm.inChartAt_apply, mpullback_apply,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_apply]
  -- Both model tangent fibres are definitionally the model spaces only after evaluation.
  change _ = phi ((extChartAt I' (f x)).symm (g z)) (fun i ↦
    mfderivWithin (modelWithCornersSelf ℝ E') I' (extChartAt I' (f x)).symm
      (range I') (g z) (fderivWithin ℝ g (range I) z (v i)))
  rw [hgz, (extChartAt I' (f x)).left_inv hfy]
  congr 1
  funext i
  exact congrArg (fun L ↦ L (v i)) hderiv

/-- Pullback by a `C²` map commutes with the exterior derivative of a `C¹` form. -/
theorem mpullback_mextDeriv {f : M → M'} (hf : ContMDiff I I' 2 f)
    {phi : RoughForm I' M' F k}
    (hphi : IsSmoothBundleForm I' F (Trivial M' F) 1 phi) :
    mpullback I I' f (mextDeriv phi) = mextDeriv (mpullback I I' f phi) := by
  funext x
  let g : E → E' := writtenInExtChartAt I I' x f
  have hphi' : DifferentiableWithinAt ℝ (phi.inChartAt (f x)) (range I')
      (extChartAt I' (f x) (f x)) := by
    simpa only [preimage_univ, univ_inter] using phi.differentiableWithinAt_inChartAt
      (((isSmoothBundleForm_def 1 phi).mp hphi (f x)).mdifferentiableWithinAt one_ne_zero)
  have hg : ContDiffWithinAt ℝ 2 g (range I) (extChartAt I x x) := by
    have hs := contMDiffWithinAt_extChartAt_symm_range (I := I) (n := 2) x
      (mem_extChartAt_target x)
    have hfs := (hf x).comp_contMDiffWithinAt_of_eq hs (extChartAt_to_inv (I := I) x)
    have ht := contMDiffAt_extChartAt' (I := I') (n := 2) (x := f x)
      (ChartedSpace.mem_chart_source (f x))
    have htotal := ht.comp_contMDiffWithinAt_of_eq hfs (by
      simp only [Function.comp_apply, extChartAt_to_inv])
    simpa only [g, writtenInExtChartAt, Function.comp_assoc] using htotal.contDiffWithinAt
  have htarget : (f ∘ (extChartAt I x).symm) ⁻¹' (extChartAt I' (f x)).source ∈
      𝓝[range I] (extChartAt I x x) := by
    apply hf.continuous.continuousAt.comp
      (continuousAt_extChartAt_symm'' (mem_extChartAt_target x))
      |>.continuousWithinAt.preimage_mem_nhdsWithin
    simpa only [Function.comp_apply, extChartAt_to_inv] using
      extChartAt_source_mem_nhds (I := I') (f x)
  have hpreTarget : g ⁻¹' (extChartAt I' (f x)).target ∈
      𝓝[range I] (extChartAt I x x) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin x, htarget] with z hz hfz
    exact writtenInExtChartAt_mapsTo ⟨hz, hfz⟩
  have hpre : g ⁻¹' range I' ∈ 𝓝[range I] (extChartAt I x x) :=
    mem_of_superset hpreTarget (preimage_mono (extChartAt_target_subset_range (f x)))
  have hgx : g (extChartAt I x x) = extChartAt I' (f x) (f x) := by
    simp only [g, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have hphi_g : DifferentiableWithinAt ℝ (phi.inChartAt (f x)) (range I')
      (g (extChartAt I x x)) := by
    rw [hgx]
    exact hphi'
  have hcoord := phi.inChartAt_mpullback_eventuallyEq hf x
  have hcoord_x := hcoord.self_of_nhdsWithin (mem_range_self _)
  have hright : mextDeriv (mpullback I I' f phi) x =
      extDerivWithin
        (fun z ↦ (phi.inChartAt (f x) (g z)).compContinuousLinearMap
          (fderivWithin ℝ g (range I) z)) (range I) (extChartAt I x x) := by
    rw [mextDeriv_def]
    exact hcoord.extDerivWithin_eq hcoord_x
  have hnatural := extDerivWithin_pullback_of_preimage_mem_nhdsWithin
    (f := g) (s := range I) (t := range I') (x := extChartAt I x x)
    hphi_g hg (by norm_num) I.uniqueDiffOn
    (I.range_subset_closure_interior (mem_range_self _)) (mem_range_self _) hpre
  ext v
  rw [mpullback_apply, hright, hnatural, hgx, mextDeriv_def,
    (hf x).mdifferentiableAt two_ne_zero |>.mfderiv_abuse]
  rfl

end TauCeti
