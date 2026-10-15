/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Chart
public import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.MFDeriv.Chart

/-!
# Naturality of the exterior derivative on manifolds

For a twice continuously differentiable map `f : M → M'` and a continuously differentiable
differential form `phi` on `M'`, pulling back commutes with exterior differentiation:
`f^* (d phi) = d (f^* phi)`. This is the naturality of the exterior derivative, which makes
pullback by `f` a map of de Rham cochain complexes and hence is what induces the maps
`f^* : H^k_dR(M') → H^k_dR(M)` on de Rham cohomology.

The local coordinate comparison follows the chart-transport pattern used for vector fields in
Mathlib's `Geometry.Manifold.VectorField.LieBracket`.

## Main statements

* `TauCeti.mpullback_mextDeriv`: pullback by a `C²` map commutes with the exterior derivative
  of a `C¹` form.

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
  [NormedAddCommGroup F] [NormedSpace ℝ F] {k : ℕ}

variable [IsManifold I 2 M] [IsManifold I' 2 M']

private theorem RoughForm.inChartAt_mpullback_eventuallyEq
    {f : M → M'} (hf : ContMDiff I I' 2 f) (phi : RoughForm I' M' F k) (x : M) :
    (mpullback I I' f phi).inChartAt x =ᶠ[𝓝[range I] (extChartAt I x x)]
      fun z ↦ (phi.inChartAt (f x) (writtenInExtChartAt I I' x f z)).compContinuousLinearMap
        (fderivWithin ℝ (writtenInExtChartAt I I' x f) (range I) z) := by
  let g : E → E' := writtenInExtChartAt I I' x f
  have hfx : f ((extChartAt I x).symm (extChartAt I x x)) ∈ (extChartAt I' (f x)).source := by
    simpa only [extChartAt_to_inv] using mem_extChartAt_source (I := I') (f x)
  filter_upwards [extChartAt_target_mem_nhdsWithin x,
    preimage_extChartAt_source_mem_nhdsWithin (mem_extChartAt_target x)
      hf.continuous.continuousAt hfx] with z hz hfy
  replace hfy : f ((extChartAt I x).symm z) ∈ (extChartAt I' (f x)).source := hfy
  have hgz : g z = extChartAt I' (f x) (f ((extChartAt I x).symm z)) := rfl
  have hderiv := mfderiv_comp_mfderivWithin_extChartAt_symm hz
    ((hf _).mdifferentiableAt two_ne_zero) hfy
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
  have hfx : f ((extChartAt I x).symm (extChartAt I x x)) ∈ (extChartAt I' (f x)).source := by
    simpa only [extChartAt_to_inv] using mem_extChartAt_source (I := I') (f x)
  have hpreTarget := writtenInExtChartAt_preimage_target_mem_nhdsWithin
    (mem_extChartAt_target x) hf.continuous.continuousAt hfx
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
  -- `MDifferentiableAt.mfderiv` writes `mfderiv I I' f x` as the flat chart derivative of `g`
  -- conjugated by `tangentSpaceCastModel`, the identification of `TangentSpace I x` with `E`
  -- (and of `TangentSpace I' (f x)` with `E'`). Both casts are the identity on vectors, since
  -- tangent fibres are model spaces by definition, so `rfl` closes the remaining goal.
  rw [mpullback_apply, hright, hnatural, hgx, mextDeriv_def,
    (hf x).mdifferentiableAt two_ne_zero |>.mfderiv]
  rfl

end TauCeti
