/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Regularity of pullback for bundle-valued forms

Pullback along a `C^(n+1)` map preserves `C^n` regularity of differential forms with values in
an arbitrary vector bundle. The resulting form takes values in the pullback coefficient bundle,
not in a chosen trivialization of the original bundle. The relative statements use derivatives
within a unique-differentiability set and apply to manifolds with boundary or corners.

The proof uses the coordinate formula for rough bundle pullback from
`TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth`: the coefficient trivialization of
the pullback bundle is the original coefficient trivialization at the image point. Neither
finite dimensionality nor completeness is required.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Chapter 14.
-/

public section

noncomputable section

open Bundle Set Filter
open scoped Manifold Topology

namespace TauCeti

variable {E H M E' H' M' F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  [TopologicalSpace M'] [ChartedSpace H' M'] {I' : ModelWithCorners ℝ E' H'}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [IsManifold I 1 M] [IsManifold I' 1 M']
  {V : M' → Type*} [∀ y, AddCommGroup (V y)] [∀ y, Module ℝ (V y)]
  [∀ y, TopologicalSpace (V y)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V]
  {k : ℕ} {m n : WithTop ℕ∞} {s : Set M} {t : Set M'} {x : M}
  {ω : RoughBundleForm I' M' V k} {f : C(M, M')}

/-- In the canonical pullback coefficient trivialization, bundle pullback precomposes the
original form's coordinates with the tangent-coordinate derivative. -/
theorem _root_.ContinuousMap.inCoordinates_bundleMpullbackWithin
    (f : C(M, M')) (s : Set M) (ω : RoughBundleForm I' M' V k) (x y : M)
    (hy : f y ∈ (trivializationAt E' (TangentSpace I') (f x)).baseSet) :
    ContinuousAlternatingMap.inCoordinates (E₁ := TangentSpace I) (E₂ := f *ᵖ V) E F x y x y
        (bundleMpullbackWithin I I' f s ω y :
          TangentSpace I y [⋀^Fin k]→L[ℝ] (f *ᵖ V) y) =
      (ContinuousAlternatingMap.inCoordinates E' F (f x) (f y) (f x) (f y)
        (ω (f y))).compContinuousLinearMap
          (inTangentCoordinates I I' id f (mfderivWithin I I' f s) x y) := by
  rw [← TauCeti.inCoordinates_bundleMpullbackWithin ω f s x y hy]
  ext v
  simp only [ContinuousAlternatingMap.inCoordinates,
    ContinuousLinearMap.compContinuousAlternatingMap_coe,
    ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Trivialization.continuousLinearMapAt_apply, trivializationAt,
    FiberBundle.pullback_trivializationAt']
  -- The pulled-back linear chart has the original chart's fibre map, including off its base set.
  rfl

variable [∀ y, IsTopologicalAddGroup (V y)] [∀ y, ContinuousSMul ℝ (V y)]

/-- A bundle-valued `C^m` form pulls back to a `C^m` form within a unique-differentiability set
along a `C^n` map, provided `m + 1 ≤ n`. The continuous map supplies the canonical topology on
the pullback coefficient bundle; its differentiability is only required within `s` at `x`. -/
theorem _root_.ContMDiffWithinAt.bundleMpullbackWithin_form
    (hω : ContMDiffWithinAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) t (f x))
    (hf : ContMDiffWithinAt I I' n f s x) (hmn : m + 1 ≤ n)
    (hst : MapsTo f s t) (hx : x ∈ s) (hs : UniqueMDiffOn I s) :
    ContMDiffWithinAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] (f *ᵖ V) y)
        y (bundleMpullbackWithin I I' f s ω y)) s x := by
  have hfm : ContMDiffWithinAt I I' m f s x :=
    hf.of_le ((le_add_of_nonneg_right zero_le_one).trans hmn)
  have hcoeff := (contMDiffWithinAt_continuousAlternatingMap_bundle _).mp hω |>.2
  have hc := hcoeff.comp x hfm hst
  have hd := hf.mfderivWithin_const hmn hx hs
  have hpre := ContinuousAlternatingMap.contDiff_compContinuousLinearMapCLM
    (𝕜 := ℝ) (E := E) (F := E') (G := F) (ι := Fin k) m
  have hp := (hpre.comp_contMDiffWithinAt hd).clm_apply hc
  apply (contMDiffWithinAt_continuousAlternatingMap_bundle _).mpr
  refine ⟨contMDiffWithinAt_id, hp.congr_of_eventuallyEq_of_mem ?_ hx⟩
  have hmem : f ⁻¹' (trivializationAt E' (TangentSpace I') (f x)).baseSet ∈ 𝓝[s] x :=
    hf.continuousWithinAt.preimage_mem_nhdsWithin
      ((trivializationAt E' (TangentSpace I') (f x)).open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt' (f x)))
  filter_upwards [hmem] with y hy
  simpa only [Function.comp_apply, ContinuousAlternatingMap.compContinuousLinearMapCLM_apply]
    using f.inCoordinates_bundleMpullbackWithin s ω x y hy

/-- Pullback of bundle-valued forms within a unique-differentiability set preserves regularity
on that set, with the loss of one derivative of the map. -/
theorem _root_.ContMDiffOn.bundleMpullbackWithin_form
    (hω : ContMDiffOn I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) t)
    (hf : ContMDiffOn I I' n f s) (hmn : m + 1 ≤ n)
    (hst : MapsTo f s t) (hs : UniqueMDiffOn I s) :
    ContMDiffOn I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] (f *ᵖ V) y)
        y (bundleMpullbackWithin I I' f s ω y)) s :=
  fun x hx ↦ (hω _ (hst hx)).bundleMpullbackWithin_form (hf x hx) hmn hst hx hs

/-- Pointwise regularity of bundle-valued pullback, in the canonical pullback bundle. -/
theorem _root_.ContMDiffAt.bundleMpullback_form
    (hω : ContMDiffAt I' (I'.prod 𝓘(ℝ, E' [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E' [⋀^Fin k]→L[ℝ] F) y (ω y)) (f x))
    (hf : ContMDiffAt I I' n f x) (hmn : m + 1 ≤ n) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F)) m
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin k]→L[ℝ] F)
        (E := fun y ↦ TangentSpace I y [⋀^Fin k]→L[ℝ] (f *ᵖ V) y)
        y (bundleMpullback I I' f ω y)) x := by
  simpa only [bundleMpullbackWithin_univ, contMDiffWithinAt_univ] using
    ContMDiffWithinAt.bundleMpullbackWithin_form (s := univ) (t := univ)
      hω.contMDiffWithinAt hf.contMDiffWithinAt hmn (mapsTo_univ _ _) (mem_univ x)
      uniqueMDiffOn_univ

/-- Pullback along a `C^n` map preserves `C^m` bundle-valued forms if `m + 1 ≤ n`.
The coefficients live in the canonical pullback bundle. No smoothness assumption on the
coefficient bundle's transition maps is needed beyond the displayed regularity of the form. -/
theorem IsSmoothBundleForm.bundleMpullback (hω : IsSmoothBundleForm I' F V m ω)
    (hf : ContMDiff I I' n f) (hmn : m + 1 ≤ n) :
    IsSmoothBundleForm I F (f *ᵖ V) m (fun y ↦ bundleMpullback I I' f ω y) := by
  have h := (isSmoothBundleForm_def m ω).mp hω
  apply (isSmoothBundleForm_def (I := I) (F := F) (V := f *ᵖ V) m
    (fun y ↦ TauCeti.bundleMpullback I I' f ω y)).mpr
  exact fun x ↦ (h (f x)).bundleMpullback_form (hf x) hmn

end TauCeti
