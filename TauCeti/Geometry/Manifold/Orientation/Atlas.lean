/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OrientedAtlas
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Orientations determined by oriented atlases and model orientations

An oriented subatlas of the maximal atlas determines an actual orientation, also at boundary and
corner points. The converse requires a boundaryless hypothesis and is not used here.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [cM : ChartedSpace H M] [mM : IsManifold I 1 M]
  {n : ℕ∞ω} [NeZero n]

variable {ι : Type*} [Fintype ι]

private def IsOrientedAtlas.orientationData {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    {l : Manifold.OrientationLift I M ι //
      ∀ e ∈ A, ∀ x ∈ e.source, ∃ L : TangentSpace I x ≃L[ℝ] E,
        (L : TangentSpace I x →L[ℝ] E) = mfderiv I I e x ∧
          Orientation.map ι L.toLinearEquiv
            (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
              else -l.modelOrientation) = model} := by
  have hsub : A ⊆ IsManifold.maximalAtlas I 1 M :=
    hA.subset_maximalAtlas.trans (IsManifold.maximalAtlas_subset_of_le
      (ENat.one_le_iff_ne_zero_withTop.mpr (NeZero.ne n)))
  have hAcover := hA.exists_mem_source
  have hAdet : ∀ {e e' : OpenPartialHomeomorph M H}, e ∈ A → e' ∈ A →
      ∀ {x : M}, x ∈ e.source → x ∈ e'.source →
      0 < (fderivWithin ℝ (e'.extend I ∘ (e.extend I).symm) (range I)
        (e.extend I x)).det := by
    intro e e' he he' x hx hx'
    exact hA.det_fderivWithin_pos he he' hx hx'
  have hcompat := @IsManifold.compatible_of_mem_maximalAtlas ℝ _ E _ _ H _ I 1 M _ _
  let enlarged : ChartedSpace H M := {
    atlas := IsManifold.maximalAtlas I 1 M
    chartAt := chartAt H
    mem_chart_source := mem_chart_source H
    chart_mem_atlas := IsManifold.chart_mem_maximalAtlas }
  let : ChartedSpace H M := enlarged
  let : HasGroupoid M (contDiffGroupoid 1 I) := ⟨fun he he' ↦ hcompat he he'⟩
  let : IsManifold I 1 M := IsManifold.mk' I 1 M
  let Z := tangentBundleCore I M
  let S : Set (atlas H M) := {e | e.val ∈ A}
  have hcover : ∀ x, ∃ e ∈ S, x ∈ Z.baseSet e := by
    intro x
    obtain ⟨e, he, hx⟩ := hAcover x
    exact ⟨⟨e, hsub he⟩, he, hx⟩
  have hpos : ∀ e ∈ S, ∀ e' ∈ S, ∀ x ∈ Z.baseSet e ∩ Z.baseSet e',
      0 < (Z.coordChange e e' x).det := by
    intro e he e' he' x hx
    exact hAdet he he' hx.1 hx.2
  let vb := Z.orientationOfPositiveAtlas model hι hcover hpos
  let l := Manifold.OrientationLift.ofVectorBundleOrientation model hι vb
  have ho (x : M) : (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
      else -l.modelOrientation) = vb x := by
    have heq := Manifold.OrientationLift.orientationAt_ofVectorBundleOrientation model hι vb x
    rw [Manifold.OrientationLift.orientationAt_eq,
      Manifold.OrientationLift.chartOrientation_def] at heq
    exact heq
  have hread (j : atlas H M) (hj : j ∈ S) (x : M)
      (hxj : x ∈ (Z.localTriv j).baseSet) :
      Orientation.map ι ((Z.localTriv j).linearEquivAt ℝ x hxj) (vb x) = model := by
    simpa only [Bundle.Trivialization.mapOrientation_apply] using
      Z.mapOrientation_orientationOfPositiveAtlas model hι hcover hpos j hj x hxj
  let l' := @Manifold.OrientationLift.mk E H _ _ _ I M _ cM ι _ _
    l.modelOrientation l.card_eq l.sign l.locallyConstant_sign l.compatible
  let : ChartedSpace H M := cM
  let : IsManifold I 1 M := mM
  refine ⟨l', ?_⟩
  intro e he x hx
  let j : enlarged.atlas := ⟨e, hsub he⟩
  have hxj : x ∈ (Z.localTriv j).baseSet := hx
  have hd : e.MDifferentiable I I :=
    ⟨fun y hy ↦ (mdifferentiableAt_of_mem_maximalAtlas (hsub he) hy).mdifferentiableWithinAt,
      fun y hy ↦
        (mdifferentiableAt_symm_of_mem_maximalAtlas (hsub he) hy).mdifferentiableWithinAt⟩
  let L : TangentSpace I x ≃L[ℝ] E := hd.mfderiv hx
  have hlin : L.toLinearEquiv = (Z.localTriv j).linearEquivAt ℝ x hxj := by
    ext v
    -- L is the derivative equivalence; compare it pointwise with the tangent chart map.
    change mfderiv I I e x v = (Z.localTriv j).linearEquivAt ℝ x hxj v
    erw [Bundle.Trivialization.linearEquivAt_apply]
    erw [← Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ _ hxj]
    erw [Z.localTriv_continuousLinearMapAt hxj]
    have hmd := mdifferentiableAt_of_mem_maximalAtlas (I := I) (hsub he) hx
    simp only [mfderiv, ite_eq_left hmd]
    rfl
  refine ⟨L, rfl, ?_⟩
  have hox : (if l'.sign x ⟨x, mem_chart_source H x⟩ = 1 then l'.modelOrientation
      else -l'.modelOrientation) = vb x := ho x
  erw [hox, hlin]
  exact hread j he x hxj

/-- An oriented subatlas defines the quotient orientation whose charts read the
specified model orientation. It includes boundary and corner points. -/
def IsOrientedAtlas.orientation {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) : Manifold.Orientation I M ι :=
  Manifold.Orientation.mk (hA.orientationData model hι).val

/-- Every chart of the oriented atlas carries the constructed tangent orientation to the
chosen model orientation by its actual manifold derivative. -/
theorem IsOrientedAtlas.orientation_spec {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) {e : OpenPartialHomeomorph M H}
    (he : e ∈ A) {x : M} (hx : x ∈ e.source) :
    ∃ L : TangentSpace I x ≃L[ℝ] E,
      (L : TangentSpace I x →L[ℝ] E) = mfderiv I I e x ∧
        Orientation.map ι L.toLinearEquiv
          (Manifold.Orientation.orientationAt (hA.orientation model hι) x) = model := by
  rw [IsOrientedAtlas.orientation, Manifold.Orientation.orientationAt_mk]
  exact (hA.orientationData model hι).property e he x hx

end TauCeti
