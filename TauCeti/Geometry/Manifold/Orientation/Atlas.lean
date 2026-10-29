/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OrientedAtlas
public import TauCeti.Geometry.Manifold.Orientation.Basic
import TauCeti.Geometry.Manifold.MFDeriv.Chart
import TauCeti.Geometry.Manifold.VectorBundle.Tangent
public import TauCeti.Topology.VectorBundle.Orientation.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Orientations determined by oriented atlases and model orientations

An oriented subatlas of the maximal atlas determines an actual orientation, also at boundary and
corner points. The converse, existence of an oriented atlas for every orientation,
is not proved here.
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
          Orientation.map ι L.toLinearEquiv (l.orientationAt x) = model} := by
  -- First promote the positive subatlas to the C1 maximal atlas.
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
  have hcompat {e e' : OpenPartialHomeomorph M H}
      (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M) :
      e.symm.trans e' ∈ contDiffGroupoid 1 I :=
    IsManifold.compatible_of_mem_maximalAtlas (I := I) (n := 1) he he'
  -- Enlarge the atlas while retaining exactly the original preferred charts.
  let enlarged : ChartedSpace H M := {
    atlas := IsManifold.maximalAtlas I 1 M
    chartAt := chartAt H
    mem_chart_source := mem_chart_source H
    chart_mem_atlas := IsManifold.chart_mem_maximalAtlas }
  let : ChartedSpace H M := enlarged
  let : HasGroupoid M (contDiffGroupoid 1 I) := ⟨fun he he' ↦ hcompat he he'⟩
  let : IsManifold I 1 M := IsManifold.mk' I 1 M
  have enlargedManifold := (inferInstance : IsManifold I 1 M)
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
  -- The positive core subatlas constructs the fibre orientations and their chartwise equation.
  let vb := Z.orientationOfPositiveAtlas model hι hcover hpos
  let l := Manifold.OrientationLift.ofVectorBundleOrientation model hι vb
  have ho (x : M) : (if l.sign x ⟨x, mem_chart_source H x⟩ = 1 then l.modelOrientation
      else -l.modelOrientation) = vb x := by
    have heq := Manifold.OrientationLift.orientationAt_ofVectorBundleOrientation model hι vb x
    rw [Manifold.OrientationLift.orientationAt_eq,
      Manifold.OrientationLift.chartOrientation_eq_ite] at heq
    exact heq
  have hread (j : atlas H M) (hj : j ∈ S) (x : M)
      (hxj : x ∈ (Z.localTriv j).baseSet) :
      Orientation.map ι ((Z.localTriv j).linearEquivAt ℝ x hxj) (vb x) = model := by
    simpa only [Bundle.Trivialization.mapOrientation_apply] using
      Z.mapOrientation_orientationOfPositiveAtlas model hι hcover hpos j hj x hxj
  -- Transfer source-indexed signs back using equality of preferred charts, not equality of atlases.
  let l' := l.congrChartAt (c := enlarged) (c' := cM) rfl
  let : ChartedSpace H M := cM
  let : IsManifold I 1 M := mM
  refine ⟨l', ?_⟩
  intro e he x hx
  -- Finally identify the chosen chart reading with its actual manifold derivative.
  let j : enlarged.atlas := ⟨e, hsub he⟩
  have hxj : x ∈ (Z.localTriv j).baseSet := hx
  have hd : e.MDifferentiable I I :=
    ⟨fun y hy ↦ (mdifferentiableAt_of_mem_maximalAtlas (hsub he) hy).mdifferentiableWithinAt,
      fun y hy ↦
        (mdifferentiableAt_symm_of_mem_maximalAtlas (hsub he) hy).mdifferentiableWithinAt⟩
  let L : TangentSpace I x ≃L[ℝ] E := hd.mfderiv hx
  have hmap : mfderiv I I e x = (Z.localTriv j).continuousLinearMapAt ℝ x := by
    let : ChartedSpace H M := enlarged
    have : IsManifold I 1 M := enlargedManifold
    exact (Manifold.mfderiv_eq_of_chartAt_eq (I := I)
      (c := cM) (c' := enlarged) rfl e x).trans
      (Manifold.mfderiv_atlas_eq_continuousLinearMapAt (I := I) j hxj)
  have hlin : L.toLinearEquiv = (Z.localTriv j).linearEquivAt ℝ x hxj := by
    ext v
    exact (congrArg (fun f : TangentSpace I x →L[ℝ] E ↦ f v) hmap).trans
      ((Bundle.Trivialization.continuousLinearMapAt_apply_of_mem ℝ (Z.localTriv j) hxj v).trans
        (Bundle.Trivialization.linearEquivAt_apply (Z.localTriv j) x hxj v).symm)
  -- L was defined as the derivative equivalence, so its underlying map is mfderiv.
  refine ⟨L, rfl, ?_⟩
  have hox : l'.orientationAt x = vb x := by
    rw [Manifold.OrientationLift.orientationAt_eq, Manifold.OrientationLift.chartOrientation_eq_ite]
    -- At the preferred chart's centre, tangent and model orientations have the same scalar data.
    change (if l'.sign x ⟨x, mem_chart_source H x⟩ = 1 then l'.modelOrientation
      else -l'.modelOrientation) = vb x
    simpa only [l', Manifold.OrientationLift.congrChartAt_sign,
      Manifold.OrientationLift.congrChartAt_modelOrientation] using ho x
  calc
    Orientation.map ι L.toLinearEquiv (l'.orientationAt x) =
        Orientation.map ι L.toLinearEquiv (vb x) :=
      congrArg (fun o : Orientation ℝ (TangentSpace I x) ι ↦
        Orientation.map ι L.toLinearEquiv o) hox
    _ = model := (congrArg (fun f : TangentSpace I x ≃ₗ[ℝ] E ↦
      Orientation.map ι f (vb x)) hlin).trans (hread j he x hxj)

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

/-- An oriented atlas gives orientability, including at boundary and corner points. -/
theorem IsOrientedAtlas.orientable {n : ℕ∞ω} [NeZero n]
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A) : Orientable I M :=
  ⟨⟨hA.orientation (Module.finBasis ℝ E).orientation (Fintype.card_fin _)⟩⟩

/-- A manifold whose given atlas has positive transition derivatives is orientable. -/
theorem Orientable.of_hasGroupoid [HasGroupoid M (orientationPreservingGroupoid I)] :
    Orientable I M := by
  apply IsOrientedAtlas.orientable (n := 1) (A := atlas H M)
  exact ⟨IsManifold.subset_maximalAtlas,
    fun x ↦ ⟨chartAt H x, chart_mem_atlas H x, mem_chart_source H x⟩,
    fun he he' ↦ HasGroupoid.compatible he he'⟩
end TauCeti
