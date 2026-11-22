/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.OrientedAtlas
public import TauCeti.Geometry.Manifold.Orientation.Basic
public import TauCeti.Geometry.Manifold.Orientation.Preserving
import Mathlib.Geometry.Manifold.MFDeriv.Tangent
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import TauCeti.Geometry.Manifold.IsManifold.InteriorChart
import TauCeti.Geometry.Manifold.LocalDiffeomorph.Basic
import TauCeti.Geometry.Manifold.Orientation.Pullback
import TauCeti.LinearAlgebra.Reflection
import TauCeti.Geometry.Manifold.MFDeriv.Chart.Basic
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.Basic
public import TauCeti.Topology.VectorBundle.Orientation.Atlas
public import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Orientations determined by oriented atlases and model orientations

An oriented subatlas of the maximal atlas determines an actual orientation, also at boundary and
corner points (`TauCeti.IsOrientedAtlas.orientation`).

Conversely, on a `C¹` manifold without boundary (`BoundarylessManifold I M`, while the model `I`
itself may have boundary) modelled on a nontrivial space, every orientation `o` comes from an
oriented atlas: for a fixed orientation `μ` of the model space, the charts of the maximal atlas
whose derivatives carry `o` to `μ` at every point of their sources form an oriented atlas
(`TauCeti.isOrientedAtlas_setOf_isOrientationPreservingAt`), which determines `o` from `μ`
(`TauCeti.orientation_isOrientedAtlas_setOf_isOrientationPreservingAt`). They cover the manifold:
near a point where a chart reverses orientation, the chart may be followed by a reflection of `E`
fixing the image of that point, which lies in the interior of the range of the model
(`TauCeti.exists_mem_maximalAtlas_isOrientationPreservingAt_of_isOrientationReversingAt`). In
dimension zero the maximal atlas is itself oriented. Hence a `C¹` manifold without boundary is
orientable if and only if it has an oriented atlas (`TauCeti.orientable_iff_exists_atlas`,
[Lee, Proposition 15.6]). The boundary hypothesis cannot be dropped: `Set.Icc 0 1` is orientable,
but its charts send each endpoint to the boundary point of the half-line, so a chart at `0` is
increasing near `0` and a chart at `1` is decreasing near `1`, and no atlas of `Set.Icc 0 1` is
oriented.

When the given atlas is itself oriented, every model orientation is the model orientation of an
orientation lift all of whose chart signs are `1` (`Manifold.OrientationLift.ofHasGroupoid`). It
represents the orientation of that atlas (`Manifold.OrientationLift.mk_ofHasGroupoid`), and chart
computations with it involve no signs.

## Main results

* `TauCeti.IsOrientedAtlas.orientation`: the orientation determined by an oriented atlas.
* `TauCeti.isOrientedAtlas_setOf_isOrientationPreservingAt`: the charts carrying an orientation to
  a fixed model orientation form an oriented atlas of a manifold without boundary.
* `TauCeti.orientable_iff_exists_atlas`: a `C¹` manifold without boundary is orientable if and only
  if it has an oriented atlas.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd edition, Proposition 15.6.
-/

public section

noncomputable section

open Set
open scoped Manifold ContDiff Topology

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
      (c := cM) (c' := enlarged) e x rfl).trans
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

/-- At a point whose preferred chart belongs to the oriented atlas, the constructed tangent
orientation, read in that chart, is the chosen model orientation. -/
theorem IsOrientedAtlas.orientationAt_orientation {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) {x : M} (hx : chartAt H x ∈ A) :
    Manifold.Orientation.orientationAt (hA.orientation model hι) x = model := by
  obtain ⟨L, hL, hmap⟩ := hA.orientation_spec model hι hx (mem_chart_source H x)
  -- The derivative of the preferred chart at its own centre is the identity of the model.
  have hLv (v : TangentSpace I x) : L v = v := by
    have := congrArg (fun f : TangentSpace I x →L[ℝ] E ↦ f v) hL
    simp only [ContinuousLinearEquiv.coe_coe] at this
    rw [this, mfderiv_chartAt_eq_tangentCoordChange (mem_chart_source H x)]
    exact tangentCoordChange_self (mem_extChartAt_source x)
  have hrefl : L.toLinearEquiv = LinearEquiv.refl ℝ E := LinearEquiv.ext hLv
  rw [hrefl] at hmap
  exact (Equiv.ext_iff.mp (Orientation.map_refl (R := ℝ) (M := E) ι) _).symm.trans hmap

/-- Reversing the chosen model orientation reverses the manifold orientation determined by an
oriented atlas. -/
@[simp]
theorem IsOrientedAtlas.orientation_neg {A : Set (OpenPartialHomeomorph M H)}
    (hA : IsOrientedAtlas I n A) (model : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) :
    hA.orientation (-model) hι = -hA.orientation model hι := by
  ext x
  obtain ⟨e, he, hx⟩ := hA.exists_mem_source x
  obtain ⟨L, hL, hmap⟩ := hA.orientation_spec model hι he hx
  obtain ⟨L', hL', hmap'⟩ := hA.orientation_spec (-model) hι he hx
  have hLL' : L' = L := ContinuousLinearEquiv.coe_injective (hL'.trans hL.symm)
  rw [hLL'] at hmap'
  have h : Orientation.map ι L.toLinearEquiv
      ((hA.orientation (-model) hι).orientationAt x) =
      Orientation.map ι L.toLinearEquiv (-(hA.orientation model hι).orientationAt x) := by
    rw [hmap', Orientation.map_neg, hmap]
  exact ((Orientation.map ι L.toLinearEquiv).injective h).trans
    (Manifold.Orientation.orientationAt_neg _ _).symm

/-- An oriented atlas gives orientability, including at boundary and corner points. -/
theorem IsOrientedAtlas.orientable {n : ℕ∞ω} [NeZero n]
    {A : Set (OpenPartialHomeomorph M H)} (hA : IsOrientedAtlas I n A) : Orientable I M :=
  ⟨⟨hA.orientation (Module.finBasis ℝ E).orientation (Fintype.card_fin _)⟩⟩

/-- A manifold whose given atlas has positive transition derivatives is orientable. -/
theorem Orientable.of_hasGroupoid [HasGroupoid M (orientationPreservingGroupoid I)] :
    Orientable I M :=
  (isOrientedAtlas_atlas I 1 M).orientable

/-! ### Lifts with trivial chart signs -/

namespace Manifold.OrientationLift

variable [HasGroupoid M (orientationPreservingGroupoid I)]
  (model : _root_.Orientation ℝ E ι) (hι : Fintype.card ι = Module.finrank ℝ E)

/-- The lift with trivial chart signs represents the orientation that the given atlas determines
with the same model orientation. -/
theorem mk_ofHasGroupoid :
    Manifold.Orientation.mk (ofHasGroupoid (I := I) (M := M) model hι) =
      (isOrientedAtlas_atlas I 1 M).orientation model hι := by
  ext x
  rw [Manifold.Orientation.orientationAt_mk, orientationAt_ofHasGroupoid,
    IsOrientedAtlas.orientationAt_orientation _ _ _ (chart_mem_atlas H x)]

end Manifold.OrientationLift

/-! ### Oriented atlases of an orientation -/

section OfOrientation

open Manifold.Orientation

/-- A self-map of the model space `H` which preserves the constant orientation of `H` at every
point of `s` preserves orientation on `s` in the sense of coordinate changes. -/
theorem orientationPreservingOn_of_isOrientationPreservingAt (μ : Orientation ℝ E ι)
    (hι : Fintype.card ι = Module.finrank ℝ E) {g : H → H} {s : Set H}
    (h : ∀ z ∈ s, IsOrientationPreservingAt (model (I := I) μ hι) (model (I := I) μ hι) g z) :
    OrientationPreservingOn I g s := by
  rw [orientationPreservingOn_iff]
  intro z hz
  obtain ⟨D, hD, hmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 (h z hz)
  have hg : MDifferentiableAt I I g z := mdifferentiableAt_of_isInvertible_mfderiv ⟨D, hD⟩
  refine ⟨by simpa only [writtenInExtChartAt_self_eq, extChartAt_self_apply] using
    hg.differentiableWithinAt_writtenInExtChartAt, ?_⟩
  rw [orientationAt_model, orientationAt_model] at hmap
  have hdet := (Orientation.map_eq_iff_det_pos μ D.toLinearEquiv hι).1 hmap
  rwa [← hg.mfderiv_eq_fderivWithin_self, ← hD]

/-- If a chart `e` of the maximal `C¹` atlas and a chart `e'` both carry the orientation `o` of
`M` to one constant orientation of the model at every point of their sources, then the coordinate
change from `e` to `e'` has positive Jacobian determinant on its source. -/
theorem orientationPreservingOn_symm_trans_of_isOrientationPreservingAt
    {o : Manifold.Orientation I M ι} {μ : Orientation ℝ E ι} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M)
    (ho : ∀ x ∈ e.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e x)
    (ho' : ∀ x ∈ e'.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e' x) :
    OrientationPreservingOn I (e.symm ≫ₕ e') (e.symm ≫ₕ e').source := by
  refine orientationPreservingOn_of_isOrientationPreservingAt μ o.card_eq fun z hz ↦ ?_
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source] at hz
  rw [OpenPartialHomeomorph.coe_trans]
  -- The chart `e`, as a partial diffeomorphism onto its image in the model.
  set Φ := e.toPartialDiffeomorph he
  have hΦ : IsOrientationPreservingAt o (model (I := I) μ o.card_eq) Φ (Φ.symm z) := by
    simpa [Φ] using ho _ (e.map_target hz.1)
  have hsymm := hΦ.partialDiffeomorph_symm (by simpa [Φ] using hz.1) one_ne_zero
  simp only [Φ, OpenPartialHomeomorph.coe_toPartialDiffeomorph_symm] at hsymm
  exact (ho' _ hz.2).comp hsymm

/-- Charts of the maximal `C¹` atlas which carry the orientation `o` of `M` to one constant
orientation of the model at every point of their sources change coordinates with positive
Jacobian determinant. -/
theorem symm_trans_mem_orientationPreservingGroupoid {o : Manifold.Orientation I M ι}
    {μ : Orientation ℝ E ι} {e e' : OpenPartialHomeomorph M H}
    (he : e ∈ IsManifold.maximalAtlas I 1 M) (he' : e' ∈ IsManifold.maximalAtlas I 1 M)
    (ho : ∀ x ∈ e.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e x)
    (ho' : ∀ x ∈ e'.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e' x) :
    e.symm ≫ₕ e' ∈ orientationPreservingGroupoid I := by
  rw [mem_orientationPreservingGroupoid_iff]
  refine ⟨orientationPreservingOn_symm_trans_of_isOrientationPreservingAt he ho ho', ?_⟩
  rw [← OpenPartialHomeomorph.symm_source, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]
  exact orientationPreservingOn_symm_trans_of_isOrientationPreservingAt he' ho' ho

/-- Let `c` be a chart of the maximal `C¹` atlas which reverses the orientation `o` against a
constant orientation `μ` of the model at every point of its source, and let `x` be a point of its
source with `I (c x)` in the interior of the range of `I`. Following `c` by a reflection of `E`
fixing `I (c x)` gives a chart of the maximal atlas around `x` which carries `o` to `μ` at every
point of its source. -/
theorem exists_mem_maximalAtlas_isOrientationPreservingAt_of_isOrientationReversingAt
    [Nontrivial E] {o : Manifold.Orientation I M ι} {μ : Orientation ℝ E ι}
    {c : OpenPartialHomeomorph M H} (hc : c ∈ IsManifold.maximalAtlas I 1 M)
    (hcr : ∀ y ∈ c.source, IsOrientationReversingAt o (model (I := I) μ o.card_eq) c y) {x : M}
    (hx : x ∈ c.source) (hxi : I (c x) ∈ interior (range I)) :
    ∃ e ∈ IsManifold.maximalAtlas I 1 M, x ∈ e.source ∧
      ∀ y ∈ e.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e y := by
  obtain ⟨g, hg⟩ := Module.exists_det_eq_neg_one (R := ℝ) (M := E) Module.finrank_pos
  set R : E ≃L[ℝ] E := g.toContinuousLinearEquiv
  have hR : LinearMap.det (R : E →ₗ[ℝ] E) < 0 := by
    simp [R, ← LinearEquiv.coe_det, hg]
  -- The reflection `A` of `E` along `R`, fixing `I (c x)`.
  set v₀ := I (c x)
  let A : E ≃ₜ E :=
    { toFun v := R (v - v₀) + v₀
      invFun v := R.symm (v - v₀) + v₀
      left_inv v := by simp
      right_inv v := by simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  have hA : A.toOpenPartialHomeomorph ∈ IsManifold.maximalAtlas 𝓘(ℝ, E) 1 E :=
    OpenPartialHomeomorph.mem_maximalAtlas_of_contMDiffOn _
      (ContDiff.contMDiff (f := fun v ↦ R (v - v₀) + v₀) (by fun_prop)).contMDiffOn
      (ContDiff.contMDiff (f := fun v ↦ R.symm (v - v₀) + v₀) (by fun_prop)).contMDiffOn
  have hchart : ⇑(((c.trans I.interiorChart).trans A.toOpenPartialHomeomorph).trans
      I.interiorChart.symm) = (I.symm ∘ A ∘ I) ∘ c := by
    simp only [OpenPartialHomeomorph.coe_trans, ModelWithCorners.interiorChart_coe,
      ModelWithCorners.interiorChart_coe_symm, Homeomorph.toOpenPartialHomeomorph_apply,
      Function.comp_assoc]
  refine ⟨((c.trans I.interiorChart).trans A.toOpenPartialHomeomorph).trans I.interiorChart.symm,
    OpenPartialHomeomorph.trans_interiorChart_trans_trans_interiorChart_symm_mem_maximalAtlas hc
      hA, ?_, fun y hy ↦ ?_⟩
  · have hAv₀ : A v₀ = v₀ := by simp [A]
    have hx' : (x ∈ c.source ∧ I (c x) ∈ interior (range I)) ∧
        A (I (c x)) ∈ interior (range I) := ⟨⟨hx, hxi⟩, hAv₀ ▸ hxi⟩
    simpa using hx'
  · have hy' : (y ∈ c.source ∧ I (c y) ∈ interior (range I)) ∧
        A (I (c y)) ∈ interior (range I) := by
      simpa using hy
    have hAd := (((R : E →L[ℝ] E).hasFDerivAt (x := I (c y) - v₀)).comp (I (c y))
      ((hasFDerivAt_id (I (c y))).sub_const v₀)).add_const v₀
    rw [ContinuousLinearMap.comp_id] at hAd
    rw [hchart]
    exact (isOrientationReversingAt_symm_comp_comp μ o.card_eq hAd hR hy'.1.2 hy'.2).comp
      (hcr y hy'.1.1)

section Boundaryless

variable [BoundarylessManifold I M]

/-- On a manifold without boundary modelled on a nontrivial space, the charts of the maximal
`C¹` atlas which carry an orientation `o` of `M` to a given constant orientation `μ` of the model at
every point of their sources form an oriented atlas. -/
theorem isOrientedAtlas_setOf_isOrientationPreservingAt [Nontrivial E]
    (o : Manifold.Orientation I M ι) (μ : Orientation ℝ E ι) :
    IsOrientedAtlas I 1 {e | e ∈ IsManifold.maximalAtlas I 1 M ∧
      ∀ x ∈ e.source, IsOrientationPreservingAt o (model (I := I) μ o.card_eq) e x} where
  subset_maximalAtlas _ he := he.1
  exists_mem_source x := by
    set c := chartAt H x
    have hc : c ∈ IsManifold.maximalAtlas I 1 M := IsManifold.chart_mem_maximalAtlas x
    have hcx : ContMDiffAt I I 1 c x := (contMDiffOn_of_mem_maximalAtlas hc).contMDiffAt
      (c.open_source.mem_nhds (mem_chart_source H x))
    -- Restricting `c` to the interior of the set where a property holds gives a chart of the
    -- maximal atlas around `x` with that property on its source, if it holds near `x`.
    have restr : ∀ {P : M → Prop}, (∀ᶠ y in 𝓝 x, P y) →
        c.restr (interior {y | P y}) ∈ IsManifold.maximalAtlas I 1 M ∧
          x ∈ (c.restr (interior {y | P y})).source ∧
            ∀ y ∈ (c.restr (interior {y | P y})).source, P y := fun hP ↦
      ⟨restr_mem_maximalAtlas _ hc isOpen_interior, by
        rw [c.restr_source' _ isOpen_interior]
        exact ⟨mem_chart_source H x, mem_interior_iff_mem_nhds.2 hP⟩, fun y hy ↦ by
        rw [c.restr_source' _ isOpen_interior] at hy
        exact interior_subset hy.2⟩
    rcases (c.isLocalDiffeomorphAt_of_mem_maximalAtlas hc (mem_chart_source H x)
      ).isOrientationPreservingAt_or_isOrientationReversingAt one_ne_zero o
        (model (I := I) μ o.card_eq) with hx | hx
    · -- Restrict the chart to the open set where it already preserves orientation.
      obtain ⟨he, hxe, hpres⟩ := restr (eventually_isOrientationPreservingAt hcx hx)
      exact ⟨_, ⟨he, hpres⟩, hxe⟩
    · -- Restrict the chart to the open set where it reverses orientation, then reflect.
      obtain ⟨hU, hxU, hrev⟩ := restr (eventually_isOrientationReversingAt hcx hx)
      obtain ⟨e, he, hxe, hpres⟩ :=
        exists_mem_maximalAtlas_isOrientationPreservingAt_of_isOrientationReversingAt hU hrev hxU
          (BoundarylessManifold.isInteriorPoint (x := x))
      exact ⟨e, ⟨he, hpres⟩, hxe⟩
  symm_trans_mem he he' := symm_trans_mem_orientationPreservingGroupoid he.1 he'.1 he.2 he'.2

/-- The oriented atlas of the charts which carry `o` to `μ` determines the orientation `o`
from the model orientation `μ`. -/
theorem orientation_isOrientedAtlas_setOf_isOrientationPreservingAt [Nontrivial E]
    (o : Manifold.Orientation I M ι) (μ : Orientation ℝ E ι) :
    (isOrientedAtlas_setOf_isOrientationPreservingAt o μ).orientation μ o.card_eq = o := by
  set hA := isOrientedAtlas_setOf_isOrientationPreservingAt o μ
  ext x
  obtain ⟨e, he, hx⟩ := hA.exists_mem_source x
  obtain ⟨L, hL, hmap⟩ := hA.orientation_spec μ o.card_eq he hx
  obtain ⟨D, hD, hDmap⟩ := (isOrientationPreservingAt_iff _ _ _ _).1 (he.2 x hx)
  rw [orientationAt_model] at hDmap
  obtain rfl : L = D := ContinuousLinearEquiv.coe_injective (hL.trans hD.symm)
  exact (Orientation.map ι L.toLinearEquiv).injective (hmap.trans hDmap.symm)

end Boundaryless

variable (I M) in
/-- **The oriented-atlas criterion.** A `C¹` manifold without boundary is orientable if and only
if it has an oriented atlas. -/
theorem orientable_iff_exists_atlas [BoundarylessManifold I M] :
    Orientable I M ↔ ∃ A : Set (OpenPartialHomeomorph M H), IsOrientedAtlas I 1 A := by
  refine ⟨fun ⟨⟨o⟩⟩ ↦ ?_, fun ⟨_, hA⟩ ↦ hA.orientable⟩
  rcases subsingleton_or_nontrivial E with hE | hE
  · exact ⟨_, isOrientedAtlas_maximalAtlas_of_subsingleton I 1 M⟩
  · exact ⟨_, isOrientedAtlas_setOf_isOrientationPreservingAt o (Module.finBasis ℝ E).orientation⟩

end OfOrientation

end TauCeti
