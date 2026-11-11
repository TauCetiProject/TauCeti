/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Riesz
public import Mathlib.Analysis.InnerProductSpace.TwoDim

/-!
# Regularity of the right-angle rotation on an oriented Riemannian surface

An orientation `o` of a Riemannian surface orients every tangent plane (`orientationAt`), and
Mathlib's `Orientation.rightAngleRotation` rotates each tangent plane by `+π/2`. Applied to a
tangent vector field `s`, this rotation gives a field `J s` as regular as `s` and the metric
(`TauCeti.Manifold.Orientation.contMDiffAt_rightAngleRotation`,
`TauCeti.Manifold.Orientation.contMDiff_rightAngleRotation`).

The metric identifies `J s` with the Riesz dual of the covector `w ↦ vol(s, w)`, where `vol` is the
Riemannian volume form (`Orientation.inner_rightAngleRotation_left`). The regularity of `J s` thus
follows from that of the volume form (`TauCeti.isSmoothForm_riemannianVolumeForm`) and of the Riesz
dual (`Riemannian.Tensor.contMDiffAt_rieszDual`); no local frame appears in the statement.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapters 2 and 9.
-/

public section

open Bundle Set TauCeti
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.Manifold.Orientation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω} [IsManifold I 1 M] [IsManifold I (n + 1) M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I n E (TangentSpace I : M → Type _)]

/-- **The right-angle rotation preserves regularity at a point.** On a Riemannian surface with a
`C^n` metric, oriented by `o`, rotating a tangent vector field `s` by `+π/2` in each tangent plane
gives a field which is `C^n` at every point where `s` is. -/
theorem contMDiffAt_rightAngleRotation (o : Manifold.Orientation I M (Fin 2))
    {s : Π x : M, TangentSpace I x} {x : M} (hs : CMDiffAt n (T% s) x) :
    CMDiffAt n (T% (fun y ↦ letI := o.fact_finrank_tangentSpace y
      (o.orientationAt y).rightAngleRotation (s y))) x := by
  let Φ : Π y : M, TangentSpace I y →L[ℝ] ℝ := fun y ↦
    letI := o.fact_finrank_tangentSpace y
    (o.orientationAt y).areaForm' (s y)
  have hJ (y : M) : (letI := o.fact_finrank_tangentSpace y
      (o.orientationAt y).rightAngleRotation (s y)) =
        Riemannian.Tensor.rieszDual (I := I) y (Φ y) := by
    apply Riemannian.Tensor.eq_rieszDual_iff_inner_eq.mpr
    intro w
    let := o.fact_finrank_tangentSpace y
    exact (o.orientationAt y).inner_rightAngleRotation_left (s y) w
  have hd : ContMDiffAt I I.tangent n
      (fun y ↦ TotalSpace.mk' E y (Riemannian.Tensor.rieszDual (I := I) y (Φ y))) x := by
    apply Riemannian.Tensor.contMDiffAt_rieszDual x (mem_chart_source H x)
    intro j
    have hj := Riemannian.Tensor.contMDiffOn_chartLocalFrame (I := I) (n := n) x j
    rw [TangentBundle.trivializationAt_baseSet] at hj
    have hjx := hj.contMDiffAt ((chartAt H x).open_source.mem_nhds (mem_chart_source H x))
    have hvol := (isSmoothForm_riemannianVolumeForm (n := n) o).contMDiff x
    have heval := hvol.continuousAlternatingMap_bundle_apply
      (v := fun i y ↦ ![s y, Riemannian.Tensor.chartLocalFrame (I := I) x j y] i)
      (fun i ↦ by
        fin_cases i
        · exact hs
        · exact hjx)
    have hscalar := (contMDiffAt_totalSpace.mp heval).2
    convert hscalar using 1
    funext y
    dsimp only [Φ]
    let := o.fact_finrank_tangentSpace y
    rw [riemannianVolumeForm_apply, ← (o.orientationAt y).areaForm_to_volumeForm]
    rfl
  exact hd.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y ↦
    congrArg (TotalSpace.mk' E y) (hJ y))

/-- **The right-angle rotation preserves regularity.** On a Riemannian surface with a `C^n`
metric, oriented by `o`, rotating a `C^n` tangent vector field by `+π/2` in each tangent plane
gives a `C^n` field. -/
theorem contMDiff_rightAngleRotation (o : Manifold.Orientation I M (Fin 2))
    {s : Π x : M, TangentSpace I x} (hs : CMDiff n (T% s)) :
    CMDiff n (T% (fun x ↦ letI := o.fact_finrank_tangentSpace x
      (o.orientationAt x).rightAngleRotation (s x))) :=
  fun x ↦ o.contMDiffAt_rightAngleRotation (hs x)

end TauCeti.Manifold.Orientation
