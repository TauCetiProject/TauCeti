/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Orientation behavior in smooth families

In a jointly `C¹` family of maps between oriented manifolds, if every slice has an invertible
derivative at a fixed source point, its orientation behavior there is locally constant in the
parameter. On a preconnected parameter manifold it is therefore independent of the parameter.
No compactness, global injectivity, or boundarylessness is required.

This is the orientation step in moving embedded discs by a diffeotopy: a motion starting at
the identity preserves orientation throughout, so moving the centre does not change the
orientation class of the disc.

The coordinate argument follows the relative-determinant method of
`TauCeti.Manifold.Orientation.eventually_mapOrientation_map_symm_eq` in the pullback-orientation
construction, applied to the derivatives of the slices of a family.

## References

* M. W. Hirsch, *Differential Topology*, Chapter 4, §6 (the disc theorem).
* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Chapter 15 (orientations).
-/

public noncomputable section

open Bundle Filter Module
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M E' H' N V G P : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace G]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'}
  {L : ModelWithCorners ℝ V G}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  [TopologicalSpace P] [ChartedSpace G P] [IsManifold L 1 P]
  {ι : Type*} [Fintype ι]

/-- The orientation behavior of a jointly `C¹` family is locally constant in the parameter,
provided the derivatives of all slices are invertible at the chosen source point. -/
theorem isLocallyConstant_isOrientationPreservingAt
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    {F : P × M → N} (hF : ContMDiff (L.prod I) J 1 F) (x : M)
    (hD : ∀ p, (mfderiv I J (fun y => F (p, y)) x).IsInvertible) :
    IsLocallyConstant (fun p => IsOrientationPreservingAt o o' (fun y => F (p, y)) x) := by
  classical
  refine IsLocallyConstant.iff_eventually_eq _ |>.2 fun a => ?_
  let f : P → N := fun p => F (p, x)
  let D (p : P) := (hD p).choose
  have hDc (p : P) : (D p : TangentSpace I x →L[ℝ] TangentSpace J (f p)) =
      mfderiv I J (fun y => F (p, y)) x := (hD p).choose_spec
  let e := trivializationAt E (TangentSpace I) x
  let e' := trivializationAt E' (TangentSpace J) (f a)
  have hx : x ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' x
  have ha : f a ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f a)
  let T (p : P) (hp : f p ∈ e'.baseSet) : E ≃L[ℝ] E' :=
    ((e.continuousLinearEquivAt ℝ x hx).symm.trans (D p)).trans
      (e'.continuousLinearEquivAt ℝ (f p) hp)
  let η := e.mapOrientation ι hx (o.orientationAt x)
  have hread (p : P) (hp : f p ∈ e'.baseSet) :
      IsOrientationPreservingAt o o' (fun y => F (p, y)) x ↔
        _root_.Orientation.map ι (T p hp).toLinearEquiv η =
          e'.mapOrientation ι hp (o'.orientationAt (f p)) :=
    isOrientationPreservingAt_iff_map_eq o o' _ x (f a) (D p) (hDc p) hx hp
  -- The slice derivatives vary continuously when read in the fixed trivializations.
  let c := inTangentCoordinates I J (fun _ : P => x) f
    (fun p => mfderiv I J (fun y => F (p, y)) x) a
  have hc : ContinuousAt c a :=
    ((hF (a, x)).mfderiv (fun p y => F (p, y)) (fun _ => x)
      (m := 0) contMDiffAt_const (by simp)).continuousAt
  have hcT (p : P) (hp : f p ∈ e'.baseSet) : c p = (T p hp : E →L[ℝ] E') := by
    simp only [c, inTangentCoordinates]
    rw [ContinuousLinearMap.inCoordinates_eq hx hp]
    ext v
    simp [T, ← hDc p, e, e']
  -- Relative to the derivative at `a`, the derivative starts at the identity,
  -- so its determinant stays positive near `a`.
  let K : P → E →L[ℝ] E := fun p => ((T a ha).symm : E' →L[ℝ] E).comp (c p)
  have hKa : K a = ContinuousLinearMap.id ℝ E := by
    ext v
    simp [K, hcT a ha]
  have hK : ContinuousAt K a := continuousAt_const.clm_comp hc
  have hpos : ∀ᶠ p in 𝓝 a, 0 < (K p).det :=
    (ContinuousLinearMap.continuous_det.continuousAt.comp hK).eventually
      (lt_mem_nhds (by simp [hKa, ContinuousLinearMap.det]))
  have hf : Continuous f := hF.continuous.comp (continuous_id.prodMk continuous_const)
  have hbase : ∀ᶠ p in 𝓝 a, f p ∈ e'.baseSet :=
    hf.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds ha)
  -- The target orientation is locally constant in the same trivialization.
  have ho := o'.toVectorBundleOrientation.eventually_mapOrientation_eq o'.card_eq e' ha
  simp only [toVectorBundleOrientation_apply] at ho
  filter_upwards [hpos, hbase, (hf.tendsto a).eventually ho] with p hpos hp hop
  have hmaps := _root_.Orientation.map_eq_map_of_det_pos η (T p hp).toLinearEquiv
    (T a ha).toLinearEquiv o.card_eq (by
      convert hpos using 2
      ext v
      simp [K, hcT p hp])
  apply propext
  rw [hread p hp, hread a ha, hmaps, hop hp]

/-- In a preconnected smooth family with invertible slice derivatives at `x`, one slice
preserves orientation at `x` exactly when every other slice does. -/
theorem isOrientationPreservingAt_family_iff [PreconnectedSpace P]
    (o : Manifold.Orientation I M ι) (o' : Manifold.Orientation J N ι)
    {F : P × M → N} (hF : ContMDiff (L.prod I) J 1 F) (x : M)
    (hD : ∀ p, (mfderiv I J (fun y => F (p, y)) x).IsInvertible) (p q : P) :
    IsOrientationPreservingAt o o' (fun y => F (p, y)) x ↔
      IsOrientationPreservingAt o o' (fun y => F (q, y)) x :=
  ((isLocallyConstant_isOrientationPreservingAt o o' hF x hD).apply_eq_of_preconnectedSpace
    p q).to_iff

end TauCeti.Manifold.Orientation
