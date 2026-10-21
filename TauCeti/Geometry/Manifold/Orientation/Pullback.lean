/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Preserving
public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# Pulling back orientations

Let `f : M → M'` be a `C¹` map between manifolds with corners whose manifold derivative is
invertible at every point. An orientation `o'` of `M'` pulls back to an orientation of `M`: the
tangent orientation at `x` is the one carried to `o'`'s tangent orientation at `f x` by the
derivative of `f` at `x`. It is the unique orientation of `M` for which `f` preserves orientation
at every point [Lee, Prop. 15.15].

Local diffeomorphisms of class `C^n`, `n ≠ 0`, are the main examples, through
`IsLocalDiffeomorph.isInvertible_mfderiv`. The weaker hypothesis also covers maps that are not
local diffeomorphisms at boundary points, such as the inclusion of a closed ball into its ambient
space, whose image is not open.

The local constancy of the pulled-back tangent orientations holds for any family of orientations
of the tangent spaces of `M'` along `f` that is locally constant in trivializations
(`TauCeti.Manifold.Orientation.eventually_mapOrientation_map_symm_eq`), not only for those of an
orientation of `M'`; this is the form needed for orientations defined fibrewise, such as the
canonical orientation of an orientation double cover.

## Main definitions

* `TauCeti.Manifold.Orientation.pullback`: the pullback of an orientation along a `C¹` map with
  everywhere invertible derivative.

## Main results

* `TauCeti.Manifold.Orientation.isOrientationPreservingAt_pullback`: `f` preserves orientation
  from the pullback orientation.
* `TauCeti.Manifold.Orientation.eq_pullback_iff`: the pullback is the only orientation from which
  `f` preserves orientation everywhere.
* `TauCeti.Manifold.Orientation.eq_neg_pullback_iff`: its opposite is the only orientation from
  which `f` reverses orientation everywhere.
* `TauCeti.Manifold.Orientation.pullback_id`, `TauCeti.Manifold.Orientation.pullback_comp`:
  functoriality.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 15.15.
-/

public section

noncomputable section

open Bundle Filter Module
open scoped Manifold Topology

namespace TauCeti.Manifold.Orientation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [FiniteDimensional ℝ E]
  {E' H' M' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' 1 M'] [FiniteDimensional ℝ E']
  {E'' H'' M'' : Type*} [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [TopologicalSpace H''] {I'' : ModelWithCorners ℝ E'' H''} [TopologicalSpace M'']
  [ChartedSpace H'' M''] [IsManifold I'' 1 M''] [FiniteDimensional ℝ E'']
  {ι : Type*} [Fintype ι]

omit [FiniteDimensional ℝ E'] in
/-- Let `f` be a map that is `C¹` at `a` and whose derivative at each `x` is the equivalence `D x`,
and let `ω x` be an orientation of the tangent space of `M'` at `f x`, locally constant near `a`
when read in the preferred trivialization at `f a`. Then the orientations of the tangent spaces of
`M` obtained by transporting `ω x` back along `D x` are locally constant near `a` when read in the
preferred trivialization at `a`. -/
theorem eventually_mapOrientation_map_symm_eq {f : M → M'} {a : M}
    (hf : ContMDiffAt I I' 1 f a)
    (D : ∀ x, TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (hD : ∀ x, (D x : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x)
    (hι : Fintype.card ι = finrank ℝ E)
    (ω : ∀ x, _root_.Orientation ℝ (TangentSpace I' (f x)) ι)
    (hω : ∀ᶠ x in 𝓝 a, ∀ hx : f x ∈ (trivializationAt E' (TangentSpace I') (f a)).baseSet,
      (trivializationAt E' (TangentSpace I') (f a)).mapOrientation ι hx (ω x) =
        (trivializationAt E' (TangentSpace I') (f a)).mapOrientation ι
          (FiberBundle.mem_baseSet_trivializationAt' (f a)) (ω a)) :
    ∀ᶠ x in 𝓝 a, ∀ hx : x ∈ (trivializationAt E (TangentSpace I) a).baseSet,
      (trivializationAt E (TangentSpace I) a).mapOrientation ι hx
          (_root_.Orientation.map ι (D x).symm.toLinearEquiv (ω x)) =
        (trivializationAt E (TangentSpace I) a).mapOrientation ι
          (FiberBundle.mem_baseSet_trivializationAt' a)
          (_root_.Orientation.map ι (D a).symm.toLinearEquiv (ω a)) := by
  set e := trivializationAt E (TangentSpace I) a
  set e' := trivializationAt E' (TangentSpace I') (f a)
  have ha : a ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt' a
  have hfa : f a ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' (f a)
  -- The derivative read in the two trivializations.
  let T (x : M) (hx : x ∈ e.baseSet) (hfx : f x ∈ e'.baseSet) : E ≃L[ℝ] E' :=
    ((e.continuousLinearEquivAt ℝ x hx).symm.trans (D x)).trans
      (e'.continuousLinearEquivAt ℝ (f x) hfx)
  -- Reading in the trivializations transports `ω x` back along `T`.
  have hread (x : M) (hx : x ∈ e.baseSet) (hfx : f x ∈ e'.baseSet) :
      e.mapOrientation ι hx (_root_.Orientation.map ι (D x).symm.toLinearEquiv (ω x)) =
        _root_.Orientation.map ι (T x hx hfx).symm.toLinearEquiv
          (e'.mapOrientation ι hfx (ω x)) := by
    rw [Trivialization.mapOrientation_apply, Trivialization.mapOrientation_apply,
      ← _root_.Orientation.map_trans, ← _root_.Orientation.map_trans]
    exact congrArg (fun L ↦ _root_.Orientation.map ι L (ω x))
      (LinearEquiv.ext fun v ↦ by simp [T, e'.symm_apply_apply_mk hfx])
  let c := inTangentCoordinates I I' id f (mfderiv I I' f) a
  have hc : ContinuousAt c a := (hf.mfderiv_const (m := 0) (by simp)).continuousAt
  have hcT (x : M) (hx : x ∈ e.baseSet) (hfx : f x ∈ e'.baseSet) :
      c x = (T x hx hfx : E →L[ℝ] E') := by
    simp only [c, inTangentCoordinates, id]
    rw [ContinuousLinearMap.inCoordinates_eq hx hfx]
    ext v
    simp [T, ← hD x, e, e']
  -- In the two trivializations the derivative varies continuously, so relative to its value at
  -- `a` it has positive determinant near `a`.
  let K : M → E →L[ℝ] E := fun x ↦ ((T a ha hfa).symm : E' →L[ℝ] E).comp (c x)
  have hKa : K a = ContinuousLinearMap.id ℝ E := by
    ext v
    simp [K, hcT a ha hfa]
  have hpos : ∀ᶠ x in 𝓝 a, 0 < (K x).det := by
    have hK : ContinuousAt K a := continuousAt_const.clm_comp hc
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp hK).eventually
      (lt_mem_nhds (by simp [hKa, ContinuousLinearMap.det]))
  have hbase : ∀ᶠ x in 𝓝 a, x ∈ e.baseSet := e.open_baseSet.mem_nhds ha
  have hfbase : ∀ᶠ x in 𝓝 a, f x ∈ e'.baseSet :=
    hf.continuousAt.preimage_mem_nhds (e'.open_baseSet.mem_nhds hfa)
  filter_upwards [hω, hpos, hbase, hfbase] with x hωx hKx hx₀ hfx hx
  rw [hread x hx hfx, hread a ha hfa, hωx hfx]
  set ω' := e'.mapOrientation ι hfa (ω a)
  set η := _root_.Orientation.map ι (T a ha hfa).symm.toLinearEquiv ω'
  set L := (T x hx hfx).trans (T a ha hfa).symm
  -- The change of reading `L = (T a)⁻¹ ∘ T x` fixes `η`, since its determinant is positive.
  have hfix : _root_.Orientation.map ι L.toLinearEquiv η = η := by
    refine (_root_.Orientation.map_eq_iff_det_pos η _ hι).mpr ?_
    convert hKx using 2
    ext v
    simp [L, K, hcT x hx hfx]
  calc _root_.Orientation.map ι (T x hx hfx).symm.toLinearEquiv ω'
      = _root_.Orientation.map ι L.symm.toLinearEquiv η := by
        rw [← _root_.Orientation.map_trans]
        exact congrArg (fun L ↦ _root_.Orientation.map ι L ω')
          (LinearEquiv.ext fun v ↦ by simp [L])
    _ = η := by
        rw [ContinuousLinearEquiv.toLinearEquiv_symm, ← _root_.Orientation.map_symm,
          Equiv.symm_apply_eq, hfix]

open Classical in
/-- The pullback of an orientation `o'` of `M'` along a `C¹` map `f : M → M'` whose manifold
derivative is invertible at every point: the tangent orientation at `x` is carried to that of `o'`
at `f x` by the derivative of `f` (`map_orientationAt_pullback`). It is the unique orientation
from which `f` preserves orientation everywhere (`eq_pullback_iff`). For a `C^n` local
diffeomorphism, `n ≠ 0`, invertibility of the derivative is
`IsLocalDiffeomorph.isInvertible_mfderiv`.

The hypothesis `hι` says that `ι` indexes orientations of the model of `M`; it follows from the
invertibility of the derivative unless `M` is empty. -/
def pullback (o' : Orientation I' M' ι) {f : M → M'} (hf : ContMDiff I I' 1 f)
    (hdf : ∀ x, (mfderiv I I' f x).IsInvertible) (hι : Fintype.card ι = finrank ℝ E) :
    Orientation I M ι :=
  -- The model orientation only selects a representative lift, which the quotient forgets.
  ofVectorBundleOrientation
    (((finBasisOfFinrankEq ℝ E hι.symm).reindex (Fintype.equivFin ι).symm).orientation) hι
    ⟨fun x ↦ _root_.Orientation.map ι (hdf x).choose.symm.toLinearEquiv (o'.orientationAt (f x)),
      fun a ↦ by
        have h := o'.toVectorBundleOrientation.eventually_mapOrientation_eq o'.card_eq
          (trivializationAt E' (TangentSpace I') (f a))
          (FiberBundle.mem_baseSet_trivializationAt' (f a))
        simp only [toVectorBundleOrientation_apply] at h
        exact eventually_mapOrientation_map_symm_eq (hf a) (fun x ↦ (hdf x).choose)
          (fun x ↦ (hdf x).choose_spec) hι _ ((hf.continuous.tendsto a).eventually h)⟩

variable (o' : Orientation I' M' ι) {f : M → M'} (hf : ContMDiff I I' 1 f)
  (hdf : ∀ x, (mfderiv I I' f x).IsInvertible) (hι : Fintype.card ι = finrank ℝ E)

/-- The derivative of `f` carries the tangent orientations of the pullback orientation to those of
the original orientation. -/
theorem map_orientationAt_pullback (x : M) (D : TangentSpace I x ≃L[ℝ] TangentSpace I' (f x))
    (hD : (D : TangentSpace I x →L[ℝ] TangentSpace I' (f x)) = mfderiv I I' f x) :
    _root_.Orientation.map ι D.toLinearEquiv ((o'.pullback hf hdf hι).orientationAt x) =
      o'.orientationAt (f x) := by
  have hDx : (hdf x).choose = D :=
    ContinuousLinearEquiv.coe_injective ((hdf x).choose_spec.trans hD.symm)
  simp only [pullback, orientationAt_ofVectorBundleOrientation, VectorBundleOrientation.coe_mk,
    hDx, ContinuousLinearEquiv.toLinearEquiv_symm, ← _root_.Orientation.map_symm,
    Equiv.apply_symm_apply]

/-- A map preserves orientation at every point from the pullback orientation. -/
@[simp]
theorem isOrientationPreservingAt_pullback (x : M) :
    IsOrientationPreservingAt (o'.pullback hf hdf hι) o' f x :=
  (isOrientationPreservingAt_iff_of_coe_eq _ o' f x (hdf x).choose (hdf x).choose_spec).mpr
    (map_orientationAt_pullback o' hf hdf hι x _ (hdf x).choose_spec)

/-- The pullback orientation is the only orientation from which `f` preserves orientation at
every point. -/
theorem eq_pullback_iff {o : Orientation I M ι} :
    o = o'.pullback hf hdf hι ↔ ∀ x, IsOrientationPreservingAt o o' f x := by
  refine ⟨fun h ↦ h ▸ isOrientationPreservingAt_pullback o' hf hdf hι, fun h ↦ ?_⟩
  ext x
  obtain ⟨D, hD, hx⟩ := (isOrientationPreservingAt_iff o o' f x).mp (h x)
  apply (_root_.Orientation.map ι D.toLinearEquiv).injective
  rw [hx, map_orientationAt_pullback o' hf hdf hι x D hD]

/-- The opposite of the pullback orientation is the only orientation from which `f` reverses
orientation at every point. -/
theorem eq_neg_pullback_iff {o : Orientation I M ι} :
    o = -o'.pullback hf hdf hι ↔ ∀ x, IsOrientationReversingAt o o' f x := by
  rw [← neg_eq_iff_eq_neg, eq_pullback_iff]
  simp only [isOrientationPreservingAt_neg_left]

/-- Pulling back the opposite orientation gives the opposite of the pullback orientation. -/
@[simp]
theorem pullback_neg : (-o').pullback hf hdf hι = -o'.pullback hf hdf hι :=
  (eq_neg_pullback_iff o' hf hdf hι).mpr fun x ↦
    (isOrientationPreservingAt_neg_right _ o' f x).mp
      (isOrientationPreservingAt_pullback (-o') hf hdf hι x)

/-- Pulling back along the identity does nothing. -/
@[simp]
theorem pullback_id (o : Orientation I M ι) (hf : ContMDiff I I 1 (id : M → M))
    (hdf : ∀ x, (mfderiv I I (id : M → M) x).IsInvertible) (hι : Fintype.card ι = finrank ℝ E) :
    o.pullback hf hdf hι = o :=
  ((eq_pullback_iff o hf hdf hι).mpr (isOrientationPreservingAt_id o)).symm

/-- Pulling back along a composite is pulling back successively. -/
theorem pullback_comp (o'' : Orientation I'' M'' ι) {g : M' → M''} (hg : ContMDiff I' I'' 1 g)
    (hdg : ∀ y, (mfderiv I' I'' g y).IsInvertible) (hι' : Fintype.card ι = finrank ℝ E') :
    (o''.pullback hg hdg hι').pullback hf hdf hι =
      o''.pullback (hg.comp hf) (fun x ↦ isInvertible_mfderiv_comp (hdg (f x)) (hdf x)) hι :=
  (eq_pullback_iff o'' (hg.comp hf) _ hι).mpr fun x ↦
    (isOrientationPreservingAt_pullback o'' hg hdg hι' (f x)).comp
      (isOrientationPreservingAt_pullback _ hf hdf hι x)

end TauCeti.Manifold.Orientation
