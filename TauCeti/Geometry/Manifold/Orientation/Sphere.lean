/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Instances.Sphere
public import Mathlib.LinearAlgebra.Complex.Orientation
public import TauCeti.Analysis.InnerProductSpace.Orientation
public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Instances.Sphere
public import TauCeti.Geometry.Manifold.Orientation.TopForm
public import TauCeti.Geometry.Diffeomorphism.Sphere
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Sphere.Connected

/-!
# The outward-normal orientation of a unit sphere and the antipodal map

Let `E` be an oriented real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`.
The tangent space of `Sⁿ` at `u` is carried by the derivative of the inclusion onto the
hyperplane `u^⊥` (`range_mvfderiv_subtypeVal`), and `u` itself is the outward normal there. The
*outward-normal orientation* `o.sphereOrientation` declares a tangent basis
`v₁, …, vₙ` at `u` positive exactly when `u, v₁, …, vₙ` is a positive basis of `E`
(`Orientation.orientation_eq_orientationAt_sphereOrientation_iff`), the convention by which
`o.orthogonalSpanSingleton` orients the hyperplane `u^⊥`.

Putting the outward normal first is the usual convention for the boundary orientation of the
closed unit ball. For the unit circle of `ℂ` with its standard orientation, the
positive tangent direction at `z` is `i z`, the counterclockwise one
(`Complex.orientation_eq_orientationAt_sphereOrientation_iff`). Mathlib's stereographic
atlas of the sphere is not coherently oriented, so the orientation is constructed instead from the
nowhere-vanishing top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` (`Orientation.sphereVolumeForm`),
the pullback to `Sⁿ` of the contraction of the volume form of `E` with the position vector,
through `TauCeti.Manifold.Orientation.ofTopForm`. Reversing `o` reverses it.

A linear isometry `e` of `E`, restricted to the sphere, pulls this top form back to `det e` times
itself, since it acts by `e` on both the point `u` and the tangent vectors. So it preserves the
outward-normal orientation when `det e > 0` and reverses it when `det e < 0`; for instance, a
reflection across a hyperplane, or complex conjugation on the unit circle of `ℂ`, reverses it.
The antipodal map `u ↦ -u` is the restriction of `-1`, of determinant `(-1)^(n+1)`. So it
preserves the outward-normal orientation of `Sⁿ` when `n` is odd and reverses it when `n` is even.
When `n ≥ 1` the sphere is connected (`TauCeti.connectedSpace_sphere`), so it has exactly two
orientations, and the antipodal map has orientation sign `(-1)^(n+1)` for every orientation of
`Sⁿ`. Since every point has exactly one antipodal preimage, the antipodal map has degree
`(-1)^(n+1)` at every value, and every value is regular, so its mapping degree `TauCeti.degree` is
`(-1)^(n+1)`.

## Main declarations

* `Orientation.sphereVolumeForm`: the nowhere-vanishing top form `vol(u, ·)` of the unit sphere.
* `Orientation.sphereVolumeForm_neg`: reversing the orientation of `E` negates it.
* `Orientation.mpullback_unitSphereEquiv_sphereVolumeForm`: a linear isometry `e` pulls the
  volume form of `Sⁿ` back to `det e` times itself.
* `Orientation.isOrientationPreservingAt_unitSphereEquiv`,
  `Orientation.isOrientationReversingAt_unitSphereEquiv`: a linear isometry preserves the
  outward-normal orientation when its determinant is positive and reverses it when negative.
* `Orientation.mpullback_neg_sphereVolumeForm`: the antipodal map pulls the volume form of `Sⁿ`
  back to `(-1)^(n+1)` times itself.
* `Orientation.sphereOrientation`: the outward-normal orientation of the unit sphere.
* `Orientation.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent basis at `u` is
  positive exactly when `u` followed by its image in `E` has positive volume, and
  `Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff` its negative counterpart.
* `Complex.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent vector `w` of the unit
  circle of `ℂ` at `z` is positive exactly when it points counterclockwise,
  `Re z Im w - Im z Re w > 0`, equivalently `Im (conj z * w) > 0`
  (`Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul`).
* `TauCeti.circleTangentBasis`: a positively oriented tangent basis of the unit circle of `ℂ`.
* `TauCeti.isOrientationPreservingAt_sphere_iff_im_conj_mul`,
  `TauCeti.isOrientationReversingAt_sphere_iff_im_conj_mul`: a self-map of the unit circle of `ℂ`
  with nonvanishing derivative preserves (reverses) orientation at `z` exactly when it carries a
  counterclockwise tangent vector at `z` to a counterclockwise (clockwise) one.
* `TauCeti.isOrientationReversingAt_conjSphere`, `TauCeti.orientationSign_conjSphere`,
  `TauCeti.degreeAtRegularValue_conjSphere`, `TauCeti.degree_conjSphere`: complex conjugation
  reverses the orientation of the unit circle and has orientation sign and mapping degree `-1`.
* `Orientation.sphereOrientation_neg`: reversing `o` reverses the outward-normal orientation.
* `TauCeti.orientable_sphere`: the unit sphere is orientable.
* `Orientation.isOrientationPreservingAt_neg_sphere`,
  `Orientation.isOrientationReversingAt_neg_sphere`: the antipodal map of `Sⁿ` preserves the
  outward-normal orientation for odd `n` and reverses it for even `n`.
* `TauCeti.Manifold.Orientation.orientationSign_neg_sphere`: for `n ≥ 1` and every orientation of
  `Sⁿ`, the antipodal map has orientation sign `(-1)^(n+1)` at every point.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_neg_sphere`: for `n ≥ 1` the antipodal map
  of `Sⁿ` has degree `(-1)^(n+1)`.
* `TauCeti.Manifold.Orientation.degree_neg_sphere`: for `n ≥ 1` the mapping degree of the
  antipodal map of `Sⁿ` is `(-1)^(n+1)`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 15 (orientations from nonvanishing top forms, outward normals and
  boundary orientations) and Chapter 17, section Degree Theory (the degree of the antipodal map).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
* M. Spivak, *Calculus on Manifolds*, Benjamin, 1965, Chapter 5 (outward normals and the
  orientation of a boundary).
-/

public section

noncomputable section

open Metric Module
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- The contraction `x ↦ vol(x, ·)` of the volume form of `E` with the position vector. -/
private def radialVolumeForm (o : Orientation ℝ E (Fin (n + 1))) : SmoothForm 𝓘(ℝ, E) E ℝ n :=
  ⟨fun x ↦ o.volumeFormL.curryLeft x,
    (isSmoothForm_modelSpace_iff.2
      (o.volumeFormL.curryLeft : E →L[ℝ] _).contDiff).mem_smoothBundleForms⟩

/-- The **volume form of the unit sphere** `Sⁿ` of an oriented real inner product space `E` of
dimension `n + 1`: the top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` at `u`, with the tangent vectors
read in `E` (`Orientation.sphereVolumeForm_apply`). It is the pullback along the inclusion of the
contraction of the volume form of `E` with the position vector, it vanishes nowhere
(`Orientation.sphereVolumeForm_apply_ne_zero`), and it defines the outward-normal orientation
`Orientation.sphereOrientation`. -/
def _root_.Orientation.sphereVolumeForm (o : Orientation ℝ E (Fin (n + 1))) :
    SmoothForm (𝓡 n) (sphere (0 : E) 1) ℝ n :=
  SmoothForm.mpullback ((↑) : sphere (0 : E) 1 → E) contMDiff_coe_sphere (radialVolumeForm o)

/-- The volume form of the unit sphere evaluates tangent vectors `v₁, …, vₙ` at `u` as
`vol(u, v₁, …, vₙ)`, with the tangent vectors read in `E` through the derivative of the
inclusion. -/
@[simp]
theorem _root_.Orientation.sphereVolumeForm_apply (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) (v : Fin n → TangentSpace (𝓡 n) u) :
    o.sphereVolumeForm.val u v = o.volumeForm
      (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [Orientation.sphereVolumeForm, SmoothForm.mpullback_apply]
  -- The radial form is `curryLeft` of the volume form, `Matrix.vecCons` is `Fin.cons`, and
  -- `mvfderiv` of the inclusion is its `mfderiv`, as `NormedSpace.fromTangentSpace` is the
  -- identity.
  exact (o.volumeFormL.curryLeft_apply_apply _ _).trans (o.volumeFormL_apply _)

/-- The volume form of the unit sphere vanishes nowhere. -/
theorem _root_.Orientation.sphereVolumeForm_apply_ne_zero (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) : o.sphereVolumeForm.val u ≠ 0 := by
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [Orientation.sphereVolumeForm_apply] at hb
  exact Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u b.linearIndependent) (by simpa using hb)

/-- Reversing the orientation of `E` negates the volume form of its unit sphere. -/
@[simp]
theorem _root_.Orientation.sphereVolumeForm_neg (o : Orientation ℝ E (Fin (n + 1))) :
    (-o).sphereVolumeForm = -o.sphereVolumeForm := by
  refine Subtype.ext (funext fun u ↦ ?_)
  ext v
  simp [Orientation.volumeForm_neg_orientation]

/-- The **outward-normal orientation** of the unit sphere `Sⁿ` of an oriented real inner product
space `E` of dimension `n + 1`: a tangent basis `v₁, …, vₙ` at `u` is positive exactly when
`u, v₁, …, vₙ` is a positive basis of `E`
(`Orientation.orientation_eq_orientationAt_sphereOrientation_iff`). -/
def _root_.Orientation.sphereOrientation (o : Orientation ℝ E (Fin (n + 1))) :
    Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n) :=
  Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin o.sphereVolumeForm.val
    (o.sphereVolumeForm.isSmoothForm.of_le zero_le) o.sphereVolumeForm_apply_ne_zero

/-- A tangent basis `v` of the unit sphere at `u` is positive for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has positive
volume, that is, is a positive basis of `E`. -/
theorem _root_.Orientation.orientation_eq_orientationAt_sphereOrientation_iff
    (o : Orientation ℝ E (Fin (n + 1))) {u : sphere (0 : E) 1}
    (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = o.sphereOrientation.orientationAt u ↔
      0 < o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [Orientation.sphereOrientation,
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff,
    Orientation.sphereVolumeForm_apply]

/-- A tangent basis `v` of the unit sphere at `u` is negative for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has negative
volume. -/
theorem _root_.Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff
    (o : Orientation ℝ E (Fin (n + 1))) {u : sphere (0 : E) 1}
    (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = -o.sphereOrientation.orientationAt u ↔
      o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) < 0 := by
  rw [← Orientation.ne_iff_eq_neg _ _
      (Nat.card_eq_fintype_card.trans (o.sphereOrientation.finrank_tangentSpace_eq u).symm), Ne,
    o.orientation_eq_orientationAt_sphereOrientation_iff, not_lt]
  exact (Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u v.linearIndependent)).le_iff_lt

/-- Reversing the orientation of `E` reverses the outward-normal orientation of its unit
sphere. -/
@[simp]
theorem _root_.Orientation.sphereOrientation_neg (o : Orientation ℝ E (Fin (n + 1))) :
    (-o).sphereOrientation = -o.sphereOrientation := by
  ext u
  have hcard :=
    Nat.card_eq_fintype_card.trans ((-o).sphereOrientation.finrank_tangentSpace_eq u).symm
  let v := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  -- A tangent basis is positive for `-o` exactly when it is negative for `o`.
  have h : v.orientation = (-o).sphereOrientation.orientationAt u ↔
      v.orientation = -o.sphereOrientation.orientationAt u := by
    rw [o.orientation_eq_neg_orientationAt_sphereOrientation_iff, ← neg_pos, ← neg_apply,
      ← Orientation.volumeForm_neg_orientation,
      (-o).orientation_eq_orientationAt_sphereOrientation_iff]
  rw [Manifold.Orientation.orientationAt_neg]
  rcases v.orientation.eq_or_eq_neg ((-o).sphereOrientation.orientationAt u) hcard with hv | hv
  · exact hv.symm.trans (h.mp hv)
  · have hne : v.orientation ≠ (-o).sphereOrientation.orientationAt u := fun h' ↦
      Module.Ray.ne_neg_self _ (h'.symm.trans hv)
    have hpos := (Orientation.ne_iff_eq_neg _ _ hcard).mp (mt h.mpr hne)
    rw [neg_neg] at hpos
    rw [← hpos, hv]
    exact (neg_neg (G := Orientation ℝ (TangentSpace (𝓡 n) u) (Fin n)) _).symm

/-- A linear isometry `e` of `E`, restricted to the unit sphere, pulls the volume form
`(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` of the sphere back to `det e` times itself: it acts by `e` on
the point and, read in `E`, on the tangent vectors. -/
theorem _root_.Orientation.mpullback_unitSphereEquiv_sphereVolumeForm
    (o : Orientation ℝ E (Fin (n + 1))) (e : E ≃ₗᵢ[ℝ] E) (u : sphere (0 : E) 1) :
    mpullback (𝓡 n) (𝓡 n) e.unitSphereEquiv o.sphereVolumeForm.val u =
      LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E) • o.sphereVolumeForm.val u := by
  ext v
  rw [mpullback_apply, Orientation.sphereVolumeForm_apply, ContinuousAlternatingMap.smul_apply,
    Orientation.sphereVolumeForm_apply, LinearIsometryEquiv.coe_unitSphereEquiv_apply,
    smul_eq_mul, ← Orientation.volumeForm_comp_linearMap, Fin.comp_cons]
  simp_rw [LinearIsometryEquiv.mvfderiv_coe_sphere_unitSphereEquiv, Function.comp_def,
    LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]

/-- **A linear isometry of positive determinant preserves the outward-normal orientation of the
unit sphere.** -/
theorem _root_.Orientation.isOrientationPreservingAt_unitSphereEquiv
    (o : Orientation ℝ E (Fin (n + 1))) {e : E ≃ₗᵢ[ℝ] E}
    (he : 0 < LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E)) (u : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationPreservingAt o.sphereOrientation o.sphereOrientation
      e.unitSphereEquiv u := by
  rw [Orientation.sphereOrientation]
  exact Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    he (o.mpullback_unitSphereEquiv_sphereVolumeForm e u)

/-- **A linear isometry of negative determinant reverses the outward-normal orientation of the
unit sphere.** For instance, a reflection across a hyperplane reverses it. -/
theorem _root_.Orientation.isOrientationReversingAt_unitSphereEquiv
    (o : Orientation ℝ E (Fin (n + 1))) {e : E ≃ₗᵢ[ℝ] E}
    (he : LinearMap.det (e.toLinearEquiv : E →ₗ[ℝ] E) < 0) (u : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationReversingAt o.sphereOrientation o.sphereOrientation
      e.unitSphereEquiv u := by
  rw [Orientation.sphereOrientation]
  exact Manifold.Orientation.isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    he (o.mpullback_unitSphereEquiv_sphereVolumeForm e u)

/-- The antipodal map `u ↦ -u` pulls the volume form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` of the
sphere back to `(-1)^(n+1)` times itself: it is the restriction of `-1`, of determinant
`(-1)^(n+1)`. -/
theorem _root_.Orientation.mpullback_neg_sphereVolumeForm (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) :
    mpullback (𝓡 n) (𝓡 n) (fun y : sphere (0 : E) 1 ↦ -y) o.sphereVolumeForm.val u =
      ((-1 : ℝ) ^ (n + 1)) • o.sphereVolumeForm.val u := by
  have hneg : (fun y : sphere (0 : E) 1 ↦ -y) = (LinearIsometryEquiv.neg ℝ).unitSphereEquiv :=
    funext fun y ↦ Subtype.ext (by simp)
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have hdet : LinearMap.det ((LinearIsometryEquiv.neg ℝ (E := E)).toLinearEquiv : E →ₗ[ℝ] E) =
      (-1) ^ (n + 1) := by
    rw [show ((LinearIsometryEquiv.neg ℝ (E := E)).toLinearEquiv : E →ₗ[ℝ] E) =
        (-1 : ℝ) • LinearMap.id from LinearMap.ext fun x ↦ by simp, LinearMap.det_smul,
      LinearMap.det_id, mul_one, (Fact.out : finrank ℝ E = n + 1)]
  rw [hneg, o.mpullback_unitSphereEquiv_sphereVolumeForm, hdet]

/-- **The antipodal map of an odd-dimensional sphere preserves the outward-normal
orientation.** -/
theorem _root_.Orientation.isOrientationPreservingAt_neg_sphere
    (o : Orientation ℝ E (Fin (n + 1))) (hn : Odd n) (u : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationPreservingAt o.sphereOrientation o.sphereOrientation
      (fun y ↦ -y) u := by
  rw [Orientation.sphereOrientation]
  refine Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    ?_ (o.mpullback_neg_sphereVolumeForm u)
  rw [hn.add_one.neg_one_pow]
  exact one_pos

/-- **The antipodal map of an even-dimensional sphere reverses the outward-normal
orientation.** -/
theorem _root_.Orientation.isOrientationReversingAt_neg_sphere
    (o : Orientation ℝ E (Fin (n + 1))) (hn : Even n) (u : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationReversingAt o.sphereOrientation o.sphereOrientation
      (fun y ↦ -y) u := by
  rw [Orientation.sphereOrientation]
  refine Manifold.Orientation.isOrientationReversingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    ?_ (o.mpullback_neg_sphereVolumeForm u)
  rw [hn.add_one.neg_one_pow]
  exact neg_one_lt_zero

/-- **The orientation sign of the antipodal map.** For `n ≥ 1` and every orientation of the
connected sphere `Sⁿ`, the antipodal map has orientation sign `(-1)^(n+1)` at every point. -/
@[simp]
theorem Manifold.Orientation.orientationSign_neg_sphere [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (u : sphere (0 : E) 1) :
    orientationSign o o (fun y ↦ -y) u = (-1) ^ (n + 1) := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have := connectedSpace_sphere (E := E) n
  -- Compare `o` with the outward-normal orientation of an orientation of `E`.
  let oE := (finBasisOfFinrankEq ℝ E hE).orientation
  have key : orientationSign oE.sphereOrientation oE.sphereOrientation (fun y ↦ -y) u =
      (-1) ^ (n + 1) := by
    rcases Nat.even_or_odd n with hn | hn
    · rw [orientationSign_of_isOrientationReversingAt (oE.isOrientationReversingAt_neg_sphere hn u),
        hn.add_one.neg_one_pow]
    · rw [orientationSign_of_isOrientationPreservingAt
        (oE.isOrientationPreservingAt_neg_sphere hn u), hn.add_one.neg_one_pow]
  rcases o.eq_or_eq_neg oE.sphereOrientation with rfl | rfl
  · exact key
  · rw [orientationSign_neg_left, orientationSign_neg_right, neg_neg, key]

/-- **The degree of the antipodal map.** For `n ≥ 1` and every orientation of `Sⁿ`, the antipodal
map has degree `(-1)^(n+1)` at every value: its only preimage is the antipodal point. -/
@[simp]
theorem Manifold.Orientation.degreeAtRegularValue_neg_sphere [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (y : sphere (0 : E) 1) :
    degreeAtRegularValue o o (fun x ↦ -x) y = (-1) ^ (n + 1) := by
  rw [degreeAtRegularValue_eq_sum (s := {-y}) fun x ↦ by
    rw [Finset.mem_singleton, neg_eq_iff_eq_neg], Finset.sum_singleton,
    orientationSign_neg_sphere]

/-- **The mapping degree of the antipodal map.** For `n ≥ 1` and every orientation of `Sⁿ`, the
antipodal map has mapping degree `(-1)^(n+1)`. -/
@[simp]
theorem Manifold.Orientation.degree_neg_sphere [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) :
    degree o o (fun x : sphere (0 : E) 1 ↦ -x) = (-1) ^ (n + 1) := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  -- Every point is regular, since the orientation sign `(-1)^(n+1)` is nonzero.
  have hreg (y : sphere (0 : E) 1) : IsRegularValue (𝓡 n) (𝓡 n)
      (fun x : sphere (0 : E) 1 ↦ -x) y := isRegularValue_iff.2 fun x _ ↦
    (isRegularPoint_iff_isInvertible_mfderiv rfl).2 <| not_not.1 <|
      orientationSign_eq_zero_iff.not.1 <| (orientationSign_neg_sphere o x).trans_ne (by simp)
  obtain ⟨y⟩ := (connectedSpace_sphere (E := E) n).toNonempty
  rw [degree_eq_degreeAtRegularValue_choose ⟨y, hreg y⟩, degreeAtRegularValue_neg_sphere]

/-- The unit sphere of a finite-dimensional real inner product space is orientable. -/
theorem orientable_sphere : Orientable (𝓡 n) (sphere (0 : E) 1) := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  constructor
  rw [finrank_euclideanSpace_fin]
  exact ⟨(finBasisOfFinrankEq ℝ E hE).orientation.sphereOrientation⟩

section Circle

open scoped ComplexConjugate

attribute [local instance] finrank_real_complex_fact'

/-- A tangent basis `c` of the unit circle of `ℂ` at `z` is positive for the outward-normal
orientation exactly when its vector `w`, read in `ℂ`, points counterclockwise:
`Re z Im w - Im z Re w > 0`. So the positive direction at `z` is that of `i z`. -/
theorem _root_.Complex.orientation_eq_orientationAt_sphereOrientation_iff
    {z : sphere (0 : ℂ) 1} (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z)) :
    c.orientation = Complex.orientation.sphereOrientation.orientationAt z ↔
      0 < (z : ℂ).re * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).im -
        (z : ℂ).im * (mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).re := by
  have hcons : (Fin.cons (z : ℂ) fun i ↦ mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z
      (c i) : Fin 2 → ℂ) = ![(z : ℂ), mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)] := by
    ext i
    fin_cases i <;> rfl
  rw [Complex.orientation.orientation_eq_orientationAt_sphereOrientation_iff, hcons,
    ← Orientation.areaForm_to_volumeForm, Complex.areaForm]
  generalize mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0) = w
  simp [Complex.mul_im]

/-- A tangent basis `c` of the unit circle of `ℂ` at `z` is positive for the outward-normal
orientation exactly when its vector `w`, read in `ℂ`, has positive counterclockwise component
`Im (conj z * w)`. -/
theorem _root_.Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul
    {z : sphere (0 : ℂ) 1} (c : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z)) :
    c.orientation = Complex.orientation.sphereOrientation.orientationAt z ↔
      0 < (conj (z : ℂ) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).im := by
  rw [Complex.orientation_eq_orientationAt_sphereOrientation_iff, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, neg_mul, ← sub_eq_add_neg]

/-- A positively oriented tangent basis of the unit circle of `ℂ` at `z`
(`TauCeti.orientation_circleTangentBasis`). -/
def circleTangentBasis (z : sphere (0 : ℂ) 1) : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) z) :=
  (finBasisOfFinrankEq ℝ (TangentSpace (𝓡 1) z)
    ((Complex.orientation.sphereOrientation.finrank_tangentSpace_eq z).trans
      (Fintype.card_fin 1))).adjustToOrientation
      (Complex.orientation.sphereOrientation.orientationAt z)

/-- The tangent basis `TauCeti.circleTangentBasis z` of the unit circle is positively oriented. -/
theorem orientation_circleTangentBasis (z : sphere (0 : ℂ) 1) :
    (circleTangentBasis z).orientation = Complex.orientation.sphereOrientation.orientationAt z :=
  Basis.orientation_adjustToOrientation _ _

/-- A self-map `f` of the unit circle of `ℂ` whose derivative at `z` does not vanish carries the
positive tangent basis `TauCeti.circleTangentBasis z` to a tangent basis at `f z`. -/
private theorem exists_basis_mfderiv_circleTangentBasis {f : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1}
    {z : sphere (0 : ℂ) 1} (hf : mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0) ≠ 0) :
    ∃ b' : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) (f z)),
      ∀ i, mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z i) = b' i := by
  refine ⟨basisOfLinearIndependentOfCardEqFinrank
    ((linearIndependent_unique_iff
      (v := fun _ : Fin 1 ↦ mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0))).2 hf)
    ((Fintype.card_fin 1).trans
      (Complex.orientation.sphereOrientation.finrank_tangentSpace_eq (f z)).symm), fun i ↦ ?_⟩
  fin_cases i
  simp

/-- **Orientation preservation on the circle.** A self-map `f` of the unit circle of `ℂ` whose
derivative at `z` does not vanish preserves the counterclockwise orientation at `z` exactly when
the image of the positive tangent vector, read in `ℂ` as `w`, points counterclockwise at `f z`:
`Im (conj (f z) * w) > 0`. -/
theorem isOrientationPreservingAt_sphere_iff_im_conj_mul {f : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1}
    {z : sphere (0 : ℂ) 1} (hf : mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0) ≠ 0) :
    Manifold.Orientation.IsOrientationPreservingAt Complex.orientation.sphereOrientation
        Complex.orientation.sphereOrientation f z ↔
      0 < (conj (f z : ℂ) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) (f z)
        (mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0))).im := by
  obtain ⟨b', hb'⟩ := exists_basis_mfderiv_circleTangentBasis hf
  rw [Manifold.Orientation.isOrientationPreservingAt_iff_of_basis _ b' hb',
    iff_true_left (orientation_circleTangentBasis z),
    Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul, hb']

/-- **Orientation reversal on the circle.** A self-map `f` of the unit circle of `ℂ` whose
derivative at `z` does not vanish reverses the counterclockwise orientation at `z` exactly when
the image of the positive tangent vector, read in `ℂ` as `w`, points clockwise at `f z`:
`Im (conj (f z) * w) < 0`. -/
theorem isOrientationReversingAt_sphere_iff_im_conj_mul {f : sphere (0 : ℂ) 1 → sphere (0 : ℂ) 1}
    {z : sphere (0 : ℂ) 1} (hf : mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0) ≠ 0) :
    Manifold.Orientation.IsOrientationReversingAt Complex.orientation.sphereOrientation
        Complex.orientation.sphereOrientation f z ↔
      (conj (f z : ℂ) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) (f z)
        (mfderiv (𝓡 1) (𝓡 1) f z (circleTangentBasis z 0))).im < 0 := by
  obtain ⟨b', hb'⟩ := exists_basis_mfderiv_circleTangentBasis hf
  -- `b'` is negative exactly when the basis `-b'` is positive.
  rw [Manifold.Orientation.isOrientationReversingAt_iff_of_basis _ b' hb',
    iff_true_left (orientation_circleTangentBasis z), ← neg_eq_iff_eq_neg (a := b'.orientation),
    ← b'.orientation_neg_single 0,
    Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul, hb',
    Basis.unitsSMul_apply]
  simp only [Function.update_self, Units.smul_def, Units.val_neg, Units.val_one, neg_one_smul,
    map_neg]
  rw [mul_neg, Complex.neg_im, neg_pos]

/-- Complex conjugation, restricted to the unit circle, reverses its orientation: it is the
restriction of a linear isometry of `ℂ` of determinant `-1`. -/
theorem isOrientationReversingAt_conjSphere (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationReversingAt Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation conjSphere z := by
  have h : conjSphere = Complex.conjLIE.unitSphereEquiv := funext fun w ↦ Subtype.ext (by simp)
  rw [h]
  exact Complex.orientation.isOrientationReversingAt_unitSphereEquiv
    (by rw [Complex.det_conjLIE]; exact neg_one_lt_zero) z

/-- Complex conjugation `conjSphere` on `sphere (0 : ℂ) 1` has orientation sign `-1` at every
point, for either orientation `o` of the circle. -/
@[simp]
theorem orientationSign_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.orientationSign o o conjSphere z = -1 := by
  have := connectedSpace_sphere (E := ℂ) 1
  have hstd : Manifold.Orientation.orientationSign Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation conjSphere z = -1 :=
    Manifold.Orientation.orientationSign_of_isOrientationReversingAt
      (isOrientationReversingAt_conjSphere z)
  rcases o.eq_or_eq_neg Complex.orientation.sphereOrientation with rfl | rfl
  · exact hstd
  · rw [Manifold.Orientation.orientationSign_neg_left,
      Manifold.Orientation.orientationSign_neg_right, neg_neg, hstd]

/-- Complex conjugation `conjSphere` on `sphere (0 : ℂ) 1` has degree `-1` at every value. -/
@[simp]
theorem degreeAtRegularValue_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (y : sphere (0 : ℂ) 1) :
    degreeAtRegularValue o o conjSphere y = -1 := by
  rw [degreeAtRegularValue_eq_sum (s := {conjSphere y}) fun x ↦ by
    rw [Finset.mem_singleton]
    exact ⟨fun h ↦ by rw [h, conjSphere_conjSphere],
      fun h ↦ by rw [← h, conjSphere_conjSphere]⟩,
    Finset.sum_singleton, orientationSign_conjSphere]

/-- **Degree of complex conjugation on `S¹`.** On `sphere (0 : ℂ) 1`, complex conjugation
`z ↦ conj z` has smooth mapping degree `-1` for every orientation `o`. -/
@[simp]
theorem degree_conjSphere (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) :
    degree o o conjSphere = -1 := by
  have hreg (y : sphere (0 : ℂ) 1) : IsRegularValue (𝓡 1) (𝓡 1) conjSphere y :=
    isRegularValue_iff.2 fun z _ ↦ (isRegularPoint_iff_isInvertible_mfderiv rfl).2 <|
      not_not.1 <| Manifold.Orientation.orientationSign_eq_zero_iff (o := o) (o' := o).not.1 <|
        (orientationSign_conjSphere o z).trans_ne (by decide)
  rw [degree_eq_degreeAtRegularValue_choose ⟨⟨1, by simp⟩, hreg _⟩, degreeAtRegularValue_conjSphere]

end Circle

end TauCeti
