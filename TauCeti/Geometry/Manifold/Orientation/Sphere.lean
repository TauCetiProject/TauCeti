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
public import TauCeti.Geometry.Manifold.Orientation.TopForm
import Mathlib.Analysis.InnerProductSpace.TwoDim
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.DifferentialForm.Regularity
import TauCeti.Geometry.Manifold.Instances.Sphere
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
nowhere-vanishing top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)`, the pullback to `Sⁿ` of the
contraction of the volume form of `E` with the position vector, through
`TauCeti.Manifold.Orientation.ofTopForm`. Reversing `o` reverses it.

The antipodal map `u ↦ -u` pulls this top form back to `(-1)^(n+1)` times itself, since it negates
both the point `u` and the tangent vectors. So it preserves the outward-normal orientation of `Sⁿ`
when `n` is odd and reverses it when `n` is even. When `n ≥ 1` the sphere is connected
(`TauCeti.connectedSpace_sphere`), so it has exactly two orientations, and the antipodal map has
orientation sign `(-1)^(n+1)` for every orientation of `Sⁿ`. Since every point has exactly one
antipodal preimage, the antipodal map has degree `(-1)^(n+1)` at every value.

## Main declarations

* `Orientation.sphereOrientation`: the outward-normal orientation of the unit sphere.
* `Orientation.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent basis at `u` is
  positive exactly when `u` followed by its image in `E` has positive volume, and
  `Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff` its negative counterpart.
* `Complex.orientation_eq_orientationAt_sphereOrientation_iff`: a tangent vector `w` of the unit
  circle of `ℂ` at `z` is positive exactly when it points counterclockwise,
  `Re z Im w - Im z Re w > 0`.
* `Orientation.sphereOrientation_neg`: reversing `o` reverses the outward-normal orientation.
* `TauCeti.orientable_sphere`: the unit sphere is orientable.
* `Orientation.isOrientationPreservingAt_neg_sphere`,
  `Orientation.isOrientationReversingAt_neg_sphere`: the antipodal map of `Sⁿ` preserves the
  outward-normal orientation for odd `n` and reverses it for even `n`.
* `TauCeti.Manifold.Orientation.orientationSign_neg_sphere`: for `n ≥ 1` and every orientation of
  `Sⁿ`, the antipodal map has orientation sign `(-1)^(n+1)` at every point.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_neg_sphere`: for `n ≥ 1` the antipodal map
  of `Sⁿ` has degree `(-1)^(n+1)`.

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
private def radialVolumeForm (o : Orientation ℝ E (Fin (n + 1))) : RoughForm 𝓘(ℝ, E) E ℝ n :=
  fun x ↦ o.volumeFormL.curryLeft x

/-- The top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` on the unit sphere: the pullback along the
inclusion of the contraction of the volume form of `E` with the position vector. -/
private def sphereTopForm (o : Orientation ℝ E (Fin (n + 1))) :
    RoughForm (𝓡 n) (sphere (0 : E) 1) ℝ n :=
  mpullback (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (radialVolumeForm o)

private theorem sphereTopForm_apply (o : Orientation ℝ E (Fin (n + 1))) (u : sphere (0 : E) 1)
    (v : Fin n → TangentSpace (𝓡 n) u) :
    sphereTopForm o u v = o.volumeForm
      (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) := by
  rw [sphereTopForm, mpullback_apply]
  -- The radial form is `curryLeft` of the volume form, `Matrix.vecCons` is `Fin.cons`, and
  -- `mvfderiv` of the inclusion is its `mfderiv`, as `NormedSpace.fromTangentSpace` is the
  -- identity.
  exact (o.volumeFormL.curryLeft_apply_apply _ _).trans (o.volumeFormL_apply _)

private theorem isSmoothForm_sphereTopForm (o : Orientation ℝ E (Fin (n + 1))) :
    IsSmoothForm (𝓡 n) 0 (sphereTopForm o) :=
  (isSmoothForm_modelSpace_iff.2 (o.volumeFormL.curryLeft : E →L[ℝ] _).contDiff).mpullback
    contMDiff_coe_sphere

private theorem sphereTopForm_ne_zero (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) : sphereTopForm o u ≠ 0 := by
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) u) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  intro h
  have hb := DFunLike.congr_fun h ⇑b
  rw [sphereTopForm_apply] at hb
  exact Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u b.linearIndependent) (by simpa using hb)

/-- The **outward-normal orientation** of the unit sphere `Sⁿ` of an oriented real inner product
space `E` of dimension `n + 1`: a tangent basis `v₁, …, vₙ` at `u` is positive exactly when
`u, v₁, …, vₙ` is a positive basis of `E`
(`Orientation.orientation_eq_orientationAt_sphereOrientation_iff`). -/
def _root_.Orientation.sphereOrientation (o : Orientation ℝ E (Fin (n + 1))) :
    Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n) :=
  Manifold.Orientation.ofTopForm finrank_euclideanSpace_fin (sphereTopForm o)
    (isSmoothForm_sphereTopForm o) (sphereTopForm_ne_zero o)

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
    Manifold.Orientation.orientation_eq_orientationAt_ofTopForm_iff, sphereTopForm_apply]

/-- A tangent basis `v` of the unit sphere at `u` is negative for the outward-normal orientation
exactly when `u, v₁, …, vₙ`, read in `E` through the derivative of the inclusion, has negative
volume. -/
theorem _root_.Orientation.orientation_eq_neg_orientationAt_sphereOrientation_iff
    (o : Orientation ℝ E (Fin (n + 1))) {u : sphere (0 : E) 1}
    (v : Basis (Fin n) ℝ (TangentSpace (𝓡 n) u)) :
    v.orientation = -o.sphereOrientation.orientationAt u ↔
      o.volumeForm
        (Fin.cons (u : E) fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) < 0 := by
  rw [← Orientation.ne_iff_eq_neg _ _ (o.sphereOrientation.finrank_tangentSpace_eq u).symm, Ne,
    o.orientation_eq_orientationAt_sphereOrientation_iff, not_lt]
  exact (Orientation.volumeForm_apply_ne_zero_iff.2
    (LinearIndependent.finCons_mvfderiv_coe_sphere u v.linearIndependent)).le_iff_lt

/-- Reversing the orientation of `E` reverses the outward-normal orientation of its unit
sphere. -/
@[simp]
theorem _root_.Orientation.sphereOrientation_neg (o : Orientation ℝ E (Fin (n + 1))) :
    (-o).sphereOrientation = -o.sphereOrientation := by
  ext u
  have hcard := ((-o).sphereOrientation.finrank_tangentSpace_eq u).symm
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

/-- The antipodal map `u ↦ -u` pulls the top form `(v₁, …, vₙ) ↦ vol(u, v₁, …, vₙ)` of the sphere
back to `(-1)^(n+1)` times itself: it negates both the point and the tangent vectors. -/
private theorem mpullback_neg_sphereTopForm (o : Orientation ℝ E (Fin (n + 1)))
    (u : sphere (0 : E) 1) :
    mpullback (𝓡 n) (𝓡 n) (fun y : sphere (0 : E) 1 ↦ -y) (sphereTopForm o) u =
      ((-1 : ℝ) ^ (n + 1)) • sphereTopForm o u := by
  have hneg : MDifferentiableAt (𝓡 n) (𝓡 n) (fun y : sphere (0 : E) 1 ↦ -y) u :=
    (contMDiff_neg_sphere (m := 1)).mdifferentiableAt one_ne_zero
  have hcoe : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) (-u) :=
    (contMDiff_coe_sphere (m := 1)).mdifferentiableAt one_ne_zero
  -- The inclusion intertwines the antipodal maps of the sphere and of `E`.
  have hd (w : TangentSpace (𝓡 n) u) :
      mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (-u) (mfderiv (𝓡 n) (𝓡 n) (fun y ↦ -y) u w) =
        -mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u w := by
    have hcomp : ((↑) : sphere (0 : E) 1 → E) ∘ (fun y ↦ -y) = -((↑) : _ → E) :=
      funext fun y ↦ coe_neg_sphere y
    rw [← mvfderiv_comp_apply u hcoe hneg, hcomp, mvfderiv_neg, neg_apply]
  ext v
  rw [mpullback_apply, sphereTopForm_apply, ContinuousAlternatingMap.smul_apply,
    sphereTopForm_apply, coe_neg_sphere]
  simp_rw [hd]
  have hcons : (Fin.cons (-(u : E))
      (fun i ↦ -mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) : Fin (n + 1) → E) =
      fun i ↦ (-1 : ℝ) • (Fin.cons (u : E)
        (fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) u (v i)) : Fin (n + 1) → E) i := by
    ext i
    refine Fin.cases ?_ (fun i ↦ ?_) i <;> simp only [Fin.cons_zero, Fin.cons_succ, neg_one_smul]
  rw [hcons, AlternatingMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The antipodal map of an odd-dimensional sphere preserves the outward-normal
orientation.** -/
theorem _root_.Orientation.isOrientationPreservingAt_neg_sphere
    (o : Orientation ℝ E (Fin (n + 1))) (hn : Odd n) (u : sphere (0 : E) 1) :
    Manifold.Orientation.IsOrientationPreservingAt o.sphereOrientation o.sphereOrientation
      (fun y ↦ -y) u := by
  rw [Orientation.sphereOrientation]
  refine Manifold.Orientation.isOrientationPreservingAt_ofTopForm_of_mpullback_eq_smul _ _ _ _ _ _
    ?_ (mpullback_neg_sphereTopForm o u)
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
    ?_ (mpullback_neg_sphereTopForm o u)
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

/-- The unit sphere of a finite-dimensional real inner product space is orientable. -/
theorem orientable_sphere : Orientable (𝓡 n) (sphere (0 : E) 1) := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  constructor
  rw [finrank_euclideanSpace_fin]
  exact ⟨(finBasisOfFinrankEq ℝ E hE).orientation.sphereOrientation⟩

section Circle

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

end Circle

end TauCeti
