/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Category.TopCat.Sphere
public import TauCeti.Geometry.Sphere.LinearIsometry

/-!
# Identification of the unit circle in two-dimensional Euclidean space with the complex circle

The unit sphere `sphere (0 : EuclideanSpace ℝ (Fin 2)) 1` is isometric to Mathlib's complex unit
circle `Circle = {z : ℂ | ‖z‖ = 1}` via the standard orthonormal basis isometry
`Complex.orthonormalBasisOneI`.

## Main declarations

* `TauCeti.Sphere1`, `TauCeti.Sphere1.east`: the unit circle in `ℝ²` and its point `(1, 0)`.
* `TauCeti.EuclideanSpace.sphereIsometryEquivCircle`: the isometry equivalence between the unit
  circle in two-dimensional Euclidean space and `Circle`.
* `TauCeti.EuclideanSpace.sphereHomeomorphCircle`: the homeomorphism between the unit circle in
  two-dimensional Euclidean space and `Circle`.
* `TauCeti.EuclideanSpace.coe_sphereIsometryEquivCircle_apply`: forward evaluation of the
  isometry equivalence on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_apply`: forward evaluation of the
  homeomorphism on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereIsometryEquivCircle_symm_apply`: backward evaluation of the
  isometry equivalence on underlying points.
* `TauCeti.EuclideanSpace.coe_sphereHomeomorphCircle_symm_apply`: backward evaluation of the
  homeomorphism on underlying points.
* `TauCeti.EuclideanSpace.sphereIsometryEquivCircle_neg`: the isometry equivalence negates under
  the antipodal map.
* `TauCeti.EuclideanSpace.sphereHomeomorphCircle_neg`: the homeomorphism negates under
  the antipodal map.
* `TauCeti.sphereOneHomeomorphCircle`, `TauCeti.sphereOneIsoCircle`: Mathlib's circle
  `TopCat.sphere 1` is homeomorphic, and isomorphic in `TopCat`, to `Circle`, lifted to the same
  universe.
* `TauCeti.sphereOnePiIsoCirclePi`: the torus `ι → TopCat.sphere 1` is isomorphic in `TopCat` to
  the torus `ι → Circle`, lifted to the same universe.
-/

public section

namespace TauCeti

open Metric
open scoped EuclideanSpace

/-- The unit circle `S¹ ⊆ ℝ²`. -/
abbrev Sphere1 : Type := sphere (0 : EuclideanSpace ℝ (Fin 2)) 1

/-- The point `(1, 0)` of the unit circle. -/
noncomputable def Sphere1.east : Sphere1 := ⟨EuclideanSpace.single 0 1, by simp⟩

/-- The point `(1, 0)` of the unit circle, as a vector of `ℝ²`. -/
@[simp]
theorem Sphere1.coe_east :
    (Sphere1.east : EuclideanSpace ℝ (Fin 2)) = EuclideanSpace.single 0 1 := by
  rw [Sphere1.east]

namespace EuclideanSpace

noncomputable section

/-- The unit circle in two-dimensional real Euclidean space is isometric to Mathlib's complex
unit circle `Circle`.

Note: `Circle` is by definition the unit sphere `sphere (0 : ℂ) 1` in `ℂ`
(via `Submonoid.unitSphere ℂ`), so the metric and topological instances agree definitionally
with those on `sphere (0 : ℂ) 1`. The type ascription `Circle` is therefore definitionally equal
to `sphere (0 : ℂ) 1`. -/
def sphereIsometryEquivCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ᵢ Circle :=
  LinearIsometryEquiv.unitSphereIsometryEquiv Complex.orthonormalBasisOneI.repr.symm

/-- The unit circle in two-dimensional real Euclidean space is homeomorphic to Mathlib's complex
unit circle `Circle`. -/
def sphereHomeomorphCircle :
    sphere (0 : EuclideanSpace ℝ (Fin 2)) 1 ≃ₜ Circle :=
  sphereIsometryEquivCircle.toHomeomorph

/-- The Euclidean-circle isometry is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma coe_sphereIsometryEquivCircle_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereIsometryEquivCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  LinearIsometryEquiv.coe_unitSphereIsometryEquiv_apply Complex.orthonormalBasisOneI.repr.symm x

/-- The Euclidean-circle homeomorphism is the standard orthonormal-coordinate isometry on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_apply
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    (sphereHomeomorphCircle x : ℂ) = Complex.orthonormalBasisOneI.repr.symm x :=
  coe_sphereIsometryEquivCircle_apply x

/-- The inverse Euclidean-circle isometry is the standard coordinate representation on
underlying points. -/
@[simp]
lemma coe_sphereIsometryEquivCircle_symm_apply (z : Circle) :
    (sphereIsometryEquivCircle.symm z : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (z : ℂ) := by
  apply Complex.orthonormalBasisOneI.repr.symm.injective
  rw [← coe_sphereIsometryEquivCircle_apply, IsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.symm_apply_apply]

/-- The inverse Euclidean-circle homeomorphism is the standard coordinate representation on
underlying points. -/
@[simp]
lemma coe_sphereHomeomorphCircle_symm_apply (z : Circle) :
    (sphereHomeomorphCircle.symm z : EuclideanSpace ℝ (Fin 2)) =
      Complex.orthonormalBasisOneI.repr (z : ℂ) :=
  coe_sphereIsometryEquivCircle_symm_apply z

/-- The Euclidean-circle isometry negates under the antipodal map. -/
@[simp]
lemma sphereIsometryEquivCircle_neg
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereIsometryEquivCircle (-x) = -(sphereIsometryEquivCircle x) := by
  ext
  simp [map_neg]

/-- The Euclidean-circle homeomorphism negates under the antipodal map. -/
@[simp]
lemma sphereHomeomorphCircle_neg
    (x : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1) :
    sphereHomeomorphCircle (-x) = -(sphereHomeomorphCircle x) :=
  sphereIsometryEquivCircle_neg x

end

end EuclideanSpace

section TopCatSphere

/-! ### Mathlib's circle `TopCat.sphere 1` -/

noncomputable section

universe u

/-- Mathlib's circle `TopCat.sphere 1`, the unit circle of `ℝ²` lifted to universe `u`, is
homeomorphic to Mathlib's complex unit circle `Circle` lifted to the same universe. -/
def sphereOneHomeomorphCircle : TopCat.sphere.{u} 1 ≃ₜ ULift.{u} Circle :=
  (Homeomorph.ulift.trans EuclideanSpace.sphereHomeomorphCircle).trans Homeomorph.ulift.symm

@[simp]
lemma sphereOneHomeomorphCircle_apply_down (x : TopCat.sphere.{u} 1) :
    (sphereOneHomeomorphCircle x).down = EuclideanSpace.sphereHomeomorphCircle x.down :=
  (rfl)

@[simp]
lemma sphereOneHomeomorphCircle_symm_apply_down (z : ULift.{u} Circle) :
    (sphereOneHomeomorphCircle.symm z).down = EuclideanSpace.sphereHomeomorphCircle.symm z.down :=
  (rfl)

/-- Mathlib's circle `TopCat.sphere 1` is isomorphic in `TopCat` to Mathlib's complex unit circle
`Circle`, lifted to the same universe. -/
def sphereOneIsoCircle : TopCat.sphere.{u} 1 ≅ TopCat.of (ULift.{u} Circle) :=
  TopCat.isoOfHomeo sphereOneHomeomorphCircle

@[simp]
lemma sphereOneIsoCircle_hom_apply (x : TopCat.sphere.{u} 1) :
    sphereOneIsoCircle.hom x = sphereOneHomeomorphCircle x :=
  (rfl)

@[simp]
lemma sphereOneIsoCircle_inv_apply (z : ULift.{u} Circle) :
    sphereOneIsoCircle.inv z = sphereOneHomeomorphCircle.symm z :=
  (rfl)

/-- The torus `ι → TopCat.sphere 1` is isomorphic in `TopCat` to the torus `ι → Circle`, with
`Circle` lifted to the same universe, by `TauCeti.sphereOneHomeomorphCircle` in each factor. -/
def sphereOnePiIsoCirclePi (ι : Type u) :
    TopCat.of (ι → TopCat.sphere.{u} 1) ≅ TopCat.of (ι → ULift.{u} Circle) :=
  TopCat.isoOfHomeo (Homeomorph.piCongrRight fun _ ↦ sphereOneHomeomorphCircle)

@[simp]
lemma sphereOnePiIsoCirclePi_hom_apply {ι : Type u} (x : ι → TopCat.sphere.{u} 1) (i : ι) :
    (sphereOnePiIsoCirclePi ι).hom x i = sphereOneHomeomorphCircle (x i) :=
  (rfl)

@[simp]
lemma sphereOnePiIsoCirclePi_inv_apply {ι : Type u} (z : ι → ULift.{u} Circle) (i : ι) :
    (sphereOnePiIsoCirclePi ι).inv z i = sphereOneHomeomorphCircle.symm (z i) :=
  (rfl)

end

end TopCatSphere

end TauCeti
