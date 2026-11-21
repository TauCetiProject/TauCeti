/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.Sphere
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
public import Mathlib.LinearAlgebra.CrossProduct
import TauCeti.Analysis.InnerProductSpace.Euclidean.CrossProduct
import TauCeti.Geometry.Symplectic.Manifold.Surface

/-!
# The volume form of a two-sphere is symplectic

Let `E` be an oriented real inner product space of dimension three. The volume form
`vol(u, ·, ·)` of its unit sphere (`Orientation.sphereVolumeForm`) is a nowhere-vanishing two-form
on a surface, so it is closed and nondegenerate
(`TauCeti.SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two`): the two-sphere is a
symplectic manifold.

For the unit sphere `S² ⊂ ℝ³` with the standard orientation of `ℝ³`, this volume form is the
**area form** `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`).

## Main definitions

* `TauCeti.sphereAreaForm`: the area form `σ_x(v, w) = x ⬝ (v × w)` of `S²`.

## Main results

* `Orientation.isSymplectic_sphereVolumeForm`: the volume form of a two-sphere is symplectic.
* `TauCeti.sphereAreaForm_eq_sphereVolumeForm`: the area form of `S²` is the volume form of the
  unit sphere for the standard orientation of `ℝ³`.
* `TauCeti.eval₂_sphereAreaForm`: the area form of `S²` is the triple product.
* `TauCeti.isSymplectic_sphereAreaForm`: the area form of `S²` is symplectic.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford University
  Press, 2017, Section 3.1 (area forms on surfaces).
-/

public section

noncomputable section

open Metric Module Matrix WithLp
open scoped Manifold EuclideanSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]

/-- **The volume form of a two-sphere is symplectic.** On the unit sphere of an oriented
three-dimensional real inner product space, the volume form `vol(u, ·, ·)` is a nowhere-vanishing
two-form on a surface, hence closed and nondegenerate. -/
theorem _root_.Orientation.isSymplectic_sphereVolumeForm (o : Orientation ℝ E (Fin (2 + 1))) :
    SmoothTwoForm.IsSymplectic o.sphereVolumeForm :=
  (SmoothTwoForm.isSymplectic_iff_forall_ne_zero_of_finrank_eq_two finrank_euclideanSpace_fin).2
    o.sphereVolumeForm_apply_ne_zero

/-! ### The area form of the unit sphere of `ℝ³` -/

/-- Euclidean three-space. -/
local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The unit sphere of `ℝ³`. -/
local notation "S²" => sphere (0 : ℝ³) 1

/-- The inclusion of the unit sphere into `ℝ³`. -/
local notation "ι" => ((↑) : S² → ℝ³)

/-- The **area form of the unit two-sphere** `S² ⊂ ℝ³`, `σ_x(v, w) = x ⬝ (v × w)`
(`TauCeti.eval₂_sphereAreaForm`): the volume form of the sphere for the outward normal and the
standard orientation of `ℝ³`. It is symplectic (`TauCeti.isSymplectic_sphereAreaForm`). -/
def sphereAreaForm : SmoothTwoForm (𝓡 2) S² :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm

/-- The area form of `S²` is the volume form of the unit sphere for the standard orientation of
`ℝ³`. -/
theorem sphereAreaForm_eq_sphereVolumeForm :
    sphereAreaForm = (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation.sphereVolumeForm :=
  (rfl)

/-- The area form of `S²` evaluates tangent vectors `v, w` at `x`, read in `ℝ³`, as the triple
product `x ⬝ (v × w)`. -/
theorem eval₂_sphereAreaForm (x : S²) (v w : TangentSpace (𝓡 2) x) :
    SmoothBundleForm.eval₂ sphereAreaForm x v w =
      ofLp (x : ℝ³) ⬝ᵥ ofLp (mvfderiv (𝓡 2) ι x v) ⨯₃ ofLp (mvfderiv (𝓡 2) ι x w) := by
  rw [SmoothBundleForm.eval₂_apply, sphereAreaForm, Orientation.sphereVolumeForm_apply,
    ← EuclideanSpace.volumeForm_basisFun_orientation_three]
  congr 1
  ext i : 1
  fin_cases i <;> rfl

/-- The area form of `S²` is symplectic. -/
theorem isSymplectic_sphereAreaForm : sphereAreaForm.IsSymplectic :=
  Orientation.isSymplectic_sphereVolumeForm _

end TauCeti
