/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Manifold.LiouvilleMeasure
public import TauCeti.Geometry.Symplectic.Manifold.Sphere
import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere

/-!
# The symplectic area of the two-sphere

Let `E` be an oriented real inner product space of dimension three. The volume form
`vol(u, ·, ·)` of its unit sphere `S²` (`Orientation.sphereVolumeForm`) is a symplectic form. On a
surface the Liouville measure of a symplectic form is its measure `|σ|`
(`TauCeti.SmoothTwoForm.liouvilleMeasure_one`), so the area `4π` of the sphere
(`Orientation.measure_sphereVolumeForm_univ`, computed on the Riemann sphere) is its total
Liouville measure (`Orientation.liouvilleMeasure_sphereVolumeForm_univ`). Rescaling the form by
`r` gives Liouville measure `4π |r|` (`Orientation.liouvilleMeasure_smul_sphereVolumeForm_univ`).

For the unit sphere of `ℝ³`, the area form `σ_x(v, w) = x ⬝ (v × w)` (`TauCeti.sphereAreaForm`)
has area `4π` (`TauCeti.liouvilleMeasure_sphereAreaForm_univ`), and rescaled by `r` it has area
`4π |r|` (`TauCeti.liouvilleMeasure_smul_sphereAreaForm_univ`). By
`TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`, on the infinitesimal rotations, which span
every tangent plane, `r σ` is the Kirillov–Kostant–Souriau form of the coadjoint orbit of `SO(3)` of
radius `r`, carried to `S²` along `x ↦ r x`. So this is the KKS area `4π r` of that orbit.

## Main results

* `Orientation.liouvilleMeasure_sphereVolumeForm_univ`: the Liouville measure of `S²` is `4π`.
* `Orientation.liouvilleMeasure_smul_sphereVolumeForm_univ`: the volume form of `S²` scaled by `r`
  has Liouville measure `4π |r|`.
* `TauCeti.liouvilleMeasure_sphereAreaForm_univ`: the area form of the unit sphere of `ℝ³` has
  Liouville measure `4π`.
* `TauCeti.liouvilleMeasure_smul_sphereAreaForm_univ`: the area form of the unit sphere of `ℝ³`
  scaled by `r` has Liouville measure `4π |r|`.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2 (the coadjoint orbits of `SO(3)`).
-/

public section

noncomputable section

open Metric Module Set MeasureTheory
open scoped Manifold

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

section Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

/-- **The Liouville measure of the two-sphere is `4π`.** The volume form of the unit sphere of an
oriented three-dimensional inner product space, regarded as a symplectic form, has total Liouville
measure `4π`. -/
theorem _root_.Orientation.liouvilleMeasure_sphereVolumeForm_univ
    (o : Orientation ℝ E (Fin (2 + 1))) :
    SmoothTwoForm.liouvilleMeasure 1 o.sphereVolumeForm (univ : Set (sphere (0 : E) 1)) =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [SmoothTwoForm.liouvilleMeasure_one]
  exact o.measure_sphereVolumeForm_univ

/-- **The rescaled Liouville measure of the two-sphere.** The volume form of the unit sphere of an
oriented three-dimensional inner product space, scaled by `r`, has total Liouville measure
`4π |r|`. -/
theorem _root_.Orientation.liouvilleMeasure_smul_sphereVolumeForm_univ
    (o : Orientation ℝ E (Fin (2 + 1))) (r : ℝ) :
    SmoothTwoForm.liouvilleMeasure 1 (r • o.sphereVolumeForm) (univ : Set (sphere (0 : E) 1)) =
      ENNReal.ofReal (4 * Real.pi * |r|) := by
  rw [SmoothTwoForm.liouvilleMeasure_smul, smul_apply,
    o.liouvilleMeasure_sphereVolumeForm_univ, pow_one, smul_eq_mul,
    ← ENNReal.ofReal_mul (abs_nonneg r), mul_comm]

end Orientation

/-- **The area of the unit sphere of `ℝ³`.** The area form `σ_x(v, w) = x ⬝ (v × w)` of the unit
sphere of `ℝ³` has total Liouville measure `4π`. -/
theorem liouvilleMeasure_sphereAreaForm_univ :
    sphereAreaForm.liouvilleMeasure 1 (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      ENNReal.ofReal (4 * Real.pi) := by
  rw [sphereAreaForm_eq_sphereVolumeForm]
  exact Orientation.liouvilleMeasure_sphereVolumeForm_univ (E := EuclideanSpace ℝ (Fin 3)) _

/-- **The KKS area of the coadjoint spheres of `SO(3)`.** The area form `σ` of the unit sphere of
`ℝ³`, rescaled by `r`, has total Liouville measure `4π |r|`. On the infinitesimal rotations, which
span every tangent plane, `r σ` is the Kirillov–Kostant–Souriau form of the coadjoint orbit of
`SO(3)` of radius `r`, carried to the unit sphere along `x ↦ r x`
(`TauCeti.mul_eval₂_sphereAreaForm_sphereRotationAction`). So for `r > 0` that orbit has KKS area
`4π r`. -/
theorem liouvilleMeasure_smul_sphereAreaForm_univ (r : ℝ) :
    (r • sphereAreaForm).liouvilleMeasure 1
        (univ : Set (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) =
      ENNReal.ofReal (4 * Real.pi * |r|) := by
  rw [sphereAreaForm_eq_sphereVolumeForm]
  exact Orientation.liouvilleMeasure_smul_sphereVolumeForm_univ (E := EuclideanSpace ℝ (Fin 3)) _ r

end TauCeti
