/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Sphere.Connected

/-!
# The degree of the power maps of the circle

The unit circle `S¹ = sphere (0 : ℂ) 1` is a group, and for every integer `k` the power map
`z ↦ z ^ k` is a smooth self-map of it (`TauCeti.contMDiff_zpow_sphere`). Read in `ℂ`, its
derivative at `z` is multiplication by `k z ^ (k - 1)` (`TauCeti.mvfderiv_coe_zpow_sphere_apply`).
A self-map of the circle preserves (reverses) orientation at `z` exactly when it carries a tangent
vector `w` at `z` with `Im (conj z * w) > 0` to a counterclockwise (clockwise) one
(`TauCeti.isOrientationPreservingAt_sphere_iff_im_conj_mul`), and since `conj z = z⁻¹` on the
circle, `Im (conj (z ^ k) * k z ^ (k - 1) w) = k Im (conj z * w)`. So the power map preserves the
orientation of the circle at every point when `k > 0` and reverses it when `k < 0`, and its
orientation sign is `Int.sign k` everywhere, for each of the two orientations of the circle
(`TauCeti.Manifold.Orientation.orientationSign_zpow_sphere`).

For `k ≠ 0` the fibre over `1` consists of the `|k|` roots of unity of order dividing `|k|`, so
the signed count of that fibre is `|k| · sign k = k`. Every value is regular, and the degree does
not depend on the regular value, so the power map `z ↦ z ^ k` has degree `k` at every value and
mapping degree `k` (`TauCeti.Manifold.Orientation.degree_zpow_sphere`); for `k = 0` the map is
constant and both are `0`. In particular `z ↦ z ^ n` has degree `n` for `n : ℕ`; for `k = -1`
this recovers `TauCeti.degree_conjSphere`, since complex conjugation is `z ↦ z⁻¹` on the circle.

## Main results

* `TauCeti.isOrientationPreservingAt_zpow_sphere`, `TauCeti.isOrientationReversingAt_zpow_sphere`:
  the power map preserves the counterclockwise orientation for `k > 0` and reverses it for
  `k < 0`.
* `TauCeti.Manifold.Orientation.orientationSign_zpow_sphere`: for every orientation of the
  circle, the orientation sign of `z ↦ z ^ k` is `Int.sign k` at every point.
* `TauCeti.isRegularValue_zpow_sphere`: for `k ≠ 0` every value of `z ↦ z ^ k` is regular.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_zpow_sphere`,
  `TauCeti.Manifold.Orientation.degree_zpow_sphere`: the power map `z ↦ z ^ k` has degree `k`.
* `TauCeti.Manifold.Orientation.degree_pow_sphere`: `z ↦ z ^ n` has degree `n` for `n : ℕ`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Chapter 17, section Degree Theory.
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5.
-/

public section

noncomputable section

open Metric Module
open scoped Manifold ComplexConjugate ContDiff

namespace TauCeti

attribute [local instance] finrank_real_complex_fact'

/-- Read in `ℂ`, the derivative of `z ↦ z ^ k` multiplies the counterclockwise component
`Im (conj z * w)` of a tangent vector `w` at `z` by `k`. -/
private theorem im_conj_mul_mvfderiv_zpow_sphere (k : ℤ) (z : sphere (0 : ℂ) 1)
    (v : TangentSpace (𝓡 1) z) :
    (conj ((z ^ k : sphere (0 : ℂ) 1) : ℂ) *
        mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) (z ^ k)
          (mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z v)).im =
      k * (conj (z : ℂ) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z v).im := by
  -- On the circle `conj z = z⁻¹`, so `conj (z ^ k) * k z ^ (k - 1) = k * conj z`.
  have key : conj ((z ^ k : sphere (0 : ℂ) 1) : ℂ) * (k * (z : ℂ) ^ (k - 1)) =
      k * conj (z : ℂ) := by
    rw [Metric.unitSphere.coe_zpow, mul_left_comm, mul_comm (conj _),
      Complex.zpow_mul_conj_zpow_of_mem_sphere z.property, show k - 1 - k = -1 by ring,
      zpow_neg_one, Complex.inv_eq_conj (norm_eq_of_mem_sphere z)]
  rw [mvfderiv_coe_zpow_sphere_apply, ← mul_assoc, key, mul_assoc]
  simp

/-- For `k ≠ 0`, the derivative of `z ↦ z ^ k` does not vanish on the positive tangent vector
`TauCeti.circleTangentBasis z 0`. -/
private theorem mfderiv_zpow_sphere_circleTangentBasis_ne_zero {k : ℤ} (hk : k ≠ 0)
    (z : sphere (0 : ℂ) 1) :
    mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z (circleTangentBasis z 0) ≠ 0 :=
  fun h0 ↦ by
    have him := im_conj_mul_mvfderiv_zpow_sphere k z (circleTangentBasis z 0)
    rw [h0, map_zero, mul_zero, Complex.zero_im] at him
    exact (mul_ne_zero (Int.cast_ne_zero.2 hk)
      ((Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul _).1
        (orientation_circleTangentBasis z)).ne') him.symm

/-- **The positive power maps preserve the orientation of the circle.** For `k > 0`, the map
`z ↦ z ^ k` preserves the counterclockwise orientation of the unit circle of `ℂ` at every
point. -/
theorem isOrientationPreservingAt_zpow_sphere {k : ℤ} (hk : 0 < k) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationPreservingAt Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z := by
  rw [isOrientationPreservingAt_sphere_iff_im_conj_mul
    (mfderiv_zpow_sphere_circleTangentBasis_ne_zero hk.ne' z), im_conj_mul_mvfderiv_zpow_sphere]
  exact mul_pos (Int.cast_pos.2 hk)
    ((Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul _).1
      (orientation_circleTangentBasis z))

/-- **The negative power maps reverse the orientation of the circle.** For `k < 0`, the map
`z ↦ z ^ k` reverses the counterclockwise orientation of the unit circle of `ℂ` at every
point. -/
theorem isOrientationReversingAt_zpow_sphere {k : ℤ} (hk : k < 0) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationReversingAt Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z := by
  rw [isOrientationReversingAt_sphere_iff_im_conj_mul
    (mfderiv_zpow_sphere_circleTangentBasis_ne_zero hk.ne z), im_conj_mul_mvfderiv_zpow_sphere]
  exact mul_neg_of_neg_of_pos (Int.cast_lt_zero.2 hk)
    ((Complex.orientation_eq_orientationAt_sphereOrientation_iff_im_conj_mul _).1
      (orientation_circleTangentBasis z))

/-- **The orientation sign of a power map of the circle.** For every orientation of the unit
circle of `ℂ`, the map `z ↦ z ^ k` has orientation sign `Int.sign k` at every point. -/
@[simp]
theorem Manifold.Orientation.orientationSign_zpow_sphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (k : ℤ)
    (z : sphere (0 : ℂ) 1) :
    orientationSign o o (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z = k.sign := by
  rcases eq_or_ne k 0 with rfl | hk
  · -- The power map with exponent `0` is constant, so its derivative is not invertible.
    simp only [zpow_zero, Int.sign_zero]
    refine orientationSign_of_not_isInvertible ?_
    rw [mfderiv_const, ContinuousLinearMap.isInvertible_zero_iff, not_and]
    intro h
    exact absurd (Complex.orientation.sphereOrientation.finrank_tangentSpace_eq z)
      (by rw [finrank_zero_of_subsingleton]; simp)
  have := connectedSpace_sphere (E := ℂ) 1
  -- Compare `o` with the counterclockwise orientation.
  have key : orientationSign Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z = k.sign := by
    rcases hk.lt_or_gt with hk | hk
    · rw [orientationSign_of_isOrientationReversingAt (isOrientationReversingAt_zpow_sphere hk z),
        Int.sign_eq_neg_one_of_neg hk]
    · rw [orientationSign_of_isOrientationPreservingAt
        (isOrientationPreservingAt_zpow_sphere hk z), Int.sign_eq_one_of_pos hk]
  rcases o.eq_or_eq_neg Complex.orientation.sphereOrientation with rfl | rfl
  · exact key
  · rw [orientationSign_neg_left, orientationSign_neg_right, neg_neg, key]

/-- For `k ≠ 0`, every value of the power map `z ↦ z ^ k` of the circle is regular. -/
theorem isRegularValue_zpow_sphere {k : ℤ} (hk : k ≠ 0) (y : sphere (0 : ℂ) 1) :
    IsRegularValue (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) y := by
  set o := Complex.orientation.sphereOrientation
  exact isRegularValue_iff.2 fun x _ ↦ (isRegularPoint_iff_isInvertible_mfderiv rfl).2 <|
    not_not.1 <| (Manifold.Orientation.orientationSign_eq_zero_iff (o := o) (o' := o)).not.1 <|
      (Manifold.Orientation.orientationSign_zpow_sphere o k x).trans_ne (by simpa using hk)

/-- The fibre of `z ↦ z ^ k` over `1` consists of `|k|` points of the circle. -/
private theorem exists_finset_zpow_sphere_eq_one {k : ℤ} (hk : k ≠ 0) :
    ∃ s : Finset (sphere (0 : ℂ) 1), (∀ z, z ∈ s ↔ z ^ k = 1) ∧ s.card = k.natAbs := by
  have hk' : 0 < k.natAbs := Int.natAbs_pos.2 hk
  classical
  refine ⟨(Polynomial.nthRootsFinset k.natAbs (1 : ℂ)).subtype (· ∈ sphere (0 : ℂ) 1),
    fun z ↦ ?_, ?_⟩
  · rw [Finset.mem_subtype, Polynomial.mem_nthRootsFinset hk', ← pow_natAbs_eq_one,
      Subtype.ext_iff, Metric.unitSphere.coe_pow, Metric.unitSphere.coe_one]
  · rw [Finset.card_subtype, Finset.filter_true_of_mem fun x hx ↦ ?_,
      (Complex.isPrimitiveRoot_exp _ hk'.ne').card_nthRootsFinset]
    rw [Polynomial.mem_nthRootsFinset hk'] at hx
    exact mem_sphere_zero_iff_norm.2 (Complex.norm_eq_one_of_pow_eq_one hx hk'.ne')

/-- **The degree of a power map of the circle at a value.** For every orientation of the unit
circle of `ℂ`, the map `z ↦ z ^ k` has degree `k` at every value `y`: for `k ≠ 0` every value
has `|k|` preimages, each of orientation sign `Int.sign k`, and for `k = 0` the map is
constant. -/
@[simp]
theorem Manifold.Orientation.degreeAtRegularValue_zpow_sphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (k : ℤ)
    (y : sphere (0 : ℂ) 1) :
    degreeAtRegularValue o o (fun z : sphere (0 : ℂ) 1 ↦ z ^ k) y = k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [zpow_zero]
    exact degreeAtRegularValue_const (by simp) 1 y
  have := connectedSpace_sphere (E := ℂ) 1
  -- The signed count does not depend on the regular value, so compute it over `1`.
  rw [degreeAtRegularValue_eq_of_isRegularValue o o (contMDiff_zpow_sphere k)
    (contMDiff_zpow_sphere k (m := ∞)).continuous.isProperMap (isRegularValue_zpow_sphere hk y)
    (isRegularValue_zpow_sphere hk 1)]
  obtain ⟨s, hs, hcard⟩ := exists_finset_zpow_sphere_eq_one hk
  rw [degreeAtRegularValue_eq_sum hs]
  simp only [orientationSign_zpow_sphere, Finset.sum_const, hcard, nsmul_eq_mul]
  rw [mul_comm]
  exact Int.sign_mul_natAbs k

/-- **The degree of a power map of the circle.** For every orientation of the unit circle of `ℂ`,
the map `z ↦ z ^ k` has mapping degree `k`. -/
@[simp]
theorem Manifold.Orientation.degree_zpow_sphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (k : ℤ) :
    degree o o (fun z : sphere (0 : ℂ) 1 ↦ z ^ k) = k := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [zpow_zero]
    exact degree_const (by simp) 1
  rw [degree_eq_degreeAtRegularValue_choose ⟨1, isRegularValue_zpow_sphere hk 1⟩,
    degreeAtRegularValue_zpow_sphere]

/-- For every orientation of the unit circle of `ℂ`, the map `z ↦ z ^ n` has mapping degree `n`,
for `n : ℕ`. -/
@[simp]
theorem Manifold.Orientation.degree_pow_sphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) (n : ℕ) :
    degree o o (fun z : sphere (0 : ℂ) 1 ↦ z ^ n) = n := by
  simpa only [zpow_natCast] using degree_zpow_sphere o n

end TauCeti
