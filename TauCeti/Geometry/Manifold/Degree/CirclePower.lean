/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.RingTheory.RootsOfUnity.Complex
import TauCeti.Analysis.Complex.Circle
import TauCeti.Geometry.Sphere.Connected

/-!
# The degree of the power maps of the circle

The unit circle `S¹ = sphere (0 : ℂ) 1` is a group, and for every integer `k` the power map
`z ↦ z ^ k` is a smooth self-map of it (`TauCeti.contMDiff_zpow_sphere`). Read in `ℂ`, its
derivative at `z` is multiplication by `k z ^ (k - 1)` (`TauCeti.mvfderiv_coe_zpow_sphere_apply`).
A tangent vector `w` at `z` is counterclockwise exactly when `Im (conj z * w) > 0`
(`Complex.orientation_eq_orientationAt_sphereOrientation_iff`), and since `conj z = z⁻¹` on the
circle, `Im (conj (z ^ k) * k z ^ (k - 1) w) = k Im (conj z * w)`. So the power map preserves the
orientation of the circle at every point when `k > 0` and reverses it when `k < 0`, and its
orientation sign is `Int.sign k` everywhere, for each of the two orientations of the circle
(`TauCeti.Manifold.Orientation.orientationSign_zpow_sphere`).

For `k ≠ 0` the fibre over `1` consists of the `|k|` roots of unity of order dividing `|k|`, so
the signed count of that fibre is `|k| · sign k = k`. Every value is regular, and the degree does
not depend on the regular value, so the power map `z ↦ z ^ k` has degree `k` at every value and
mapping degree `k` (`TauCeti.Manifold.Orientation.degree_zpow_sphere`); for `k = 0` the map is
constant and both are `0`. In particular `z ↦ z ^ n` has degree `n` for `n : ℕ`, and complex
conjugation, which is `z ↦ z⁻¹` on the circle, has degree `-1`.

## Main results

* `TauCeti.contMDiff_zpow_sphere`: the power maps of the circle are smooth.
* `TauCeti.mvfderiv_coe_zpow_sphere_apply`: read in `ℂ`, the derivative of `z ↦ z ^ k` at `z` is
  multiplication by `k z ^ (k - 1)`.
* `TauCeti.isOrientationPreservingAt_zpow_sphere`, `TauCeti.isOrientationReversingAt_zpow_sphere`:
  the power map preserves the counterclockwise orientation for `k > 0` and reverses it for
  `k < 0`.
* `TauCeti.Manifold.Orientation.orientationSign_zpow_sphere`: for every orientation of the
  circle, the orientation sign of `z ↦ z ^ k` is `Int.sign k` at every point.
* `TauCeti.isRegularValue_zpow_sphere`: for `k ≠ 0` every value of `z ↦ z ^ k` is regular.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_zpow_sphere`,
  `TauCeti.Manifold.Orientation.degree_zpow_sphere`: the power map `z ↦ z ^ k` has degree `k`.
* `TauCeti.Manifold.Orientation.degree_pow_sphere`: `z ↦ z ^ n` has degree `n` for `n : ℕ`.
* `TauCeti.Manifold.Orientation.degree_conjSphere`: complex conjugation has degree `-1`.

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

/-- The power maps `z ↦ z ^ k` of the unit circle of `ℂ`, for `k : ℤ`, are smooth. -/
theorem contMDiff_zpow_sphere (k : ℤ) {m : ℕ∞ω} :
    ContMDiff (𝓡 1) (𝓡 1) m fun z : sphere (0 : ℂ) 1 ↦ z ^ k := by
  refine ContMDiff.codRestrict_sphere (f := fun z : sphere (0 : ℂ) 1 ↦ (z : ℂ) ^ k)
    (fun z ↦ ?_) fun z ↦ by simp
  exact ((analyticAt_id.zpow (ne_zero_of_mem_unit_sphere z)).contDiffAt.contMDiffAt.comp z
    (contMDiff_coe_sphere z))

/-- **The derivative of a power map of the circle.** Read in `ℂ` through the derivative of the
inclusion, the derivative of `z ↦ z ^ k` at `z` is multiplication by `k z ^ (k - 1)`. -/
theorem mvfderiv_coe_zpow_sphere_apply (k : ℤ) (z : sphere (0 : ℂ) 1)
    (v : TangentSpace (𝓡 1) z) :
    mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) (z ^ k)
        (mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z v) =
      (k * (z : ℂ) ^ (k - 1)) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z v := by
  have hι (w : sphere (0 : ℂ) 1) := (contMDiff_coe_sphere (E := ℂ) (n := 1) (m := 1)
    w).mdifferentiableAt one_ne_zero
  have hpow : HasDerivAt (fun w : ℂ ↦ w ^ k) (k * (z : ℂ) ^ (k - 1)) (z : ℂ) :=
    hasDerivAt_zpow k (z : ℂ) (Or.inl (ne_zero_of_mem_unit_sphere z))
  rw [← mvfderiv_comp_apply (f := fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z (hι _)
    (((contMDiff_zpow_sphere k (m := 1)) z).mdifferentiableAt one_ne_zero)]
  -- Read in `ℂ`, the power map of the circle is the power map of `ℂ` after the inclusion.
  rw [show ((↑) ∘ fun w : sphere (0 : ℂ) 1 ↦ w ^ k) =
      (fun w : ℂ ↦ w ^ k) ∘ ((↑) : sphere (0 : ℂ) 1 → ℂ) from
        funext fun w ↦ by simp,
    mvfderiv_comp_apply z (hpow.differentiableAt.restrictScalars ℝ).mdifferentiableAt (hι z),
    mvfderiv_eq_fderiv, (hpow.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [mvfderiv, mul_comm]

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
      Complex.zpow_mul_conj_zpow_of_mem_sphere z.2, show k - 1 - k = -1 by ring, zpow_neg_one,
      Complex.inv_eq_conj (norm_eq_of_mem_sphere z)]
  rw [mvfderiv_coe_zpow_sphere_apply, ← mul_assoc, key, mul_assoc]
  simp

/-- The derivative of `z ↦ z ^ k`, for `k ≠ 0`, carries the positive tangent basis
`TauCeti.circleTangentBasis z` to a basis at `z ^ k`, which is positive exactly when `k > 0`. -/
private theorem exists_basis_mfderiv_zpow_sphere {k : ℤ} (hk : k ≠ 0) (z : sphere (0 : ℂ) 1) :
    ∃ b' : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) (z ^ k)),
      (∀ i, mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z
        (circleTangentBasis z i) = b' i) ∧
      (b'.orientation = Complex.orientation.sphereOrientation.orientationAt (z ^ k) ↔ 0 < k) := by
  set c := circleTangentBasis z
  have hpos := (Complex.orientation_eq_orientationAt_sphereOrientation_iff c).1
    (orientation_circleTangentBasis z)
  have him := im_conj_mul_mvfderiv_zpow_sphere k z (c 0)
  have hcz :
      0 < (conj (z : ℂ) * mvfderiv (𝓡 1) ((↑) : sphere (0 : ℂ) 1 → ℂ) z (c 0)).im := by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]
    linarith
  have hne : mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z (c 0) ≠ 0 :=
      fun h0 ↦ by
    rw [h0, map_zero, mul_zero, Complex.zero_im] at him
    exact (mul_ne_zero (Int.cast_ne_zero.2 hk) hcz.ne') him.symm
  let b' : Basis (Fin 1) ℝ (TangentSpace (𝓡 1) (z ^ k)) :=
    basisOfLinearIndependentOfCardEqFinrank
      ((linearIndependent_unique_iff
        (v := fun _ : Fin 1 ↦ mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z
          (c 0))).2 hne)
      ((Fintype.card_fin 1).trans
        (Complex.orientation.sphereOrientation.finrank_tangentSpace_eq (z ^ k)).symm)
  refine ⟨b', fun i ↦ by fin_cases i; simp [b'], ?_⟩
  rw [Complex.orientation_eq_orientationAt_sphereOrientation_iff]
  have hb : b' 0 = mfderiv (𝓡 1) (𝓡 1) (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z (c 0) := by
    simp [b']
  rw [hb, show ∀ u w : ℂ, u.re * w.im - u.im * w.re = (conj u * w).im from fun u w ↦ by
    simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring, him,
    mul_pos_iff_of_pos_right hcz, Int.cast_pos]

/-- **The positive power maps preserve the orientation of the circle.** For `k > 0`, the map
`z ↦ z ^ k` preserves the counterclockwise orientation of the unit circle of `ℂ` at every
point. -/
theorem isOrientationPreservingAt_zpow_sphere {k : ℤ} (hk : 0 < k) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationPreservingAt Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z := by
  obtain ⟨b', hb', hpos⟩ := exists_basis_mfderiv_zpow_sphere hk.ne' z
  rw [Manifold.Orientation.isOrientationPreservingAt_iff_of_basis
    (f := fun w : sphere (0 : ℂ) 1 ↦ w ^ k) _ b' hb',
    iff_true_left (orientation_circleTangentBasis z)]
  exact hpos.2 hk

/-- **The negative power maps reverse the orientation of the circle.** For `k < 0`, the map
`z ↦ z ^ k` reverses the counterclockwise orientation of the unit circle of `ℂ` at every
point. -/
theorem isOrientationReversingAt_zpow_sphere {k : ℤ} (hk : k < 0) (z : sphere (0 : ℂ) 1) :
    Manifold.Orientation.IsOrientationReversingAt Complex.orientation.sphereOrientation
      Complex.orientation.sphereOrientation (fun w : sphere (0 : ℂ) 1 ↦ w ^ k) z := by
  obtain ⟨b', hb', hpos⟩ := exists_basis_mfderiv_zpow_sphere hk.ne z
  rw [Manifold.Orientation.isOrientationReversingAt_iff_of_basis
    (f := fun w : sphere (0 : ℂ) 1 ↦ w ^ k) _ b' hb',
    iff_true_left (orientation_circleTangentBasis z),
    ← Orientation.ne_iff_eq_neg _ _
      (Complex.orientation.sphereOrientation.finrank_tangentSpace_eq (z ^ k)).symm, Ne, hpos,
    not_lt]
  exact hk.le

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

/-- For every orientation of the unit circle of `ℂ`, complex conjugation has mapping degree
`-1`. -/
@[simp]
theorem Manifold.Orientation.degree_conjSphere
    (o : Manifold.Orientation (𝓡 1) (sphere (0 : ℂ) 1) (Fin 1)) :
    degree o o conjSphere = -1 := by
  -- On the circle, conjugation is inversion.
  have h : conjSphere = fun z : sphere (0 : ℂ) 1 ↦ z ^ (-1 : ℤ) :=
    funext fun z ↦ Subtype.ext <| by
      rw [coe_conjSphere, Metric.unitSphere.coe_zpow, zpow_neg_one,
        Complex.inv_eq_conj (norm_eq_of_mem_sphere z)]
  rw [h, degree_zpow_sphere]

end TauCeti
