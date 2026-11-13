/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Homological
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Sphere.Connected

/-!
# The angle-doubling map of a sphere and its degree

Let `E` be a real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`, and fix
`p ∈ Sⁿ`. The **angle-doubling map** at `p` (`TauCeti.sphereDoubleAngle`) is

`g : Sⁿ → Sⁿ`, `g x = 2⟪p, x⟫ • x - p`.

Writing `x = cos t • p + sin t • v` with `v` a unit vector orthogonal to `p`, it sends `x` to
`cos 2t • p + sin 2t • v`: it doubles the angle from `p` along every great circle through `p`.
It is the composite of the reflection in the hyperplane `p^⊥`, which sends `p` to `-p`, with the
reflection in `x^⊥`, evaluated at `p`, so it is the evaluation at `p` of a family of rotations of
the sphere parametrized by the sphere itself.

The map is invariant under the antipodal map, `g (-x) = g x`, and the only preimages of `p` are
`±p`. At `p` its derivative is multiplication by `2`
(`TauCeti.mfderiv_sphereDoubleAngle_self_apply`), so it preserves every orientation there, and `p`
is a regular value. Since `g ∘ (-·) = g`, for `n ≥ 1` the orientation sign of `g` at `-p` is that
of the antipodal map, `(-1)ⁿ⁺¹`. Hence the degree of `g` at `p` is `1 + (-1)ⁿ⁺¹`
(`TauCeti.Manifold.Orientation.degreeAtRegularValue_sphereDoubleAngle_self`): `2` on the
odd-dimensional spheres and `0` on the even-dimensional ones. Through the comparison of the smooth
and the homological degree, `g_*[Sⁿ] = (1 + (-1)ⁿ⁺¹) • [Sⁿ]` for every orientation of the sphere
(`TauCeti.HomologicalOrientation.mapFundamentalClass_sphereDoubleAngle`).

This is the degree computation behind the direct proof that odd-dimensional spheres are
`2`-covered by diffeomorphisms (Barraud–Damian–Humilière–Oancea, Proposition 6.34). There, the
same rotations are parametrized by the rotation family `Sⁿ⁻¹ × S¹ → Sⁿ`
(`TauCeti.sphereRotationFamily`), whose degree is also `1 + (-1)ⁿ⁺¹`.

## Main declarations

* `TauCeti.sphereDoubleAngle`: the angle-doubling map `x ↦ 2⟪p, x⟫ • x - p`.
* `TauCeti.contMDiff_sphereDoubleAngle`: it is smooth.
* `TauCeti.sphereDoubleAngle_neg_right`: it is invariant under the antipodal map.
* `TauCeti.sphereDoubleAngle_eq_left_iff`: the preimages of `p` are `±p`.
* `TauCeti.mfderiv_sphereDoubleAngle_self_apply`: its derivative at `p` is multiplication by `2`.
* `TauCeti.isRegularValue_sphereDoubleAngle_self`: `p` is a regular value.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_sphereDoubleAngle_self`: its degree is
  `1 + (-1)ⁿ⁺¹`.
* `TauCeti.HomologicalOrientation.mapFundamentalClass_sphereDoubleAngle`: it sends the fundamental
  class to `1 + (-1)ⁿ⁺¹` times itself.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3 (Proposition 6.34).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Metric Module Set TauCeti.Manifold.Orientation
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

section Smooth

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### The angle-doubling map -/

/-- The **angle-doubling map** of the unit sphere at a point `p`: `x ↦ 2⟪p, x⟫ • x - p`. On every
great circle through `p` it doubles the angle from `p`, and it is the reflection in `x^⊥` of the
reflection `-p` of `p` in `p^⊥`. -/
def sphereDoubleAngle (p x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨(2 * ⟪(p : E), x⟫) • (x : E) - p, by
    -- `‖2⟪p, x⟫ • x - p‖ ^ 2 = 4⟪p, x⟫ ^ 2 - 4⟪p, x⟫ ^ 2 + 1`.
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm (p : E),
      norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere p, Real.norm_eq_abs, mul_one, sq_abs]
    ring⟩

@[simp]
theorem coe_sphereDoubleAngle (p x : sphere (0 : E) 1) :
    (sphereDoubleAngle p x : E) = (2 * ⟪(p : E), x⟫) • (x : E) - p :=
  (rfl)

/-- The angle-doubling map is smooth. -/
theorem contMDiff_sphereDoubleAngle (p : sphere (0 : E) 1) {m : ℕ∞ω} :
    ContMDiff (𝓡 n) (𝓡 n) m (sphereDoubleAngle p) := by
  have h : ContDiff ℝ m fun y : E ↦ (2 * ⟪(p : E), y⟫) • y - p :=
    ((contDiff_const.mul (contDiff_const.inner ℝ contDiff_id)).smul contDiff_id).sub contDiff_const
  exact (h.contMDiff.comp (contMDiff_coe_sphere (n := n))).codRestrict_sphere
    fun x ↦ (sphereDoubleAngle p x).2

theorem continuous_sphereDoubleAngle (p : sphere (0 : E) 1) : Continuous (sphereDoubleAngle p) :=
  continuous_induced_rng.2 (by simp only [Function.comp_def, coe_sphereDoubleAngle]; fun_prop)

/-- The angle-doubling map is invariant under the antipodal map. -/
@[simp]
theorem sphereDoubleAngle_neg_right (p x : sphere (0 : E) 1) :
    sphereDoubleAngle p (-x) = sphereDoubleAngle p x := by
  ext
  simp [inner_neg_right, neg_smul, smul_neg]

/-- The angle-doubling map at `-p` is the antipode of the angle-doubling map at `p`. -/
@[simp]
theorem sphereDoubleAngle_neg_left (p x : sphere (0 : E) 1) :
    sphereDoubleAngle (-p) x = -sphereDoubleAngle p x := by
  ext
  simp only [coe_sphereDoubleAngle, coe_neg_sphere, inner_neg_left]
  module

@[simp]
theorem sphereDoubleAngle_self (p : sphere (0 : E) 1) : sphereDoubleAngle p p = p := by
  ext
  simp only [coe_sphereDoubleAngle, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
  rw [show (2 * (1 : ℝ) ^ 2) • (p : E) = (p : E) + p by rw [one_pow, mul_one, two_smul]]
  abel

/-- **The fibre over `p`.** The angle-doubling map at `p` sends exactly `p` and `-p` to `p`. -/
theorem sphereDoubleAngle_eq_left_iff (p x : sphere (0 : E) 1) :
    sphereDoubleAngle p x = p ↔ x = p ∨ x = -p := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- From `2⟪p, x⟫ • x = 2 • p`, pairing with `p` gives `⟪p, x⟫ ^ 2 = 1`.
    have h' : ⟪(p : E), x⟫ • (x : E) = p := by
      have h₁ := congrArg Subtype.val h
      rw [coe_sphereDoubleAngle, sub_eq_iff_eq_add, ← two_smul ℝ (p : E), mul_smul] at h₁
      exact smul_right_injective E two_ne_zero h₁
    have hsq : ⟪(p : E), x⟫ * ⟪(p : E), x⟫ = 1 := by
      have h₂ := congrArg (fun y : E ↦ ⟪(p : E), y⟫) h'
      simpa [real_inner_smul_right, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
        using h₂
    rcases mul_self_eq_one_iff.1 hsq with hc | hc
    · left
      ext
      rw [← h', hc, one_smul]
    · right
      ext
      rw [coe_neg_sphere, ← h', hc, neg_one_smul, neg_neg]
  · rintro (rfl | rfl)
    · exact sphereDoubleAngle_self x
    · rw [sphereDoubleAngle_neg_right, sphereDoubleAngle_self]

/-! ### The derivative and the orientation signs -/

/-- **The derivative at `p`** of the angle-doubling map at `p` is multiplication by `2`. -/
theorem mfderiv_sphereDoubleAngle_self_apply (p : sphere (0 : E) 1)
    (w : TangentSpace (𝓡 n) p) :
    mfderiv (𝓡 n) (𝓡 n) (sphereDoubleAngle p) p w = (2 : ℝ) • w := by
  apply injective_mvfderiv_subtypeVal_sphere (n := n) p
  -- Read in `E`, the derivative at `p` is `u ↦ 2⟪p, u⟫ • p + 2⟪p, p⟫ • u`, and the tangent
  -- vectors `u` at `p` are orthogonal to `p`.
  have hu : ⟪(p : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w⟫ = 0 := by
    have hmem : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w ∈ (ℝ ∙ (p : E))ᗮ := by
      rw [← range_mvfderiv_subtypeVal (n := n) p]
      exact LinearMap.mem_range_self _ w
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem
  have hcoe := (contMDiff_coe_sphere (E := E) (n := n) (m := 1) p).mdifferentiableAt
    one_ne_zero
  have hG : HasFDerivAt (fun y : E ↦ (2 * ⟪(p : E), y⟫) • y - p)
      ((2 * ⟪(p : E), (p : E)⟫) • ContinuousLinearMap.id ℝ E +
        ((2 : ℝ) • innerSL ℝ (p : E)).smulRight (p : E)) (p : E) := by
    have hc : HasFDerivAt (fun y : E ↦ 2 * ⟪(p : E), y⟫) ((2 : ℝ) • innerSL ℝ (p : E))
        (p : E) := by
      simpa using (innerSL ℝ (p : E)).hasFDerivAt.const_mul (2 : ℝ)
    exact (hc.smul (hasFDerivAt_id (p : E))).sub_const (p : E)
  have hcomp : ((↑) : sphere (0 : E) 1 → E) ∘ sphereDoubleAngle p =
      (fun y : E ↦ (2 * ⟪(p : E), y⟫) • y - p) ∘ ((↑) : sphere (0 : E) 1 → E) :=
    funext (coe_sphereDoubleAngle p)
  rw [← mvfderiv_comp_apply_of_eq p hcoe
      ((contMDiff_sphereDoubleAngle (m := 1) p p).mdifferentiableAt one_ne_zero)
      (sphereDoubleAngle_self p), hcomp,
    mvfderiv_comp_apply_of_differentiableAt hG.differentiableAt hcoe, hG.fderiv, map_smul]
  generalize mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w = u at hu ⊢
  simp [hu, norm_eq_of_mem_sphere p]

namespace Manifold.Orientation

/-- The angle-doubling map at `p` preserves every orientation of the sphere at `p`. -/
@[simp]
theorem orientationSign_sphereDoubleAngle_self
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    orientationSign o o (sphereDoubleAngle p) p = 1 := by
  let e := (LinearEquiv.smulOfNeZero ℝ (TangentSpace (𝓡 n) p) 2
    two_ne_zero).toContinuousLinearEquiv
  -- `e` is coerced into the maps to the tangent space at `sphereDoubleAngle p p`, which is the
  -- tangent space at `p` only up to unfolding `TangentSpace`; the `simp` lemmas for `e` do not see
  -- through this cast, but `e w` is `2 • w` by definition.
  refine orientationSign_of_isOrientationPreservingAt ((isOrientationPreservingAt_iff_of_coe_eq
    o o _ p e (ContinuousLinearMap.ext fun w ↦ (mfderiv_sphereDoubleAngle_self_apply p w).symm)).2
    ?_)
  have ho : o.orientationAt (sphereDoubleAngle p p) = o.orientationAt p := by
    rw [sphereDoubleAngle_self]
  rw [ho]
  refine (_root_.Orientation.map_eq_iff_det_pos _ _ (by simp)).2 ?_
  -- The determinant of multiplication by `2` is `2 ^ n`.
  have he : (e.toLinearEquiv : TangentSpace (𝓡 n) p →ₗ[ℝ] TangentSpace (𝓡 n) p) =
      (2 : ℝ) • LinearMap.id :=
    LinearMap.ext fun _ ↦ by simp [e]
  rw [he, LinearMap.det_smul, LinearMap.det_id, mul_one]
  positivity

/-- Since the angle-doubling map at `p` is invariant under the antipodal map and preserves
orientations at `p`, its orientation sign at `-p` times that of the antipodal map at `p` is `1`. -/
theorem orientationSign_sphereDoubleAngle_neg_self_mul
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    orientationSign o o (sphereDoubleAngle p) (-p) * orientationSign o o (fun y ↦ -y) p = 1 := by
  have hcomp : sphereDoubleAngle p ∘ (fun y : sphere (0 : E) 1 ↦ -y) = sphereDoubleAngle p :=
    funext fun y ↦ sphereDoubleAngle_neg_right p y
  have h := orientationSign_comp (o := o) (o' := o) (o'' := o) (x := p)
    ((contMDiff_sphereDoubleAngle (m := 1) p _).mdifferentiableAt one_ne_zero)
    ((contMDiff_neg_sphere (n := n) (m := 1) p).mdifferentiableAt one_ne_zero)
  rw [hcomp, orientationSign_sphereDoubleAngle_self o] at h
  exact h.symm

/-- For `n ≥ 1`, at `-p` the angle-doubling map at `p` has the orientation sign `(-1)ⁿ⁺¹` of the
antipodal map, since it is invariant under the antipodal map and preserves orientations at `p`. -/
@[simp]
theorem orientationSign_sphereDoubleAngle_neg_self [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    orientationSign o o (sphereDoubleAngle p) (-p) = (-1) ^ (n + 1) := by
  have h := orientationSign_sphereDoubleAngle_neg_self_mul o p
  rw [orientationSign_neg_sphere] at h
  -- `s * (-1) ^ (n + 1) = 1`, and `(-1) ^ (n + 1)` is its own inverse.
  calc orientationSign o o (sphereDoubleAngle p) (-p)
      = orientationSign o o (sphereDoubleAngle p) (-p) * (-1) ^ (n + 1) *
          (-1) ^ (n + 1) := by rw [mul_assoc, ← mul_pow]; norm_num
    _ = (-1) ^ (n + 1) := by rw [h, one_mul]

end Manifold.Orientation

/-! ### Regular value and degree -/

/-- The point `p` is a regular value of the angle-doubling map at `p`. -/
theorem isRegularValue_sphereDoubleAngle_self (p : sphere (0 : E) 1) :
    IsRegularValue (𝓡 n) (𝓡 n) (sphereDoubleAngle p) p := by
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let o₀ := ((finBasisOfFinrankEq ℝ E
    (Fact.out : finrank ℝ E = n + 1)).orientation).sphereOrientation
  rw [isRegularValue_iff]
  intro x hx
  rw [isRegularPoint_iff_isInvertible_mfderiv (by simp)]
  have hs : orientationSign o₀ o₀ (sphereDoubleAngle p) x ≠ 0 := by
    rcases (sphereDoubleAngle_eq_left_iff p x).1 hx with rfl | rfl
    · rw [orientationSign_sphereDoubleAngle_self o₀]
      exact one_ne_zero
    · exact left_ne_zero_of_mul_eq_one (orientationSign_sphereDoubleAngle_neg_self_mul o₀ p)
  by_contra h
  exact hs (orientationSign_of_not_isInvertible h)

/-- **The degree of the angle-doubling map.** For `n ≥ 1` and every orientation of `Sⁿ`, the
angle-doubling map at `p` has degree `1 + (-1)ⁿ⁺¹` at the regular value `p`: its preimages `p` and
`-p` contribute `1` and `(-1)ⁿ⁺¹`. -/
@[simp]
theorem Manifold.Orientation.degreeAtRegularValue_sphereDoubleAngle_self [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    degreeAtRegularValue o o (sphereDoubleAngle p) p = 1 + (-1) ^ (n + 1) := by
  classical
  have hne : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  rw [degreeAtRegularValue_eq_sum (s := {p, -p}) fun x ↦ by
      rw [Finset.mem_insert, Finset.mem_singleton, sphereDoubleAngle_eq_left_iff],
    Finset.sum_pair hne, orientationSign_sphereDoubleAngle_self,
    orientationSign_sphereDoubleAngle_neg_self]

/-- For odd `n`, the angle-doubling map of the odd-dimensional sphere `Sⁿ` has degree `2`. -/
theorem Manifold.Orientation.degreeAtRegularValue_sphereDoubleAngle_self_of_odd
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1)
    (hn : Odd n) :
    degreeAtRegularValue o o (sphereDoubleAngle p) p = 2 := by
  have : NeZero n := ⟨hn.pos.ne'⟩
  rw [degreeAtRegularValue_sphereDoubleAngle_self, hn.add_one.neg_one_pow]
  norm_num

end Smooth

/-! ### The image of the fundamental class -/

namespace HomologicalOrientation

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] [NeZero n]

/-- **The angle-doubling map on the fundamental class.** For `n ≥ 1` and every homological
orientation of the sphere `Sⁿ` of a real inner product space of dimension `n + 1`, the
angle-doubling map at `p` sends the fundamental class to `(1 + (-1)ⁿ⁺¹) • [Sⁿ]`. -/
@[simp]
theorem mapFundamentalClass_sphereDoubleAngle
    (o : HomologicalOrientation (sphere (0 : E) 1) (EuclideanSpace ℝ (Fin n)) n)
    (p : sphere (0 : E) 1) :
    o.mapFundamentalClass finrank_euclideanSpace_fin
        ⟨sphereDoubleAngle p, continuous_sphereDoubleAngle p⟩ =
      (1 + (-1) ^ (n + 1)) • o.fundamentalClass finrank_euclideanSpace_fin := by
  have := connectedSpace_sphere (E := E) n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (NeZero.ne n)
  let oₛ := ((finBasisOfFinrankEq ℝ E (Fact.out : finrank ℝ E = k + 1 + 1)).orientation
    ).sphereOrientation
  have key := Manifold.Orientation.mapFundamentalClass_eq_degreeAtRegularValue_smul
    finrank_euclideanSpace_fin oₛ oₛ (f := ⟨sphereDoubleAngle p, continuous_sphereDoubleAngle p⟩)
    (isRegularValue_sphereDoubleAngle_self p)
  rw [ContinuousMap.coe_mk, Manifold.Orientation.degreeAtRegularValue_sphereDoubleAngle_self] at key
  rcases (oₛ.toHomologicalOrientation finrank_euclideanSpace_fin).eq_or_eq_neg
    finrank_euclideanSpace_fin o with rfl | rfl
  · exact key
  · rw [mapFundamentalClass_neg, fundamentalClass_neg, key]
    exact (zsmul_neg _ _).symm

end HomologicalOrientation

end TauCeti
