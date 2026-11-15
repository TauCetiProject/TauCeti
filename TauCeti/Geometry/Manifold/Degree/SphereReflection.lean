/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Basic
public import TauCeti.Geometry.Manifold.Orientation.Sphere
import TauCeti.Geometry.Sphere.Connected
import TauCeti.Geometry.Manifold.MFDeriv.IsInvertible

/-!
# The reflection map of a sphere and its degree

Let `E` be a real inner product space of dimension `n + 1`, with unit sphere `Sⁿ`, and fix
`p ∈ Sⁿ`. The **reflection map** at `p` (`TauCeti.sphereReflectionMap`) is

`g : Sⁿ → Sⁿ`, `g x = 2 ⟪p, x⟫ • x - p`,

the image of `-p` under the reflection of `E` in the hyperplane orthogonal to `x`. Writing
`x = cos θ • p + sin θ • v` with `v` a unit vector orthogonal to `p`, it is
`g x = cos 2θ • p + sin 2θ • v`: the point `p` rotated towards `v` by twice the angle from `p` to
`x`. The map is even, `g (-x) = g x` (`TauCeti.sphereReflectionMap_neg`), and the fibre over `p` is
`{p, -p}` (`TauCeti.sphereReflectionMap_eq_self_iff`).

Read in `E`, its derivative at `x` sends a tangent vector `w` to `2 ⟪p, w⟫ • x + 2 ⟪p, x⟫ • w`
(`TauCeti.mvfderiv_coe_sphereReflectionMap_apply`). It is invertible wherever `⟪p, x⟫ ≠ 0`
(`TauCeti.isInvertible_mfderiv_sphereReflectionMap`), so `p` is a regular value
(`TauCeti.isRegularValue_sphereReflectionMap_self`). At `p` itself the derivative is
multiplication by `2`, which preserves every orientation, so the orientation sign of `g` at `p` is
`1` (`TauCeti.Manifold.Orientation.orientationSign_sphereReflectionMap_self`). Since `g` is even,
its orientation sign at `-x` is that at `x` times the orientation sign `(-1)ⁿ⁺¹` of the antipodal
map (`TauCeti.Manifold.Orientation.orientationSign_sphereReflectionMap_neg`). Hence the degree of
`g` at `p` is `1 + (-1)ⁿ⁺¹` for every orientation of `Sⁿ`
(`TauCeti.Manifold.Orientation.degreeAtRegularValue_sphereReflectionMap_self`): it is `2` for odd
`n` and `0` for even `n`.

The map `g` is the evaluation at `p` of the family of rotations `x ↦ r_x ∘ r_p`, where `r_y` is the
reflection in the hyperplane orthogonal to `y`. Its degree two in odd dimensions shows that
odd-dimensional spheres are `2`-covered by diffeomorphisms, in the sense of
Barraud–Damian–Humilière–Oancea (`TauCeti.Geometry.Diffeomorphism.Sphere.Reflection`).

## Main declarations

* `TauCeti.sphereReflectionMap`: the map `x ↦ 2 ⟪p, x⟫ • x - p`.
* `TauCeti.contMDiff_sphereReflectionMap`: it is smooth.
* `TauCeti.mvfderiv_coe_sphereReflectionMap_apply`: its derivative.
* `TauCeti.isInvertible_mfderiv_sphereReflectionMap`: its derivative is invertible where
  `⟪p, x⟫ ≠ 0`.
* `TauCeti.isRegularValue_sphereReflectionMap_self`: `p` is a regular value.
* `TauCeti.Manifold.Orientation.orientationSign_sphereReflectionMap_neg`: the orientation signs at
  `x` and `-x`.
* `TauCeti.Manifold.Orientation.degreeAtRegularValue_sphereReflectionMap_self`: the degree is
  `1 + (-1)ⁿ⁺¹`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.3 (Proposition 6.34).
* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Metric Module Set
open scoped Manifold ContDiff RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-! ### The reflection map -/

/-- The **reflection map** of the unit sphere at `p`: a point `x` is sent to `2 ⟪p, x⟫ • x - p`,
the image of `-p` under the reflection in the hyperplane orthogonal to `x`. -/
def sphereReflectionMap (p : sphere (0 : E) 1) : sphere (0 : E) 1 → sphere (0 : E) 1 := fun x ↦
  ⟨(2 * ⟪(p : E), x⟫) • (x : E) - p, by
    -- `‖2c x - p‖² = 4c² - 4c² + 1` for unit vectors `x`, `p` and `c = ⟪p, x⟫`.
    rw [mem_sphere_zero_iff_norm, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
      norm_sub_sq_real, norm_smul, real_inner_smul_left, real_inner_comm,
      norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere p, Real.norm_eq_abs, mul_pow, sq_abs]
    ring⟩

@[simp]
theorem coe_sphereReflectionMap (p x : sphere (0 : E) 1) :
    (sphereReflectionMap p x : E) = (2 * ⟪(p : E), x⟫) • (x : E) - p :=
  (rfl)

/-- The reflection map is continuous. -/
theorem continuous_sphereReflectionMap (p : sphere (0 : E) 1) :
    Continuous (sphereReflectionMap p) :=
  Continuous.subtype_mk (by fun_prop) _

/-- The reflection map is even. -/
@[simp]
theorem sphereReflectionMap_neg (p x : sphere (0 : E) 1) :
    sphereReflectionMap p (-x) = sphereReflectionMap p x := by
  ext : 1
  simp [inner_neg_right]

/-- The reflection map fixes `p`. -/
@[simp]
theorem sphereReflectionMap_self (p : sphere (0 : E) 1) : sphereReflectionMap p p = p := by
  ext : 1
  rw [coe_sphereReflectionMap, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
  module

/-- The fibre of the reflection map over `p` is `{p, -p}`. -/
theorem sphereReflectionMap_eq_self_iff (p x : sphere (0 : E) 1) :
    sphereReflectionMap p x = p ↔ x = p ∨ x = -p := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · -- `2 ⟪p, x⟫ • x = 2 • p`, so `⟪p, x⟫ • x = p` and, pairing with `x`, `⟪p, x⟫ ^ 2 = 1`.
    have hE : ⟪(p : E), x⟫ • (x : E) = p := by
      have h' := congrArg Subtype.val h
      rw [coe_sphereReflectionMap, sub_eq_iff_eq_add, ← two_smul ℝ (p : E), mul_smul] at h'
      exact smul_right_injective E two_ne_zero h'
    have hsq : ⟪(p : E), x⟫ ^ 2 = 1 ^ 2 := by
      have h' := congrArg (fun w ↦ ⟪w, (p : E)⟫) hE
      simp only [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p] at h'
      rw [real_inner_comm (p : E) (x : E)] at h'
      linear_combination h'
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with hc | hc
    · left
      ext : 1
      rw [← hE, hc, one_smul]
    · right
      ext : 1
      rw [coe_neg_sphere, ← hE, hc, neg_one_smul, neg_neg]
  · rintro (rfl | rfl)
    · exact sphereReflectionMap_self x
    · rw [sphereReflectionMap_neg, sphereReflectionMap_self]

/-- The reflection map is smooth. -/
theorem contMDiff_sphereReflectionMap (p : sphere (0 : E) 1) :
    ContMDiff (𝓡 n) (𝓡 n) ∞ (sphereReflectionMap p) := by
  have hx : ContMDiff (𝓡 n) 𝓘(ℝ, E) ∞ ((↑) : sphere (0 : E) 1 → E) := contMDiff_coe_sphere
  have hc : ContMDiff (𝓡 n) 𝓘(ℝ) ∞ fun x : sphere (0 : E) 1 ↦ ((2 : ℝ) • innerSL ℝ (p : E)) x :=
    ((2 : ℝ) • innerSL ℝ (p : E)).contDiff.contMDiff.comp hx
  exact ContMDiff.codRestrict_sphere ((hc.smul hx).sub contMDiff_const)
    fun x ↦ (sphereReflectionMap p x).2

/-! ### The derivative -/

/-- **The derivative of the reflection map.** Read in `E`, a tangent vector `w` at `x`, itself
read in `E` as `w'`, is sent to `2 ⟪p, w'⟫ • x + 2 ⟪p, x⟫ • w'`. -/
theorem mvfderiv_coe_sphereReflectionMap_apply (p x : sphere (0 : E) 1)
    (w : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) (fun y ↦ (sphereReflectionMap p y : E)) x w =
      (2 * ⟪(p : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫) • (x : E) +
        (2 * ⟪(p : E), x⟫) • mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w := by
  have hι : MDifferentiableAt (𝓡 n) 𝓘(ℝ, E) ((↑) : sphere (0 : E) 1 → E) x :=
    (contMDiff_coe_sphere (E := E) (n := n) (m := 1) x).mdifferentiableAt one_ne_zero
  have hc : MDifferentiableAt (𝓡 n) 𝓘(ℝ)
      (⇑((2 : ℝ) • innerSL ℝ (p : E)) ∘ ((↑) : sphere (0 : E) 1 → E)) x :=
    ((2 : ℝ) • innerSL ℝ (p : E)).mdifferentiableAt.comp x hι
  have hc' : mvfderiv (𝓡 n) (⇑((2 : ℝ) • innerSL ℝ (p : E)) ∘ ((↑) : sphere (0 : E) 1 → E)) x w =
      2 * ⟪(p : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w⟫ := by
    rw [((2 : ℝ) • innerSL ℝ (p : E)).mvfderiv_comp_apply hι]
    simp
    rfl
  -- Write the map as the product of a scalar and a vector-valued function, minus a constant.
  rw [show (fun y ↦ (sphereReflectionMap p y : E)) =
      ((⇑((2 : ℝ) • innerSL ℝ (p : E)) ∘ ((↑) : sphere (0 : E) 1 → E)) •
        ((↑) : sphere (0 : E) 1 → E)) + fun _ : sphere (0 : E) 1 ↦ -(p : E) by
      funext y
      simp [sub_eq_add_neg],
    mvfderiv_add (hc.smul hι) mdifferentiableAt_const, mvfderiv_smul hc hι, mvfderiv_const]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, add_zero, hc']
  simp [add_comm]

/-- Read in `E`, the derivative of the reflection map at `x` is the derivative of the map itself
followed by that of the inclusion at `g x`. -/
private theorem mvfderiv_coe_mfderiv_sphereReflectionMap_apply (p x : sphere (0 : E) 1)
    (w : TangentSpace (𝓡 n) x) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (sphereReflectionMap p x)
        (mfderiv (𝓡 n) (𝓡 n) (sphereReflectionMap p) x w) =
      mvfderiv (𝓡 n) (fun y ↦ (sphereReflectionMap p y : E)) x w :=
  (mvfderiv_comp_apply x
    ((contMDiff_coe_sphere (E := E) (n := n) (m := 1) _).mdifferentiableAt one_ne_zero)
    ((contMDiff_sphereReflectionMap p x).mdifferentiableAt (by simp)) w).symm

/-- At a point `x` with `⟪p, x⟫ ≠ 0`, the derivative of the reflection map is invertible. -/
theorem isInvertible_mfderiv_sphereReflectionMap (p : sphere (0 : E) 1) {x : sphere (0 : E) 1}
    (hx : ⟪(p : E), x⟫ ≠ 0) :
    (mfderiv (𝓡 n) (𝓡 n) (sphereReflectionMap p) x).IsInvertible := by
  refine isInvertible_mfderiv_of_injective rfl fun w₁ w₂ hw ↦ ?_
  rw [← sub_eq_zero, ← map_sub] at hw
  rw [← sub_eq_zero]
  set w := w₁ - w₂
  -- Read in `E`, `w` is a vector `a ⊥ x` with `2 ⟪p, a⟫ • x + 2 ⟪p, x⟫ • a = 0`.
  set a := mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) x w
  have ha : ⟪(x : E), a⟫ = 0 := by
    have hmem : a ∈ (ℝ ∙ (x : E))ᗮ := range_mvfderiv_subtypeVal (n := n) x ▸
      LinearMap.mem_range_self _ _
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem
  have h0 : (2 * ⟪(p : E), a⟫) • (x : E) + (2 * ⟪(p : E), x⟫) • a = 0 := by
    rw [← mvfderiv_coe_sphereReflectionMap_apply, ← mvfderiv_coe_mfderiv_sphereReflectionMap_apply,
      hw, map_zero]
  -- Pairing with `x` kills the second term, so `⟪p, a⟫ = 0`, and then `⟪p, x⟫ • a = 0`.
  have hpa : 2 * ⟪(p : E), a⟫ = 0 := by
    have h' := congrArg (fun v ↦ ⟪(x : E), v⟫) h0
    simpa only [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq,
      norm_eq_of_mem_sphere x, ha, mul_zero, add_zero, one_pow, mul_one, inner_zero_right]
      using h'
  rw [hpa, zero_smul, zero_add, smul_eq_zero] at h0
  have ha0 : a = 0 := h0.resolve_left (mul_ne_zero two_ne_zero hx)
  exact injective_mvfderiv_subtypeVal_sphere x (by rw [map_zero]; exact ha0)

/-- The point `p` is a regular value of the reflection map: its preimages `±p` have
`⟪p, ±p⟫ = ±1`. -/
theorem isRegularValue_sphereReflectionMap_self (p : sphere (0 : E) 1) :
    IsRegularValue (𝓡 n) (𝓡 n) (sphereReflectionMap p) p := by
  rw [isRegularValue_iff]
  intro x hx
  rw [isRegularPoint_iff]
  refine (isInvertible_mfderiv_sphereReflectionMap p ?_).surjective
  rcases (sphereReflectionMap_eq_self_iff p x).1 hx with rfl | rfl
  · simp [norm_eq_of_mem_sphere x]
  · simp [inner_neg_right, norm_eq_of_mem_sphere p]

/-! ### Orientation signs and the degree -/

/-- At `p` the derivative of the reflection map, read in `E`, is multiplication by `2`. -/
private theorem mvfderiv_coe_mfderiv_sphereReflectionMap_self_apply (p : sphere (0 : E) 1)
    (w : TangentSpace (𝓡 n) p) :
    mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (sphereReflectionMap p p)
        (mfderiv (𝓡 n) (𝓡 n) (sphereReflectionMap p) p w) =
      (2 : ℝ) • mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w := by
  have ha : ⟪(p : E), mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w⟫ = 0 := by
    have hmem : mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p w ∈ (ℝ ∙ (p : E))ᗮ :=
      range_mvfderiv_subtypeVal (n := n) p ▸ LinearMap.mem_range_self _ _
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 hmem
  rw [mvfderiv_coe_mfderiv_sphereReflectionMap_apply, mvfderiv_coe_sphereReflectionMap_apply, ha,
    real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p]
  simp

end TauCeti

namespace TauCeti.Manifold.Orientation

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- At `p` the reflection map preserves the outward-normal orientation of the sphere: its
derivative there is multiplication by `2`. -/
private theorem isOrientationPreservingAt_sphereReflectionMap_self
    (o : _root_.Orientation ℝ E (Fin (n + 1))) (p : sphere (0 : E) 1) :
    IsOrientationPreservingAt o.sphereOrientation o.sphereOrientation
      (sphereReflectionMap p) p := by
  classical
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  let b := finBasisOfFinrankEq ℝ (TangentSpace (𝓡 n) p) (finrank_euclideanSpace_fin (𝕜 := ℝ))
  -- The derivative carries `b` to the basis `2 • b` of the tangent space at `g p = p`.
  obtain ⟨e, he⟩ := isInvertible_mfderiv_sphereReflectionMap (n := n) p (x := p) (by
    simp [norm_eq_of_mem_sphere p])
  let b' : Basis (Fin n) ℝ (TangentSpace (𝓡 n) (sphereReflectionMap p p)) :=
    b.map e.toLinearEquiv
  have hb' (i : Fin n) : mfderiv (𝓡 n) (𝓡 n) (sphereReflectionMap p) p (b i) = b' i := by
    simp [b', ← he]
  -- The volumes of `p` followed by the two bases, read in `E`, differ by the factor `2 ^ n`.
  have hvol : o.volumeForm (Fin.cons ((sphereReflectionMap p p : sphere (0 : E) 1) : E)
      fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) (sphereReflectionMap p p) (b' i)) =
      (2 : ℝ) ^ n * o.volumeForm (Fin.cons (p : E)
        fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p (b i)) := by
    simp_rw [← hb', mvfderiv_coe_mfderiv_sphereReflectionMap_self_apply, sphereReflectionMap_self]
    have hcons : (Fin.cons (p : E) fun i ↦ (2 : ℝ) •
        mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p (b i) : Fin (n + 1) → E) =
        fun j ↦ (Fin.cons (1 : ℝ) (fun _ : Fin n ↦ (2 : ℝ)) : Fin (n + 1) → ℝ) j • (Fin.cons (p : E)
          fun i ↦ mvfderiv (𝓡 n) ((↑) : sphere (0 : E) 1 → E) p (b i) : Fin (n + 1) → E) j := by
      ext j : 1
      refine Fin.cases ?_ (fun i ↦ ?_) j <;> simp <;> rfl
    rw [hcons, AlternatingMap.map_smul_univ, Fin.prod_univ_succ]
    simp
  rw [isOrientationPreservingAt_iff_of_basis b b' hb',
    o.orientation_eq_orientationAt_sphereOrientation_iff,
    o.orientation_eq_orientationAt_sphereOrientation_iff, hvol]
  exact (mul_pos_iff_of_pos_left (pow_pos two_pos n)).symm

/-- **The orientation sign of the reflection map at `p`** is `1`, for every orientation of the
connected sphere `Sⁿ`, `n ≥ 1`. -/
@[simp]
theorem orientationSign_sphereReflectionMap_self [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    orientationSign o o (sphereReflectionMap p) p = 1 := by
  have hE : finrank ℝ E = n + 1 := Fact.out
  have : FiniteDimensional ℝ E := .of_fact_finrank_eq_succ n
  have := connectedSpace_sphere (E := E) n
  -- Compare `o` with the outward-normal orientation of an orientation of `E`.
  let oE := (finBasisOfFinrankEq ℝ E hE).orientation
  have key : orientationSign oE.sphereOrientation oE.sphereOrientation (sphereReflectionMap p) p =
      1 := orientationSign_of_isOrientationPreservingAt
    (isOrientationPreservingAt_sphereReflectionMap_self oE p)
  rcases o.eq_or_eq_neg oE.sphereOrientation with rfl | rfl
  · exact key
  · rw [orientationSign_neg_left, orientationSign_neg_right, neg_neg, key]

/-- **The orientation signs at antipodal points.** Since the reflection map is even, its
orientation sign at `-x` is its orientation sign at `x` times the orientation sign `(-1)ⁿ⁺¹` of the
antipodal map, for every orientation of `Sⁿ`, `n ≥ 1`. -/
theorem orientationSign_sphereReflectionMap_neg [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p x : sphere (0 : E) 1) :
    orientationSign o o (sphereReflectionMap p) (-x) =
      (-1) ^ (n + 1) * orientationSign o o (sphereReflectionMap p) x := by
  have hg : sphereReflectionMap p = sphereReflectionMap p ∘ fun y ↦ -y :=
    funext fun y ↦ (sphereReflectionMap_neg p y).symm
  conv_lhs => rw [hg]
  rw [orientationSign_comp (((contMDiff_sphereReflectionMap p) _).mdifferentiableAt (by simp))
      ((contMDiff_neg_sphere (m := 1) (-x)).mdifferentiableAt one_ne_zero),
    orientationSign_neg_sphere, neg_neg, mul_comm]

/-- **The degree of the reflection map.** At its regular value `p`, the reflection map of `Sⁿ`,
`n ≥ 1`, has degree `1 + (-1)ⁿ⁺¹` for every orientation: its two preimages `p` and `-p` contribute
`1` and `(-1)ⁿ⁺¹`. -/
theorem degreeAtRegularValue_sphereReflectionMap_self [NeZero n]
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    degreeAtRegularValue o o (sphereReflectionMap p) p = 1 + (-1) ^ (n + 1) := by
  classical
  have hne : p ≠ -p := ne_neg_of_mem_unit_sphere ℝ p
  rw [degreeAtRegularValue_eq_sum (s := {p, -p}) fun x ↦ by
      rw [Finset.mem_insert, Finset.mem_singleton, sphereReflectionMap_eq_self_iff],
    Finset.sum_pair hne, orientationSign_sphereReflectionMap_neg,
    orientationSign_sphereReflectionMap_self, mul_one]

/-- For odd `n`, the reflection map of `Sⁿ` has degree `2` at `p`, for every orientation. -/
theorem degreeAtRegularValue_sphereReflectionMap_self_of_odd [NeZero n] (hn : Odd n)
    (o : Manifold.Orientation (𝓡 n) (sphere (0 : E) 1) (Fin n)) (p : sphere (0 : E) 1) :
    degreeAtRegularValue o o (sphereReflectionMap p) p = 2 := by
  rw [degreeAtRegularValue_sphereReflectionMap_self, hn.add_one.neg_one_pow]
  norm_num

end TauCeti.Manifold.Orientation
