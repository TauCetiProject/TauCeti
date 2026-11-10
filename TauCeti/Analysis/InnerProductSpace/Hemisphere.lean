/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.LinearIsometry
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension
import TauCeti.Data.Set.InjOnUnion
import TauCeti.Order.Interval.Set.ProjIcc
import TauCeti.Topology.ContinuousMap.GlueClosedEmbeddings

/-!
# Closed hemispheres of a unit sphere

For a unit vector `p` of a real inner product space `E`, the closed hemisphere
`{x ∈ S | 0 ≤ ⟪x, p⟫}` of the unit sphere `S` of `E` is homeomorphic to the closed unit ball of
the hyperplane `(ℝ ∙ p)ᗮ`. The homeomorphism removes the component of `x` along `p`; its inverse
lifts a point `y` of the ball to `y + √(1 - ‖y‖²) • p`.

The closed hemispheres around `p` and `-p` cover the sphere and meet in the equator, the unit
sphere of `(ℝ ∙ p)ᗮ`, included in `S` by `TauCeti.equatorInclusion (p : E)`. Closed hemispheres
are the discs out of which the sphere is built in the inductive computations of the homology
of the complement of an embedded sphere.

Conversely, a space covered by two closed discs which meet exactly along their boundary spheres is
a sphere, whatever the homeomorphism by which the boundary spheres are matched: the first disc is
sent onto the closed hemisphere around `p`, and the second onto the closed hemisphere around `-p`
after the radial extension of the matching homeomorphism (`Homeomorph.radialExtension`). This is
how a manifold built from two discs, such as one carrying a Morse function with exactly two
critical points, is recognized as a sphere.

When the equator is nonempty, every point of the unit sphere is `√(1 - t²) • u + t • p` for a
point `u` of the equator and a height `t ∈ [-1, 1]`, and this latitude parametrization is injective
off the poles `p` and `-p` (`TauCeti.latitude`). The equator is empty when `E` has dimension one,
and then the latitude map reaches no point.

## Main definitions

* `TauCeti.hemisphereHomeomorph p`: the closed hemisphere around `p` is homeomorphic to the closed
  unit ball of `(ℝ ∙ p)ᗮ`.
* `TauCeti.equatorInclusion p`: for any vector `p` and radius `r`, the inclusion of the sphere
  of radius `r` in `(ℝ ∙ p)ᗮ` into the sphere of radius `r` in `E`.
* `TauCeti.latitude p u t`: the point `√(1 - t²) • u + t • p` of the unit sphere at height `t`
  over the point `u` of the equator, with `t` clamped to `[-1, 1]`.

## Main results

* `TauCeti.coe_hemisphereHomeomorph_apply` and `TauCeti.coe_hemisphereHomeomorph_symm_apply`:
  the formulas for the homeomorphism and its inverse.
* `TauCeti.frontier_setOf_inner_nonneg`: the equator is the frontier of each closed hemisphere.
* `TauCeti.range_equatorInclusion`: the equator is the intersection of the closed hemispheres
  around `p` and `-p`.
* `TauCeti.isometry_equatorInclusion`: the equator inclusion preserves distances.
* `TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`: two closed discs glued along their
  boundary spheres form a sphere.
* `TauCeti.exists_latitude_eq` and `TauCeti.eq_and_eq_of_latitude_eq`: the latitude map is
  surjective when the equator is nonempty, and injective off the poles.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  proof of Theorem 4.1, for the gluing of two discs along their boundary spheres.
-/

public section

noncomputable section

open Metric Set
open scoped RealInnerProductSpace

namespace TauCeti

variable {E : Type*}

section Hemisphere

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- Removing from a point of the unit sphere its component along a unit vector `p` gives a vector
orthogonal to `p` of norm at most one. -/
private lemma sub_inner_smul_mem_closedBall (x : sphere (0 : E) 1) :
    (x : E) - ⟪(x : E), (p : E)⟫ • (p : E) ∈ (ℝ ∙ (p : E))ᗮ ∧
      ‖(x : E) - ⟪(x : E), (p : E)⟫ • (p : E)‖ ^ 2 = 1 - ⟪(x : E), (p : E)⟫ ^ 2 := by
  have hp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hx : ‖(x : E)‖ = 1 := norm_eq_of_mem_sphere x
  refine ⟨Submodule.mem_orthogonal_singleton_iff_inner_right.2 ?_, ?_⟩
  · rw [inner_sub_right, real_inner_smul_right, hp, real_inner_comm, mul_one, sub_self]
  · rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      norm_eq_of_mem_sphere p, hx]
    ring

/-- A vector `y` orthogonal to `p`, lifted by `t` in the direction of `p`, lands on the unit
sphere when `‖y‖² + t² = 1`. -/
private lemma norm_add_smul_eq_one {y : E} (hy : y ∈ (ℝ ∙ (p : E))ᗮ) {t : ℝ}
    (h : ‖y‖ ^ 2 + t ^ 2 = 1) : ‖y + t • (p : E)‖ = 1 := by
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero]
  exact (norm_add_smul_sq (p : E) (norm_eq_of_mem_sphere p) ⟨y, hy⟩ t).trans h

/-- Lifting a point `y` of the closed unit ball of `(ℝ ∙ p)ᗮ` by `√(1 - ‖y‖²)` in the direction
of `p` lands on the unit sphere, with inner product `√(1 - ‖y‖²)` against `p`. -/
private lemma add_sqrt_smul_mem_sphere (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ‖((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E)‖ = 1 ∧
      ⟪((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E), (p : E)⟫ =
        √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) := by
  have hp : ⟪(p : E), (p : E)⟫ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
  have hyp : ⟪((y : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (y : (ℝ ∙ (p : E))ᗮ).2
  have hy : ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) (mem_closedBall_zero_iff.1 y.2)
  refine ⟨norm_add_smul_eq_one p (y : (ℝ ∙ (p : E))ᗮ).2 ?_,
    by rw [inner_add_left, real_inner_smul_left, hyp, hp, zero_add, mul_one]⟩
  rw [Submodule.norm_coe, Real.sq_sqrt (by linarith)]
  ring

/-- **The closed hemisphere around `p` is a disc.** For a point `p` of the unit sphere of a real
inner product space `E`, the closed hemisphere `{x | 0 ≤ ⟪x, p⟫}` of the unit sphere is
homeomorphic to the closed unit ball of the orthogonal complement `(ℝ ∙ p)ᗮ`. The homeomorphism
sends `x` to `x - ⟪x, p⟫ • p` (`TauCeti.coe_hemisphereHomeomorph_apply`), and its inverse sends `y`
to `y + √(1 - ‖y‖²) • p` (`TauCeti.coe_hemisphereHomeomorph_symm_apply`). -/
def hemisphereHomeomorph :
    {x : sphere (0 : E) 1 // 0 ≤ ⟪(x : E), (p : E)⟫} ≃ₜ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 where
  toFun x := ⟨⟨_, (sub_inner_smul_mem_closedBall p x).1⟩, mem_closedBall_zero_iff.2 <|
    (pow_le_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 <| by
      simp only [← Submodule.norm_coe, (sub_inner_smul_mem_closedBall p x).2]
      linarith [sq_nonneg ⟪((x : sphere (0 : E) 1) : E), (p : E)⟫]⟩
  invFun y := ⟨⟨_, mem_sphere_zero_iff_norm.2 (add_sqrt_smul_mem_sphere p y).1⟩,
    (add_sqrt_smul_mem_sphere p y).2.symm ▸ Real.sqrt_nonneg _⟩
  left_inv x := by
    obtain ⟨⟨x, hx⟩, hxp⟩ := x
    refine Subtype.ext (Subtype.ext ?_)
    have h := (sub_inner_smul_mem_closedBall p ⟨x, hx⟩).2
    simp only [← Submodule.norm_coe, h, sub_sub_cancel, Real.sqrt_sq hxp, sub_add_cancel]
  right_inv y := by
    refine Subtype.ext (Subtype.ext ?_)
    simp only [(add_sqrt_smul_mem_sphere p y).2, add_sub_cancel_right]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- `TauCeti.hemisphereHomeomorph p` removes the component along `p`. -/
@[simp]
theorem coe_hemisphereHomeomorph_apply (x : {x : sphere (0 : E) 1 // 0 ≤ ⟪(x : E), (p : E)⟫}) :
    ((hemisphereHomeomorph p x : (ℝ ∙ (p : E))ᗮ) : E) =
      ((x : sphere (0 : E) 1) : E) - ⟪((x : sphere (0 : E) 1) : E), (p : E)⟫ • (p : E) :=
  (rfl)

/-- The inverse of `TauCeti.hemisphereHomeomorph p` lifts a point `y` of the closed unit ball of
`(ℝ ∙ p)ᗮ` to `y + √(1 - ‖y‖²) • p`. -/
@[simp]
theorem coe_hemisphereHomeomorph_symm_apply (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    (((hemisphereHomeomorph p).symm y : sphere (0 : E) 1) : E) =
      ((y : (ℝ ∙ (p : E))ᗮ) : E) + √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) • (p : E) :=
  (rfl)

end Hemisphere

section Equator

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : E) {r : ℝ}

/-- The inclusion of the equator, the sphere of radius `r` in `(ℝ ∙ p)ᗮ`, into the sphere of
radius `r` in `E`. The vector `p` need not be a unit vector. -/
def equatorInclusion : sphere (0 : (ℝ ∙ p)ᗮ) r → sphere (0 : E) r :=
  fun y ↦ ⟨((y : (ℝ ∙ p)ᗮ) : E), mem_sphere_zero_iff_norm.2
    ((Submodule.norm_coe _).trans (norm_eq_of_mem_sphere y))⟩

/-- `TauCeti.equatorInclusion p` is the inclusion of `(ℝ ∙ p)ᗮ` into `E`. -/
@[simp]
theorem coe_equatorInclusion_apply (y : sphere (0 : (ℝ ∙ p)ᗮ) r) :
    (equatorInclusion p y : E) = ((y : (ℝ ∙ p)ᗮ) : E) :=
  (rfl)

/-- The inclusion of the equator preserves distances. -/
theorem isometry_equatorInclusion : Isometry (equatorInclusion (r := r) p) := by
  intro x y
  exact ((isometry_subtype_coe (α := E)).comp isometry_subtype_coe).edist_eq x y

/-- The inclusion of the equator is continuous. -/
@[fun_prop]
theorem continuous_equatorInclusion : Continuous (equatorInclusion (r := r) p) :=
  (isometry_equatorInclusion p).continuous

/-- The equator is the set of points of the sphere orthogonal to `p`, the intersection of the two
closed hemispheres around `p` and `-p`. -/
theorem range_equatorInclusion :
    range (equatorInclusion p) = {x : sphere (0 : E) r | 0 ≤ ⟪(x : E), p⟫} ∩
      {x : sphere (0 : E) r | 0 ≤ ⟪(x : E), -p⟫} := by
  refine Set.ext fun x ↦ ?_
  simp only [mem_inter_iff, mem_ofPred_eq, inner_neg_right, neg_nonneg,
    ← le_antisymm_iff, eq_comm (a := (0 : ℝ))]
  constructor
  · rintro ⟨y, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (y : (ℝ ∙ p)ᗮ).2
  · intro hx
    exact ⟨⟨⟨x, Submodule.mem_orthogonal_singleton_iff_inner_left.2 hx⟩,
      mem_sphere_zero_iff_norm.2 (norm_eq_of_mem_sphere x)⟩, rfl⟩

end Equator

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] (p : sphere (0 : E) 1)

/-- The normalization of `x - t • p`, for a point `x` of the unit sphere orthogonal to `p`: for
`t > 0` it moves from `x` towards `-p` along a great circle. -/
private def normalizeSubSmul (x : sphere (0 : E) 1) (hx : ⟪(x : E), (p : E)⟫ = 0) (t : ℝ) :
    sphere (0 : E) 1 :=
  ⟨(√(1 + t ^ 2))⁻¹ • ((x : E) - t • (p : E)), mem_sphere_zero_iff_norm.2 <| by
    have hnorm : ‖(x : E) - t • (p : E)‖ = √(1 + t ^ 2) := by
      have h : ⟪(x : E), t • (p : E)⟫ = 0 := by simp [real_inner_smul_right, hx]
      simpa only [norm_smul, norm_eq_of_mem_sphere x, norm_eq_of_mem_sphere p, mul_one,
        Real.norm_eq_abs, ← sq, sq_abs, one_pow] using norm_sub_eq_sqrt_iff_real_inner_eq_zero.2 h
    have hpos : 0 < √(1 + t ^ 2) := Real.sqrt_pos.2 (by positivity)
    rw [norm_smul, hnorm, Real.norm_eq_abs,
      abs_of_pos (inv_pos.2 hpos), inv_mul_cancel₀ hpos.ne']⟩

/-- The frontier of the closed hemisphere around `p` in the unit sphere is the equator. -/
theorem frontier_setOf_inner_nonneg :
    frontier {x : sphere (0 : E) 1 | 0 ≤ ⟪(x : E), (p : E)⟫} =
      range (equatorInclusion (p : E)) := by
  rw [range_equatorInclusion]
  refine Set.ext fun x ↦ ?_
  simp only [mem_inter_iff, mem_ofPred_eq, inner_neg_right, neg_nonneg]
  constructor
  · intro hx
    have hx := frontier_le_subset_eq continuous_const (by fun_prop) hx
    exact ⟨hx.le, hx.ge⟩
  · rintro ⟨h₁, h₂⟩
    have hx : ⟪(x : E), (p : E)⟫ = 0 := le_antisymm h₂ h₁
    rw [frontier_eq_closure_inter_closure]
    refine ⟨subset_closure h₁, ?_⟩
    -- Moving from `x` towards `-p` along a great circle leaves the hemisphere.
    have hγ : Continuous (normalizeSubSmul p x hx) := by
      unfold normalizeSubSmul
      exact .subtype_mk (.smul (.inv₀ (by fun_prop) fun t ↦ (Real.sqrt_pos.2
        (by positivity)).ne') (by fun_prop)) _
    have h₀ : normalizeSubSmul p x hx 0 = x := by
      ext
      simp [normalizeSubSmul]
    rw [← h₀]
    refine map_mem_closure hγ (by simp) (s := Ioi 0) fun t (ht : 0 < t) ↦ ?_
    have hp : ⟪(p : E), (p : E)⟫ = 1 := by
      rw [real_inner_self_eq_norm_sq, norm_eq_of_mem_sphere p, one_pow]
    simp only [mem_compl_iff, mem_ofPred_eq, not_le, normalizeSubSmul, real_inner_smul_left,
      inner_sub_left, hx, hp]
    have hpos : 0 < (√(1 + t ^ 2))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
    nlinarith

/-! ### The latitude map -/

section Latitude

/-- The point of the unit sphere at height `t` over a point `u` of the equator orthogonal to `p`,
`√(1 - t²) • u + t • p`, with `t` clamped to `[-1, 1]`: the pole `p` for `t ≥ 1` and `-p` for
`t ≤ -1`. -/
def latitude (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) : sphere (0 : E) 1 :=
  ⟨√(1 - (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ) ^ 2) • ((u : (ℝ ∙ (p : E))ᗮ) : E) +
      (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ) • (p : E), by
    set s : ℝ := (projIcc (-1 : ℝ) 1 (by norm_num) t : ℝ)
    have hs : s ∈ Icc (-1 : ℝ) 1 := (projIcc (-1 : ℝ) 1 (by norm_num) t).2
    refine mem_sphere_zero_iff_norm.2 (norm_add_smul_eq_one p
      (Submodule.smul_mem _ _ (u : (ℝ ∙ (p : E))ᗮ).2) ?_)
    rw [norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _), Submodule.norm_coe,
      norm_eq_of_mem_sphere u, mul_one, Real.sq_sqrt (by nlinarith [hs.1, hs.2])]
    ring⟩

/-- The latitude map is continuous. -/
theorem continuous_latitude {X : Type*} [TopologicalSpace X]
    {u : X → sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {t : X → ℝ} (hu : Continuous u) (ht : Continuous t) :
    Continuous fun x ↦ latitude p (u x) (t x) := by
  refine Continuous.subtype_mk ?_ _
  have hs : Continuous fun x ↦ (projIcc (-1 : ℝ) 1 (by norm_num) (t x) : ℝ) :=
    continuous_subtype_val.comp (continuous_projIcc.comp ht)
  fun_prop

/-- For `t ∈ [-1, 1]`, the latitude map is `√(1 - t²) • u + t • p`. -/
theorem coe_latitude_of_mem (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {t : ℝ}
    (ht : t ∈ Icc (-1 : ℝ) 1) :
    (latitude p u t : E) = √(1 - t ^ 2) • ((u : (ℝ ∙ (p : E))ᗮ) : E) + t • (p : E) := by
  simp [latitude, projIcc_of_mem _ ht]

/-- For `t ≥ 1`, the latitude map is the pole `p`. -/
theorem latitude_of_one_le (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {t : ℝ} (ht : 1 ≤ t) :
    latitude p u t = p := by
  ext1
  simp [latitude, projIcc_of_right_le _ ht]

/-- For `t ≤ -1`, the latitude map is the pole `-p`. -/
theorem latitude_of_le_neg_one (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) {t : ℝ}
    (ht : t ≤ -1) : latitude p u t = -p := by
  ext1
  simp [latitude, projIcc_of_le_left _ ht]

/-- The height of a point of the latitude map is the clamped parameter. -/
@[simp]
theorem inner_latitude (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    ⟪(latitude p u t : E), (p : E)⟫ = projIcc (-1 : ℝ) 1 (by norm_num) t := by
  have hu : ⟪((u : (ℝ ∙ (p : E))ᗮ) : E), (p : E)⟫ = 0 :=
    Submodule.mem_orthogonal_singleton_iff_inner_left.1 (u : (ℝ ∙ (p : E))ᗮ).2
  simp [latitude, inner_add_left, inner_smul_left, hu]

/-- The latitude map hits the equator exactly at height `0`. -/
theorem inner_latitude_eq_zero_iff (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    ⟪(latitude p u t : E), (p : E)⟫ = 0 ↔ t = 0 := by
  rw [inner_latitude]
  refine ⟨fun h ↦ eq_of_coe_projIcc_eq h ⟨by norm_num, by norm_num⟩, ?_⟩
  rintro rfl
  rw [projIcc_of_mem _ ⟨by norm_num, by norm_num⟩]

/-- The latitude map hits a pole exactly when the parameter lies outside `(-1, 1)`. -/
theorem latitude_mem_pair_iff (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (t : ℝ) :
    latitude p u t ∈ ({p, -p} : Set (sphere (0 : E) 1)) ↔ t ∉ Ioo (-1 : ℝ) 1 := by
  refine ⟨fun h ht ↦ ?_, fun ht ↦ ?_⟩
  · have hp : ⟪(p : E), (p : E)⟫ = 1 := by simp
    have hinner := inner_latitude p u t
    rw [projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at hinner
    rcases h with h | h <;> rw [h] at hinner
    · exact ht.2.ne (hinner.symm.trans hp)
    · rw [coe_neg_sphere, inner_neg_left, hp] at hinner
      exact ht.1.ne hinner
  · rcases le_or_gt t (-1) with h | h
    · exact Or.inr (latitude_of_le_neg_one p u h)
    · exact Or.inl (latitude_of_one_le p u (not_lt.1 fun h' ↦ ht ⟨h, h'⟩))

/-- Off the poles, the latitude map is injective. -/
theorem eq_and_eq_of_latitude_eq {u u' : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1} {t t' : ℝ}
    (ht : t ∈ Ioo (-1 : ℝ) 1) (h : latitude p u t = latitude p u' t') : u = u' ∧ t = t' := by
  have htt : t = t' := by
    have h₁ := inner_latitude p u t
    rw [h, inner_latitude, projIcc_of_mem _ (Ioo_subset_Icc_self ht)] at h₁
    exact (eq_of_coe_projIcc_eq h₁ ht).symm
  subst htt
  refine ⟨?_, rfl⟩
  have hpos : 0 < √(1 - t ^ 2) := Real.sqrt_pos.2 (by nlinarith [ht.1, ht.2])
  have h₂ := congrArg Subtype.val h
  rw [coe_latitude_of_mem p u (Ioo_subset_Icc_self ht),
    coe_latitude_of_mem p u' (Ioo_subset_Icc_self ht), add_left_inj] at h₂
  exact Subtype.ext (Subtype.ext (smul_right_injective E hpos.ne' h₂))

/-- If the equator is nonempty, every point of the unit sphere is a point of the latitude map with
parameter in `[-1, 1]`; the poles are reached over the given point `u₀` of the equator. -/
theorem exists_latitude_eq (u₀ : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) (z : sphere (0 : E) 1) :
    ∃ u t, t ∈ Icc (-1 : ℝ) 1 ∧ latitude p u t = z := by
  set s := ⟪(z : E), (p : E)⟫ with hs_def
  have hzn : ‖(z : E)‖ = 1 := by simp
  have hpn : ‖(p : E)‖ = 1 := by simp
  have hs : |s| ≤ 1 := by simpa [hzn, hpn] using abs_real_inner_le_norm (z : E) (p : E)
  rcases eq_or_ne s 1 with h1 | h1
  · refine ⟨u₀, 1, ⟨by norm_num, le_rfl⟩, ?_⟩
    rw [latitude_of_one_le p u₀ le_rfl]
    exact (Subtype.ext ((inner_eq_one_iff_of_norm_eq_one hzn hpn).1 h1)).symm
  rcases eq_or_ne s (-1) with h2 | h2
  · refine ⟨u₀, -1, ⟨le_rfl, by norm_num⟩, ?_⟩
    rw [latitude_of_le_neg_one p u₀ le_rfl]
    ext1
    rw [coe_neg_sphere]
    have hpn' : ‖-(p : E)‖ = 1 := by rw [norm_neg, hpn]
    refine ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ) hzn hpn').1 ?_).symm
    rw [inner_neg_right, ← hs_def, h2, neg_neg]
  -- Away from the poles, `z` is `w + s • p` with `w ⟂ p` of norm `√(1 - s²)`.
  have hs' : s ∈ Ioo (-1 : ℝ) 1 := by
    rw [abs_le] at hs
    exact ⟨lt_of_le_of_ne hs.1 (Ne.symm h2), lt_of_le_of_ne hs.2 h1⟩
  obtain ⟨hw, hwn⟩ := sub_inner_smul_mem_closedBall p z
  set w : E := (z : E) - s • (p : E)
  have hpos : 0 < √(1 - s ^ 2) := Real.sqrt_pos.2 (by nlinarith [hs'.1, hs'.2])
  have hwn' : ‖w‖ = √(1 - s ^ 2) := by rw [← hwn, Real.sqrt_sq (norm_nonneg _)]
  let u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    ⟨⟨(√(1 - s ^ 2))⁻¹ • w, Submodule.smul_mem _ _ hw⟩, by
        rw [mem_sphere_zero_iff_norm, ← Submodule.norm_coe, Submodule.coe_mk, norm_smul, hwn',
          Real.norm_of_nonneg (inv_nonneg.2 hpos.le), inv_mul_cancel₀ hpos.ne']⟩
  refine ⟨u, s, Ioo_subset_Icc_self hs', Subtype.ext ?_⟩
  rw [coe_latitude_of_mem p u (Ioo_subset_Icc_self hs')]
  simp [u, w, smul_smul, mul_inv_cancel₀ hpos.ne']

end Latitude

/-! ### Two discs glued along their boundary spheres -/

section Gluing

/-- The inverse of `TauCeti.hemisphereHomeomorph p` lifts `y` to height `√(1 - ‖y‖²)` along
`p`. -/
private theorem inner_coe_hemisphereHomeomorph_symm_apply (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ⟪(((hemisphereHomeomorph p).symm y : sphere (0 : E) 1) : E), (p : E)⟫ =
      √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) := by
  rw [coe_hemisphereHomeomorph_symm_apply]
  exact (add_sqrt_smul_mem_sphere p y).2

/-- Every point of the sphere lies in the image of the closed ball under the inverse of
`TauCeti.hemisphereHomeomorph p`, or under that map composed with the antipode. -/
private theorem exists_eq_hemisphereHomeomorph_symm_or_neg (y : sphere (0 : E) 1) :
    ∃ v : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1,
      y = (hemisphereHomeomorph p).symm v ∨ y = -(hemisphereHomeomorph p).symm v := by
  by_cases hy : 0 ≤ ⟪(y : E), (p : E)⟫
  · exact ⟨hemisphereHomeomorph p ⟨y, hy⟩, Or.inl (by simp)⟩
  · have hy' : 0 ≤ ⟪((-y : sphere (0 : E) 1) : E), (p : E)⟫ := by
      rw [coe_neg_sphere, inner_neg_left]
      linarith
    exact ⟨hemisphereHomeomorph p ⟨-y, hy'⟩, Or.inr (by simp)⟩

variable [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X] {A B : Set X}

/-- `TauCeti.nonempty_homeomorph_sphere_of_union_closedBall` for discs in the orthogonal
complement of a unit vector `p`. The first disc is carried onto the closed hemisphere around `p`
by the inverse of `TauCeti.hemisphereHomeomorph p`. The second is carried onto the closed
hemisphere around `-p` after the radial extension of the gluing homeomorphism of the boundary
spheres, so that the two maps agree on `A ∩ B`. -/
private theorem nonempty_homeomorph_sphere_of_union_closedBall_orthogonal
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (eA : A ≃ₜ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) (eB : B ≃ₜ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1)
    (hAe : ∀ x : A, (x : X) ∈ B ↔ ‖(eA x : (ℝ ∙ (p : E))ᗮ)‖ = 1)
    (hBe : ∀ x : B, (x : X) ∈ A ↔ ‖(eB x : (ℝ ∙ (p : E))ᗮ)‖ = 1) :
    Nonempty (X ≃ₜ sphere (0 : E) 1) := by
  classical
  set e := hemisphereHomeomorph p
  obtain ⟨H, hHn, hHB⟩ := Homeomorph.exists_norm_eq_of_closedBall_glue eA eB hAe hBe
  -- The two hemisphere maps, which agree on `A ∩ B`.
  let gA (x : A) : sphere (0 : E) 1 := e.symm (eA x)
  have hmemB (x : B) : -H (eB x) ∈ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg, hHn]
    exact mem_closedBall_zero_iff.1 (eB x).2
  let gB (x : B) : sphere (0 : E) 1 := -(e.symm ⟨_, hmemB x⟩ : sphere (0 : E) 1)
  have hgAB (x : X) (hxA : x ∈ A) (hxB : x ∈ B) : gA ⟨x, hxA⟩ = gB ⟨x, hxB⟩ := by
    ext1
    simp [gA, gB, e, hHB x hxA hxB, (hAe ⟨x, hxA⟩).1 hxB]
  let g : C(X, sphere (0 : E) 1) := ContinuousMap.glueClosedEmbeddings
    (i := (Subtype.val : A → X)) (j := (Subtype.val : B → X)) ⟨gA, by fun_prop⟩
    ⟨gB, by fun_prop⟩ hA.isClosedEmbedding_subtypeVal hB.isClosedEmbedding_subtypeVal
    (by simpa [Subtype.range_coe] using hAB) fun x y h ↦ by
      obtain ⟨x, hx⟩ := x
      obtain ⟨y, hy⟩ := y
      cases h
      exact hgAB x hx hy
  have hg_A (x : A) : g x = gA x := ContinuousMap.glueClosedEmbeddings_apply_left _ _ _ _ _ _ x
  have hg_B (x : B) : g x = gB x := ContinuousMap.glueClosedEmbeddings_apply_right _ _ _ _ _ _ x
  -- `g` sends exactly the points of `A` into the closed hemisphere around `p`.
  have hupper (x : X) : 0 ≤ ⟪(g x : E), (p : E)⟫ ↔ x ∈ A := by
    refine ⟨fun h ↦ ?_, fun hx ↦ hg_A ⟨x, hx⟩ ▸ (e.symm (eA ⟨x, hx⟩)).2⟩
    by_contra hx
    have hxB := Set.compl_subset_iff_union.mpr hAB hx
    rw [hg_B ⟨x, hxB⟩] at h
    simp only [gB, e, coe_neg_sphere, inner_neg_left, inner_coe_hemisphereHomeomorph_symm_apply,
      norm_neg, hHn, neg_nonneg] at h
    have h₀ := Real.sqrt_eq_zero'.1 (le_antisymm h (Real.sqrt_nonneg _))
    refine hx ((hBe ⟨x, hxB⟩).2 (le_antisymm (mem_closedBall_zero_iff.1 (eB _).2) ?_))
    nlinarith [norm_nonneg (eB ⟨x, hxB⟩ : (ℝ ∙ (p : E))ᗮ)]
  -- Injectivity: `g` is injective on `A` and on `B`, whose images lie in opposite hemispheres.
  have hinjA : Function.Injective gA := fun x y h ↦
    eA.injective (e.symm.injective (Subtype.val_injective h))
  have hinjB : Function.Injective gB := fun x y h ↦ by
    have h' : (e.symm ⟨_, hmemB x⟩ : sphere (0 : E) 1) = e.symm ⟨_, hmemB y⟩ :=
      neg_injective h
    exact eB.injective (Subtype.ext (H.injective (neg_injective
      (congrArg Subtype.val (e.symm.injective (Subtype.val_injective h'))))))
  have hinj : Function.Injective g :=
    injective_of_injOn_of_union_eq_univ
      (P := fun y : sphere (0 : E) 1 ↦ 0 ≤ ⟪(y : E), (p : E)⟫) hAB hupper
      (fun x hx y hy h ↦ congrArg Subtype.val
        (hinjA ((hg_A ⟨x, hx⟩).symm.trans (h.trans (hg_A ⟨y, hy⟩)))))
      (fun x hx y hy h ↦ congrArg Subtype.val
        (hinjB ((hg_B ⟨x, hx⟩).symm.trans (h.trans (hg_B ⟨y, hy⟩)))))
  -- Surjectivity: the closed hemispheres around `p` and `-p` cover the sphere.
  have hsurj : Function.Surjective g := by
    intro y
    obtain ⟨v, rfl | rfl⟩ := exists_eq_hemisphereHomeomorph_symm_or_neg p y
    · exact ⟨eA.symm v, by rw [hg_A]; simp [gA, e]⟩
    · have hz : H.symm (-(v : (ℝ ∙ (p : E))ᗮ)) ∈ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 := by
        rw [mem_closedBall_zero_iff, ← hHn (H.symm _), H.apply_symm_apply, norm_neg]
        exact mem_closedBall_zero_iff.1 v.2
      refine ⟨eB.symm ⟨_, hz⟩, ?_⟩
      rw [hg_B]
      have hw : (⟨_, hmemB (eB.symm ⟨_, hz⟩)⟩ : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) = v :=
        Subtype.ext (by simp)
      simp only [gB, hw, e]
  -- A compact space mapping bijectively and continuously onto the sphere is homeomorphic to it.
  have : CompactSpace (closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
    isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
  have : CompactSpace X := ⟨hAB ▸ (isCompact_iff_compactSpace.2 eA.symm.compactSpace).union
    (isCompact_iff_compactSpace.2 eB.symm.compactSpace)⟩
  exact ⟨g.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hinj, hsurj⟩)⟩

omit [FiniteDimensional ℝ E] in
/-- **Two discs glued along their boundary spheres form a sphere.** Let `X` be covered by two
closed sets `A` and `B`, each homeomorphic to the closed unit ball of a real inner product space
`F` of dimension `n`, such that `A ∩ B` corresponds to the unit sphere under both
homeomorphisms. Then `X` is homeomorphic to the unit sphere of any real inner product space of
dimension `n + 1`. The gluing homeomorphism of the boundary spheres is arbitrary: it extends
radially over the disc (`Homeomorph.radialExtension`). For `n = 0`, `A` and `B` are points and
`X` is the two-point sphere `S⁰`. -/
theorem nonempty_homeomorph_sphere_of_union_closedBall {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    (hF : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    (hA : IsClosed A) (hB : IsClosed B) (hAB : A ∪ B = univ)
    (eA : A ≃ₜ closedBall (0 : F) 1) (eB : B ≃ₜ closedBall (0 : F) 1)
    (hAe : ∀ x : A, (x : X) ∈ B ↔ ‖(eA x : F)‖ = 1)
    (hBe : ∀ x : B, (x : X) ∈ A ↔ ‖(eB x : F)‖ = 1) :
    Nonempty (X ≃ₜ sphere (0 : E) 1) := by
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos (by omega)
  have : Fact (Module.finrank ℝ E = Module.finrank ℝ F + 1) := ⟨hF⟩
  have : Nontrivial E := Module.nontrivial_of_finrank_eq_succ hF
  obtain ⟨p⟩ : Nonempty (sphere (0 : E) 1) :=
    (NormedSpace.sphere_nonempty.2 zero_le_one).to_subtype
  -- Identify `F` isometrically with the orthogonal complement of `p`.
  have hdim : Module.finrank ℝ (ℝ ∙ (p : E))ᗮ = Module.finrank ℝ F :=
    Submodule.finrank_orthogonal_span_singleton (ne_zero_of_mem_unit_sphere p)
  let L : F ≃ₗᵢ[ℝ] (ℝ ∙ (p : E))ᗮ :=
    (stdOrthonormalBasis ℝ F).equiv (stdOrthonormalBasis ℝ _) (finCongr hdim.symm)
  let S : closedBall (0 : F) 1 ≃ₜ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    L.toHomeomorph.subtype fun v ↦ by simp
  exact nonempty_homeomorph_sphere_of_union_closedBall_orthogonal p hA hB hAB (eA.trans S)
    (eB.trans S) (fun x ↦ by simpa [S] using hAe x) (fun x ↦ by simpa [S] using hBe x)

end Gluing

end TauCeti
