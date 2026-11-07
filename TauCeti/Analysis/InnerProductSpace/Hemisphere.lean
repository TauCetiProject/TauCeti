/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Orthogonal
public import Mathlib.Analysis.Normed.Group.BallSphere
public import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.Normed.Module.Ball.Radial.Extension

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

## Main definitions

* `TauCeti.hemisphereHomeomorph p`: the closed hemisphere around `p` is homeomorphic to the closed
  unit ball of `(ℝ ∙ p)ᗮ`.
* `TauCeti.equatorInclusion p`: for any vector `p` and radius `r`, the inclusion of the sphere
  of radius `r` in `(ℝ ∙ p)ᗮ` into the sphere of radius `r` in `E`.

## Main results

* `TauCeti.coe_hemisphereHomeomorph_apply` and `TauCeti.coe_hemisphereHomeomorph_symm_apply`:
  the formulas for the homeomorphism and its inverse.
* `TauCeti.frontier_setOf_inner_nonneg`: the equator is the frontier of each closed hemisphere.
* `TauCeti.range_equatorInclusion`: the equator is the intersection of the closed hemispheres
  around `p` and `-p`.
* `TauCeti.isometry_equatorInclusion`: the equator inclusion preserves distances.
* `TauCeti.nonempty_homeomorph_sphere_of_union_closedBall`: two closed discs glued along their
  boundary spheres form a sphere.

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
  refine ⟨?_, by rw [inner_add_left, real_inner_smul_left, hyp, hp, zero_add, mul_one]⟩
  rw [← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero, norm_add_sq_real,
    real_inner_smul_right, hyp, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (by linarith),
    norm_eq_of_mem_sphere p, Submodule.norm_coe]
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

/-! ### Two discs glued along their boundary spheres -/

section Gluing

/-- The inverse of `TauCeti.hemisphereHomeomorph p` lifts `y` to height `√(1 - ‖y‖²)` along
`p`. -/
private theorem inner_coe_hemisphereHomeomorph_symm_apply (y : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :
    ⟪(((hemisphereHomeomorph p).symm y : sphere (0 : E) 1) : E), (p : E)⟫ =
      √(1 - ‖(y : (ℝ ∙ (p : E))ᗮ)‖ ^ 2) := by
  rw [coe_hemisphereHomeomorph_symm_apply]
  exact (add_sqrt_smul_mem_sphere p y).2

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
  -- The gluing homeomorphism `eA ∘ eB⁻¹` of the boundary spheres, and its radial extension.
  have memA (u : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
      ((eB.symm ⟨u, sphere_subset_closedBall u.2⟩ : B) : X) ∈ A :=
    (hBe _).2 (by simp [norm_eq_of_mem_sphere u])
  have memB (v : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1) :
      ((eA.symm ⟨v, sphere_subset_closedBall v.2⟩ : A) : X) ∈ B :=
    (hAe _).2 (by simp [norm_eq_of_mem_sphere v])
  let t : sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 ≃ₜ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
    { toFun u := ⟨eA ⟨_, memA u⟩, mem_sphere_zero_iff_norm.2 ((hAe _).1 (eB.symm _).2)⟩
      invFun v := ⟨eB ⟨_, memB v⟩, mem_sphere_zero_iff_norm.2 ((hBe _).1 (eA.symm _).2)⟩
      left_inv u := by ext; simp
      right_inv v := by ext; simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  set H := Homeomorph.radialExtension t
  have hHn (v : (ℝ ∙ (p : E))ᗮ) : ‖H v‖ = ‖v‖ := Homeomorph.norm_radialExtension t v
  have hHn' (v : (ℝ ∙ (p : E))ᗮ) : ‖H.symm v‖ = ‖v‖ := by
    rw [Homeomorph.radialExtension_symm, Homeomorph.norm_radialExtension]
  have hHB (x : X) (hxA : x ∈ A) (hxB : x ∈ B) : H (eB ⟨x, hxB⟩) = eA ⟨x, hxA⟩ := by
    have hn : (eB ⟨x, hxB⟩ : (ℝ ∙ (p : E))ᗮ) ∈ sphere (0 : (ℝ ∙ (p : E))ᗮ) 1 :=
      mem_sphere_zero_iff_norm.2 ((hBe _).1 hxA)
    refine (Homeomorph.radialExtension_coe_sphere t ⟨_, hn⟩).trans ?_
    simp [t]
  -- The two hemisphere maps, which agree on `A ∩ B`.
  let gA (x : A) : sphere (0 : E) 1 := e.symm (eA x)
  have hmemB (x : B) : -H (eB x) ∈ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 := by
    rw [mem_closedBall_zero_iff, norm_neg, hHn]
    exact mem_closedBall_zero_iff.1 (eB x).2
  let gB (x : B) : sphere (0 : E) 1 := -(e.symm ⟨_, hmemB x⟩ : sphere (0 : E) 1)
  have hgAB (x : X) (hxA : x ∈ A) (hxB : x ∈ B) : gA ⟨x, hxA⟩ = gB ⟨x, hxB⟩ := by
    ext1
    simp [gA, gB, e, hHB x hxA hxB, (hAe ⟨x, hxA⟩).1 hxB]
  have hcov (x : X) (hx : x ∉ A) : x ∈ B := (hAB.symm ▸ mem_univ x : x ∈ A ∪ B).resolve_left hx
  let g (x : X) : sphere (0 : E) 1 := if hx : x ∈ A then gA ⟨x, hx⟩ else gB ⟨x, hcov x hx⟩
  have hg_A (x : A) : g x = gA x := dite_eq_left x.2
  have hg_B (x : B) : g x = gB x := by
    by_cases hx : (x : X) ∈ A
    · exact (hg_A ⟨x, hx⟩).trans (hgAB x hx x.2)
    · exact dite_eq_right hx
  -- Continuity, by the pasting lemma for the closed cover `A ∪ B`.
  have hgA : Continuous gA := by fun_prop
  have hgB : Continuous gB := by fun_prop
  have hg : Continuous g := by
    have hcA : ContinuousOn g A := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (funext hg_A : A.domRestrict g = gA) ▸ hgA
    have hcB : ContinuousOn g B := by
      rw [continuousOn_iff_continuous_domRestrict]
      exact (funext hg_B : B.domRestrict g = gB) ▸ hgB
    exact continuousOn_univ.1 (hAB ▸ hcA.union_of_isClosed hcB hA hB)
  -- Injectivity: `g` is injective on `A` and on `B`, whose images lie in opposite hemispheres.
  have hinjA : Function.Injective gA := fun x y h ↦
    eA.injective (e.symm.injective (Subtype.val_injective h))
  have hinjB : Function.Injective gB := fun x y h ↦ by
    have h' := e.symm.injective (Subtype.val_injective (neg_injective h))
    exact eB.injective (Subtype.ext (H.injective (neg_injective (congrArg Subtype.val h'))))
  -- `g` sends exactly the points of `A` into the closed hemisphere around `p`.
  have hupper (x : X) : 0 ≤ ⟪(g x : E), (p : E)⟫ ↔ x ∈ A := by
    refine ⟨fun h ↦ ?_, fun hx ↦ hg_A ⟨x, hx⟩ ▸ (e.symm (eA ⟨x, hx⟩)).2⟩
    by_contra hx
    have hxB := hcov x hx
    rw [hg_B ⟨x, hxB⟩] at h
    simp only [gB, e, coe_neg_sphere, inner_neg_left, inner_coe_hemisphereHomeomorph_symm_apply,
      norm_neg, hHn, neg_nonneg] at h
    have h₀ := Real.sqrt_eq_zero'.1 (le_antisymm h (Real.sqrt_nonneg _))
    refine hx ((hBe ⟨x, hxB⟩).2 (le_antisymm (mem_closedBall_zero_iff.1 (eB _).2) ?_))
    nlinarith [norm_nonneg (eB ⟨x, hxB⟩ : (ℝ ∙ (p : E))ᗮ)]
  have hinj : Function.Injective g := by
    intro x y hxy
    have hxy' : x ∈ A ↔ y ∈ A := by rw [← hupper, ← hupper, hxy]
    by_cases hx : x ∈ A
    · exact congrArg Subtype.val
        (hinjA ((hg_A ⟨x, hx⟩).symm.trans (hxy.trans (hg_A ⟨y, hxy'.1 hx⟩))))
    · exact congrArg Subtype.val (hinjB ((hg_B ⟨x, hcov x hx⟩).symm.trans
        (hxy.trans (hg_B ⟨y, hcov y (hxy'.not.1 hx)⟩))))
  -- Surjectivity: the closed hemispheres around `p` and `-p` cover the sphere.
  have hsurj : Function.Surjective g := by
    intro y
    by_cases hy : 0 ≤ ⟪(y : E), (p : E)⟫
    · refine ⟨eA.symm (e ⟨y, hy⟩), ?_⟩
      rw [hg_A]
      simp [gA]
    · have hy' : 0 ≤ ⟪((-y : sphere (0 : E) 1) : E), (p : E)⟫ := by
        rw [coe_neg_sphere, inner_neg_left]
        linarith
      have hz : H.symm (-(e ⟨-y, hy'⟩ : (ℝ ∙ (p : E))ᗮ)) ∈ closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1 := by
        rw [mem_closedBall_zero_iff, hHn', norm_neg]
        exact mem_closedBall_zero_iff.1 (e ⟨-y, hy'⟩).2
      refine ⟨eB.symm ⟨_, hz⟩, ?_⟩
      rw [hg_B]
      have hw : (⟨_, hmemB (eB.symm ⟨_, hz⟩)⟩ : closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) = e ⟨-y, hy'⟩ :=
        Subtype.ext (by simp)
      simp only [gB, hw, Homeomorph.symm_apply_apply, neg_neg]
  -- A compact space mapping bijectively and continuously onto the sphere is homeomorphic to it.
  have hAc : IsCompact A :=
    have : CompactSpace (closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
      isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
    isCompact_iff_compactSpace.2 eA.symm.compactSpace
  have hBc : IsCompact B :=
    have : CompactSpace (closedBall (0 : (ℝ ∙ (p : E))ᗮ) 1) :=
      isCompact_iff_compactSpace.1 (isCompact_closedBall _ _)
    isCompact_iff_compactSpace.2 eB.symm.compactSpace
  have : CompactSpace X := ⟨hAB ▸ hAc.union hBc⟩
  exact ⟨hg.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g ⟨hinj, hsurj⟩)⟩

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
