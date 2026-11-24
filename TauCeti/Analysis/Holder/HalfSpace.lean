/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.HyperplaneReflection
public import TauCeti.Topology.MetricSpace.Holder
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Affine.Convex

/-!
# Hölder continuity up to a hyperplane

Let `v` be a unit vector of a real inner product space and let `S` be a convex set in the closed
half-space `0 ≤ ⟪x, v⟫`. This file collects two ways of proving that a function is Hölder
continuous on `S` up to the hyperplane `⟪x, v⟫ = 0`, as needed for boundary regularity at a flat
boundary.

* **From weighted derivative bounds**
  (`TauCeti.holderOnWith_of_norm_fderiv_le_mul_rpow`). Let `0 < α ≤ 1`. If `φ` is `α`-Hölder on the
  hyperplane, its values differ from those at the foot `x - ⟪x, v⟫ v` by at most `K ⟪x, v⟫^α`, and
  its derivative is at most `K ⟪x, v⟫^(α - 1)` above the hyperplane, then `φ` is `α`-Hölder on `S`
  with constant `5 K`. The derivative may blow up at the hyperplane, at the rate allowed by the
  exponent. This is the classical criterion behind Hölder estimates up to the boundary for
  functions built from the derivatives of harmonic extensions.
* **Odd reflection**
  (`TauCeti.holderOnWith_ite_neg_comp_hyperplaneReflection`). If `φ` is `α`-Hölder on the part
  of a convex reflection-invariant set `S` in the closed half-space and vanishes on the hyperplane,
  then its odd reflection, `φ` above the hyperplane and `-φ ∘ ρ` below it, is `α`-Hölder on all of
  `S` with constant `2 K`.

## The argument

For the first criterion, let `x, y ∈ S` at distance `d`. If both heights are at most `2 d`, pass
through the feet `x'`, `y'` of `x` and `y`, which are at distance at most `d`, and use the bound at
the feet and the Hölder bound on the hyperplane. Otherwise one of them, say `x`, has height
`⟪x, v⟫ > 2 d`; then the whole segment `[x, y]` lies at height at least `d`, where the derivative
is at most `K d^(α - 1)`, and the mean value theorem gives `K d^α`.
-/

public section

noncomputable section

open Set

open scoped NNReal RealInnerProductSpace

namespace TauCeti

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {v : F}

/-- The case of the Hölder criterion in which `x` lies at height above twice its distance to `y`:
the segment `[x, y]` stays at height at least `dist x y`, where the derivative is controlled. -/
private theorem dist_le_of_two_mul_dist_lt {v : F} (hv : ‖v‖ = 1) {α : ℝ≥0} (hα1 : α ≤ 1)
    {S : Set F} (hS : Convex ℝ S) {φ : F → G} {K : ℝ≥0}
    (hd : ∀ x ∈ S, 0 < ⟪x, v⟫ →
      DifferentiableAt ℝ φ x ∧ ‖fderiv ℝ φ x‖ ≤ K * ⟪x, v⟫ ^ ((α : ℝ) - 1))
    {x y : F} (hx : x ∈ S) (hy : y ∈ S) (hxy : 0 < dist x y) (h2 : 2 * dist x y < ⟪x, v⟫) :
    dist (φ x) (φ y) ≤ K * dist x y ^ (α : ℝ) := by
  set d := dist x y
  have hseg : segment ℝ x y ⊆ S := hS.segment_subset hx hy
  -- Points of the segment lie at height at least `d`.
  have hheight : ∀ z ∈ segment ℝ x y, d ≤ ⟪z, v⟫ := by
    intro z hz
    have hzx : dist z x ≤ d := by
      rw [dist_comm]
      linarith [dist_add_dist_of_mem_segment hz, dist_nonneg (x := z) (y := y)]
    have := abs_inner_sub_inner_le hv x z
    rw [abs_le, dist_comm] at this
    linarith
  have hbound : ∀ z ∈ segment ℝ x y, ‖fderiv ℝ φ z‖ ≤ K * d ^ ((α : ℝ) - 1) := by
    intro z hz
    have hz0 : 0 < ⟪z, v⟫ := hxy.trans_le (hheight z hz)
    refine (hd z (hseg hz) hz0).2.trans (mul_le_mul_of_nonneg_left ?_ K.property)
    exact Real.rpow_le_rpow_of_nonpos hxy (hheight z hz) (by linarith [show (α : ℝ) ≤ 1 from hα1])
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz ↦ (hd z (hseg hz) (hxy.trans_le (hheight z hz))).1) hbound (convex_segment x y)
    (left_mem_segment ℝ x y) (right_mem_segment ℝ x y)
  rw [dist_eq_norm, norm_sub_rev]
  refine hmvt.trans_eq ?_
  rw [← dist_eq_norm, dist_comm, mul_assoc, ← Real.rpow_add_one hxy.ne', sub_add_cancel]

/-- **Hölder continuity from weighted derivative bounds.** Let `v` be a unit vector, `0 < α ≤ 1`,
and let `S` be a convex set in the closed half-space `0 ≤ ⟪x, v⟫` containing the foot
`x - ⟪x, v⟫ v` of each of its points. Suppose that `φ` is `α`-Hölder with constant `K` on the part
of `S` on the hyperplane, that `‖φ x - φ (x - ⟪x, v⟫ v)‖ ≤ K ⟪x, v⟫^α` on `S`, and that above the
hyperplane `φ` is differentiable with `‖Dφ x‖ ≤ K ⟪x, v⟫^(α - 1)`. Then `φ` is `α`-Hölder on `S`
with constant `5 K`. -/
theorem holderOnWith_of_norm_fderiv_le_mul_rpow (hv : ‖v‖ = 1) {α : ℝ≥0} (hα1 : α ≤ 1)
    {S : Set F} (hS : Convex ℝ S) (hS0 : ∀ x ∈ S, 0 ≤ ⟪x, v⟫)
    (hfoot : ∀ x ∈ S, x - ⟪x, v⟫ • v ∈ S) {φ : F → G} {K : ℝ≥0}
    (hd : ∀ x ∈ S, 0 < ⟪x, v⟫ →
      DifferentiableAt ℝ φ x ∧ ‖fderiv ℝ φ x‖ ≤ K * ⟪x, v⟫ ^ ((α : ℝ) - 1))
    (hb : ∀ x ∈ S, ‖φ x - φ (x - ⟪x, v⟫ • v)‖ ≤ K * ⟪x, v⟫ ^ (α : ℝ))
    (hH : HolderOnWith K α φ {x ∈ S | ⟪x, v⟫ = 0}) :
    HolderOnWith (5 * K) α φ S := by
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  set d := dist x y
  rcases (dist_nonneg : 0 ≤ d).eq_or_lt with hd0 | hd0
  · have hxy : x = y := dist_eq_zero.1 hd0.symm
    subst hxy
    rw [dist_self]
    positivity
  have hK : 0 ≤ (K : ℝ) * d ^ (α : ℝ) := by positivity
  have h5 : (K : ℝ) * d ^ (α : ℝ) ≤ ((5 * K : ℝ≥0) : ℝ) * d ^ (α : ℝ) := by
    push_cast
    nlinarith
  by_cases hx2 : 2 * d < ⟪x, v⟫
  · exact (dist_le_of_two_mul_dist_lt hv hα1 hS hd hx hy hd0 hx2).trans h5
  by_cases hy2 : 2 * d < ⟪y, v⟫
  · have h := dist_le_of_two_mul_dist_lt hv hα1 hS hd hy hx (by rwa [dist_comm])
      (by rwa [dist_comm])
    rw [dist_comm, dist_comm y x] at h
    exact h.trans h5
  push Not at hx2 hy2
  -- Both points are close to the hyperplane: pass through their feet.
  -- The foot `z - ⟪z, v⟫ v` is the orthogonal projection of `z` onto `(ℝ ∙ v)ᗮ`.
  have hproj : ∀ z, z - ⟪z, v⟫ • v = z - (ℝ ∙ v).starProjection z := fun z ↦ by
    rw [Submodule.starProjection_unit_singleton ℝ hv, real_inner_comm]
  have hfoot0 : ∀ z, ⟪z - ⟪z, v⟫ • v, v⟫ = 0 := fun z ↦ by
    rw [hproj, ← Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact Submodule.sub_starProjection_mem_orthogonal z
  set x' := x - ⟪x, v⟫ • v
  set y' := y - ⟪y, v⟫ • v
  have hx'H : x' ∈ {x ∈ S | ⟪x, v⟫ = 0} := ⟨hfoot x hx, hfoot0 x⟩
  have hy'H : y' ∈ {x ∈ S | ⟪x, v⟫ = 0} := ⟨hfoot y hy, hfoot0 y⟩
  have hx'y' : dist x' y' ≤ d := by
    have : x' - y' = (ℝ ∙ v)ᗮ.starProjection (x - y) := by
      rw [Submodule.starProjection_orthogonal_val, ← hproj]
      simp only [x', y', inner_sub_left, sub_smul]
      abel
    rw [dist_eq_norm, this]
    exact (Submodule.norm_starProjection_apply_le _ _).trans_eq (dist_eq_norm x y).symm
  have h2d : ∀ t : ℝ, 0 ≤ t → t ≤ 2 * d → t ^ (α : ℝ) ≤ 2 * d ^ (α : ℝ) := by
    intro t ht0 ht
    calc t ^ (α : ℝ) ≤ (2 * d) ^ (α : ℝ) := Real.rpow_le_rpow ht0 ht α.property
      _ = 2 ^ (α : ℝ) * d ^ (α : ℝ) := Real.mul_rpow (by norm_num) dist_nonneg
      _ ≤ 2 ^ (1 : ℝ) * d ^ (α : ℝ) := by
          gcongr
          · norm_num
          · exact hα1
      _ = 2 * d ^ (α : ℝ) := by rw [Real.rpow_one]
  calc dist (φ x) (φ y) ≤ dist (φ x) (φ x') + dist (φ x') (φ y') + dist (φ y') (φ y) :=
        dist_triangle4 _ _ _ _
    _ ≤ K * ⟪x, v⟫ ^ (α : ℝ) + K * d ^ (α : ℝ) + K * ⟪y, v⟫ ^ (α : ℝ) := by
        gcongr
        · rw [dist_eq_norm]
          exact hb x hx
        · exact (hH.dist_le hx'H hy'H).trans
            (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow dist_nonneg hx'y' α.property) K.property)
        · rw [dist_eq_norm, norm_sub_rev]
          exact hb y hy
    _ ≤ K * (2 * d ^ (α : ℝ)) + K * d ^ (α : ℝ) + K * (2 * d ^ (α : ℝ)) := by
        gcongr
        · exact h2d _ (hS0 x hx) hx2
        · exact h2d _ (hS0 y hy) hy2
    _ = ((5 * K : ℝ≥0) : ℝ) * d ^ (α : ℝ) := by
        push_cast
        ring

omit [NormedSpace ℝ G] in
/-- The odd reflection of a function across the hyperplane `⟪x, v⟫ = 0`, in the case of points
on opposite sides: passing through the point of the segment on the hyperplane. -/
private theorem dist_ite_neg_comp_hyperplaneReflection_le {v : F} (hv : v ≠ 0) {α : ℝ≥0}
    {S : Set F} (hS : Convex ℝ S) {φ : F → G} {K : ℝ≥0}
    (hφ : HolderOnWith K α φ (S ∩ {x | 0 ≤ ⟪x, v⟫}))
    (hzero : ∀ x ∈ S, ⟪x, v⟫ = 0 → φ x = 0) (hρS : ∀ x ∈ S, hyperplaneReflection v 0 x ∈ S)
    {x y : F} (hx : x ∈ S) (hy : y ∈ S) (hx0 : 0 ≤ ⟪x, v⟫) (hy0 : ⟪y, v⟫ < 0) :
    dist (φ x) (-φ (hyperplaneReflection v 0 y)) ≤ 2 * K * dist x y ^ (α : ℝ) := by
  set a := ⟪x, v⟫
  set b := -⟪y, v⟫
  have hb : 0 < b := neg_pos.2 hy0
  have hab : 0 < a + b := by positivity
  -- The point `z` of the segment `[x, y]` on the hyperplane.
  set z := (b / (a + b)) • x + (a / (a + b)) • y
  have hsum : b / (a + b) + a / (a + b) = 1 := by
    rw [← add_div, add_comm b a, div_self hab.ne']
  have hzseg : z ∈ segment ℝ x y := ⟨_, _, by positivity, by positivity, hsum, rfl⟩
  have hzS : z ∈ S := hS.segment_subset hx hy hzseg
  have hz0 : ⟪z, v⟫ = 0 := by
    have hy : ⟪y, v⟫ = -b := by simp [b]
    simp only [z, inner_add_left, inner_smul_left, RCLike.conj_to_real, hy]
    field_simp
    ring
  -- `z` lies on the segment `[x, y]`, so it is within `dist x y` of both endpoints.
  have hxzy := dist_add_dist_of_mem_segment hzseg
  have hxz : dist x z ≤ dist x y := by linarith [dist_nonneg (x := z) (y := y)]
  have hyz : dist y z ≤ dist x y := by
    rw [dist_comm]
    linarith [dist_nonneg (x := x) (y := z)]
  have hρy : hyperplaneReflection v 0 y ∈ S ∩ {x | 0 ≤ ⟪x, v⟫} :=
    ⟨hρS y hy, by rw [mem_ofPred_eq, inner_hyperplaneReflection hv]; linarith⟩
  have hρz : hyperplaneReflection v 0 z = z := hyperplaneReflection_eq_self_of_inner_eq hz0
  have hzS' : z ∈ S ∩ {x | 0 ≤ ⟪x, v⟫} := ⟨hzS, hz0.ge⟩
  have hφz : φ z = 0 := hzero z hzS hz0
  have hdρ : dist (hyperplaneReflection v 0 y) z = dist y z := by
    rw [← hρz, (hyperplaneReflection v 0).dist_map, hρz]
  calc dist (φ x) (-φ (hyperplaneReflection v 0 y))
      = ‖(φ x - φ z) + (φ (hyperplaneReflection v 0 y) - φ z)‖ := by
        rw [dist_eq_norm, hφz]
        simp
    _ ≤ dist (φ x) (φ z) + dist (φ (hyperplaneReflection v 0 y)) (φ z) := by
        rw [dist_eq_norm, dist_eq_norm]
        exact norm_add_le _ _
    _ ≤ K * dist x z ^ (α : ℝ) + K * dist (hyperplaneReflection v 0 y) z ^ (α : ℝ) :=
        add_le_add (hφ.dist_le ⟨hx, hx0⟩ hzS') (hφ.dist_le hρy hzS')
    _ ≤ K * dist x y ^ (α : ℝ) + K * dist x y ^ (α : ℝ) := by
        rw [hdρ]
        gcongr
    _ = 2 * K * dist x y ^ (α : ℝ) := by ring

omit [NormedSpace ℝ G] in
/-- **Hölder continuity of an odd reflection.** Let `v` be a nonzero vector and `ρ` the reflection
in the hyperplane `⟪x, v⟫ = 0`. Let `S` be convex with `ρ S ⊆ S`, and let `φ` be `α`-Hölder with
constant `K` on the part of `S` in the closed half-space `0 ≤ ⟪x, v⟫` and vanish on the
hyperplane. Then the odd reflection of `φ`, equal to `φ` on the closed half-space and to `-φ ∘ ρ`
on the other side, is `α`-Hölder on `S` with constant `2 K`. -/
theorem holderOnWith_ite_neg_comp_hyperplaneReflection (hv : v ≠ 0) {α : ℝ≥0} {S : Set F}
    (hS : Convex ℝ S) (hρS : ∀ x ∈ S, hyperplaneReflection v 0 x ∈ S) {φ : F → G} {K : ℝ≥0}
    (hφ : HolderOnWith K α φ (S ∩ {x | 0 ≤ ⟪x, v⟫}))
    (hzero : ∀ x ∈ S, ⟪x, v⟫ = 0 → φ x = 0) :
    HolderOnWith (2 * K) α
      (fun x ↦ if 0 ≤ ⟪x, v⟫ then φ x else -φ (hyperplaneReflection v 0 x)) S := by
  refine HolderOnWith.of_dist_le fun x hx y hy ↦ ?_
  have hK : (K : ℝ) * dist x y ^ (α : ℝ) ≤ 2 * K * dist x y ^ (α : ℝ) := by
    have : 0 ≤ (K : ℝ) * dist x y ^ (α : ℝ) := by positivity
    linarith
  push_cast
  by_cases hx0 : 0 ≤ ⟪x, v⟫ <;> by_cases hy0 : 0 ≤ ⟪y, v⟫ <;> simp only [hx0, hy0, ↓reduceIte]
  · exact (hφ.dist_le ⟨hx, hx0⟩ ⟨hy, hy0⟩).trans hK
  · exact dist_ite_neg_comp_hyperplaneReflection_le hv hS hφ hzero hρS hx hy hx0 (not_le.1 hy0)
  · rw [dist_comm, dist_comm x y]
    exact dist_ite_neg_comp_hyperplaneReflection_le hv hS hφ hzero hρS hy hx hy0 (not_le.1 hx0)
  · have hρ : ∀ w ∈ S, ⟪w, v⟫ < 0 → hyperplaneReflection v 0 w ∈ S ∩ {x | 0 ≤ ⟪x, v⟫} :=
      fun w hw hw0 ↦ ⟨hρS w hw, by rw [mem_ofPred_eq, inner_hyperplaneReflection hv]; linarith⟩
    rw [dist_neg_neg]
    refine (hφ.dist_le (hρ x hx (not_le.1 hx0)) (hρ y hy (not_le.1 hy0))).trans ?_
    rw [(hyperplaneReflection v 0).dist_map]
    exact hK

end TauCeti
