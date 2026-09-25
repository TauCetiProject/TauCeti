/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Analysis.Normed.Module.Basic

/-!
# The unit sphere is a closed cofibration in the closed unit ball

The unit sphere of a real normed space has the homotopy extension property inside the closed
unit ball.  Concretely, the cylinder `I × D` over the closed unit ball `D` retracts onto
`D × {0} ∪ S × I`, where `S` is the unit sphere, by radial projection away from the point of the
cylinder axis at height `2`: the ray from that point through `(t, x)` leaves the cylinder either
through its bottom face or through its side, and the retraction sends `(t, x)` to that exit
point.

This is the basic example of a closed cofibration.  It is the geometric input for the homotopy
extension property of the inclusion of a skeleton of a CW complex into the next one, whose cells
are attached along maps defined on such spheres.

## Main declarations

* `TauCeti.hasHomotopyExtensionProperty_sphere`: **the unit sphere has the homotopy extension
  property inside the closed unit ball.**

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, Example 0.15.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set unitInterval

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Radial projection of the cylinder over the closed unit ball away from the point at height `2`
on its axis, written in the ambient coordinates `ℝ × E`.  Where the ray exits through the bottom
face the value has time coordinate `0`; on the remaining region the space coordinate has unit
norm.  The truncated norm `max ‖x‖ 2⁻¹` in the second branch agrees with `‖x‖` wherever that
branch is used, and keeps the formula continuous at `x = 0`. -/
private def ballRadialProjection (p : I × closedBall (0 : E) 1) : ℝ × E :=
  if (p.1 : ℝ) ≤ 2 - 2 * ‖(p.2 : E)‖ then
    (0, (2 / (2 - (p.1 : ℝ))) • (p.2 : E))
  else
    ((2 * max ‖(p.2 : E)‖ 2⁻¹ + (p.1 : ℝ) - 2) / max ‖(p.2 : E)‖ 2⁻¹,
      (max ‖(p.2 : E)‖ 2⁻¹)⁻¹ • (p.2 : E))

omit [NormedSpace ℝ E] in
private lemma max_norm_ne_zero (p : I × closedBall (0 : E) 1) :
    max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))

omit [NormedSpace ℝ E] in
private lemma two_sub_ne_zero (p : I × closedBall (0 : E) 1) : (2 : ℝ) - (p.1 : ℝ) ≠ 0 :=
  ne_of_gt (by have := p.1.2.2; linarith)

private lemma continuous_ballRadialProjection : Continuous (ballRadialProjection (E := E)) := by
  have hvec : Continuous fun p : I × closedBall (0 : E) 1 => ((p.2 : E)) := by fun_prop
  have hmax : Continuous fun p : I × closedBall (0 : E) 1 => max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ := by
    fun_prop
  refine Continuous.if_le ?_ ?_ (by fun_prop) (by fun_prop) ?_
  · exact continuous_const.prodMk
      ((continuous_const.div (by fun_prop) two_sub_ne_zero).smul hvec)
  · exact ((by fun_prop : Continuous fun p : I × closedBall (0 : E) 1 =>
        2 * max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ + (p.1 : ℝ) - 2).div hmax max_norm_ne_zero).prodMk
      ((hmax.inv₀ max_norm_ne_zero).smul hvec)
  · rintro p hp
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hn : (2 : ℝ)⁻¹ ≤ ‖(p.2 : E)‖ := by rw [hp] at ht1; linarith
    have hnpos : (0 : ℝ) < ‖(p.2 : E)‖ := lt_of_lt_of_le (by norm_num) hn
    have h1 : (2 : ℝ) - (2 - 2 * ‖(p.2 : E)‖) = 2 * ‖(p.2 : E)‖ := by ring
    have h2 : (2 : ℝ) / (2 * ‖(p.2 : E)‖) = ‖(p.2 : E)‖⁻¹ := by field_simp
    have h3 : (2 * ‖(p.2 : E)‖ + (2 - 2 * ‖(p.2 : E)‖) - 2) / ‖(p.2 : E)‖ = 0 := by
      rw [show 2 * ‖(p.2 : E)‖ + (2 - 2 * ‖(p.2 : E)‖) - 2 = (0 : ℝ) from by ring, zero_div]
    rw [max_eq_left hn, hp, h1, h2, h3]

/-- The radial projection lands in the cylinder, and in the union of its bottom face with the
part of the cylinder lying over the sphere. -/
private lemma ballRadialProjection_spec (p : I × closedBall (0 : E) 1) :
    (ballRadialProjection p).1 ∈ I ∧ (ballRadialProjection p).2 ∈ closedBall (0 : E) 1 ∧
      ((ballRadialProjection p).1 = 0 ∨ (ballRadialProjection p).2 ∈ sphere (0 : E) 1) := by
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  have hn1 : ‖(p.2 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 p.2.2
  have hn0 : (0 : ℝ) ≤ ‖(p.2 : E)‖ := norm_nonneg _
  simp only [ballRadialProjection]
  split_ifs with h
  · have h2t : (0 : ℝ) < 2 - (p.1 : ℝ) := by linarith
    have hpos : (0 : ℝ) < 2 / (2 - (p.1 : ℝ)) := by positivity
    refine ⟨unitInterval.zero_mem, ?_, Or.inl rfl⟩
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hpos,
      div_mul_eq_mul_div, div_le_one h2t]
    linarith
  · rw [not_le] at h
    have hn : (2 : ℝ)⁻¹ < ‖(p.2 : E)‖ := by linarith
    have hnpos : (0 : ℝ) < ‖(p.2 : E)‖ := lt_trans (by norm_num) hn
    have hunit : ‖(‖(p.2 : E)‖⁻¹ • (p.2 : E))‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hnpos),
        inv_mul_cancel₀ (ne_of_gt hnpos)]
    rw [max_eq_left hn.le]
    refine ⟨?_, ?_, Or.inr ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨div_nonneg (by linarith) hnpos.le, by rw [div_le_one hnpos]; linarith⟩
    · rw [mem_closedBall_zero_iff, hunit]
    · rw [mem_sphere_zero_iff_norm, hunit]

/-- The radial projection fixes the bottom face of the cylinder and the part of the cylinder
lying over the sphere. -/
private lemma ballRadialProjection_eq_self (p : I × closedBall (0 : E) 1)
    (hp : p ∈ cylinderBase (Subtype.val ⁻¹' sphere (0 : E) 1)) :
    ballRadialProjection p = ((p.1 : ℝ), (p.2 : E)) := by
  have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  rw [mem_cylinderBase_iff] at hp
  by_cases ht : (p.1 : ℝ) ≤ 2 - 2 * ‖(p.2 : E)‖
  · -- The first branch applies, and the point lies on the bottom face of the cylinder.
    have hzero : (p.1 : ℝ) = 0 := by
      obtain h0 | hs := hp
      · exact congrArg Subtype.val h0
      · rw [mem_sphere_zero_iff_norm.1 hs] at ht
        linarith
    rw [show ballRadialProjection p = (0, (2 / (2 - (p.1 : ℝ))) • (p.2 : E)) from ite_eq_left ht,
      hzero]
    norm_num
  · -- The second branch applies, and the point lies over the sphere.
    have hn : ‖(p.2 : E)‖ = 1 := by
      obtain h0 | hs := hp
      · have hz : (p.1 : ℝ) = 0 := congrArg Subtype.val h0
        have hb : ‖(p.2 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 p.2.2
        exact absurd (by rw [hz]; linarith) ht
      · exact mem_sphere_zero_iff_norm.1 hs
    rw [show ballRadialProjection p =
        ((2 * max ‖(p.2 : E)‖ 2⁻¹ + (p.1 : ℝ) - 2) / max ‖(p.2 : E)‖ 2⁻¹,
          (max ‖(p.2 : E)‖ 2⁻¹)⁻¹ • (p.2 : E)) from ite_eq_right ht,
      hn, max_eq_left (by norm_num : (2 : ℝ)⁻¹ ≤ 1)]
    norm_num

/-- The retraction of the cylinder over the closed unit ball onto the union of its bottom face
with the part lying over the unit sphere. -/
private def ballCylinderRetraction :
    C(I × closedBall (0 : E) 1, I × closedBall (0 : E) 1) where
  toFun p := (⟨(ballRadialProjection p).1, (ballRadialProjection_spec p).1⟩,
    ⟨(ballRadialProjection p).2, (ballRadialProjection_spec p).2.1⟩)
  continuous_toFun :=
    (continuous_ballRadialProjection.fst.subtype_mk _).prodMk
      (continuous_ballRadialProjection.snd.subtype_mk _)

/-- **The unit sphere of a real normed space has the homotopy extension property inside the
closed unit ball**: the inclusion of the boundary sphere of a disk is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_sphere :
    HasHomotopyExtensionProperty
      (Subtype.val ⁻¹' sphere (0 : E) 1 : Set (closedBall (0 : E) 1)) := by
  refine hasHomotopyExtensionProperty_of_retraction
    (isClosed_sphere.preimage continuous_subtype_val) (r := ballCylinderRetraction)
    (fun p => ?_) (fun p hp => ?_)
  · rw [mem_cylinderBase_iff]
    obtain h0 | hs := (ballRadialProjection_spec p).2.2
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr hs
  · have h := ballRadialProjection_eq_self p hp
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

end TauCeti
