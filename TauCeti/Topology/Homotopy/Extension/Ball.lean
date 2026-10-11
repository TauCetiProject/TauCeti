/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Extension.Basic
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Analysis.Normed.Module.Convex

/-!
# The unit sphere is a closed cofibration in the closed unit ball

The unit sphere of a real seminormed space has the homotopy extension property inside the closed
unit ball.  Concretely, the cylinder `I × D` over the closed unit ball `D` retracts onto
`{0} × D ∪ I × S`, where `S` is the unit sphere, by radial projection away from the point of the
cylinder axis at height `2`: the ray from that point through `(t, x)` leaves the cylinder either
through its bottom face or through its side, and the retraction sends `(t, x)` to that exit
point.

This is the basic example of a closed cofibration.  It is the geometric input for the homotopy
extension property of the inclusion of a skeleton of a CW complex into the next one, whose cells
are attached along maps defined on such spheres.

As a consequence, a map out of the unit sphere is null-homotopic exactly when it extends over the
closed unit ball: a null-homotopy is extended from the sphere to the ball, starting at a constant
map, and conversely the closed ball is contractible.  This is the criterion for extending a map
over a cell attached along a sphere.

## Main declarations

* `TauCeti.hasHomotopyExtensionProperty_sphere_closedBall`: **the unit sphere has the homotopy
  extension property inside the closed unit ball.**
* `ContinuousMap.nullhomotopic_iff_exists_extension_closedBall`: a map out of the unit sphere is
  null-homotopic exactly when it extends over the closed unit ball.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Chapter 0, proof of Proposition 0.16, which retracts `Dⁿ × I` onto `Dⁿ × {0} ∪ ∂Dⁿ × I` by
  radial projection from the point `(0, 2)`.
-/

public section

noncomputable section

namespace TauCeti

open Metric Set unitInterval

universe u

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]

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
private lemma ballRadialProjection_max_norm_ne_zero (p : I × closedBall (0 : E) 1) :
    max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ ≠ 0 :=
  ne_of_gt (lt_of_lt_of_le (by norm_num) (le_max_right _ _))

omit [NormedSpace ℝ E] in
private lemma ballRadialProjection_two_sub_ne_zero (p : I × closedBall (0 : E) 1) :
    (2 : ℝ) - (p.1 : ℝ) ≠ 0 :=
  ne_of_gt (by have := p.1.2.2; linarith)

private lemma continuous_ballRadialProjection : Continuous (ballRadialProjection (E := E)) := by
  have hvec : Continuous fun p : I × closedBall (0 : E) 1 => ((p.2 : E)) := by fun_prop
  have hmax : Continuous fun p : I × closedBall (0 : E) 1 => max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ := by
    fun_prop
  refine Continuous.if_le ?_ ?_ (by fun_prop) (by fun_prop) ?_
  · exact continuous_const.prodMk
      ((continuous_const.div (by fun_prop) ballRadialProjection_two_sub_ne_zero).smul hvec)
  · exact ((by fun_prop : Continuous fun p : I × closedBall (0 : E) 1 =>
        2 * max ‖(p.2 : E)‖ (2 : ℝ)⁻¹ + (p.1 : ℝ) - 2).div hmax
          ballRadialProjection_max_norm_ne_zero).prodMk
      ((hmax.inv₀ ballRadialProjection_max_norm_ne_zero).smul hvec)
  · rintro p hp
    -- On the seam the truncation is inactive and both branches are the exit point through the
    -- rim of the cylinder.
    have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
    have hn : (2 : ℝ)⁻¹ ≤ ‖(p.2 : E)‖ := by rw [hp] at ht1; linarith
    have hnpos : ‖(p.2 : E)‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hn)
    rw [max_eq_left hn, hp]
    refine Prod.ext ?_ (congrArg (· • (p.2 : E)) ?_)
    · field_simp
      ring
    · field_simp
      rw [sub_sub_cancel, div_self hnpos]

/-- The radial projection lands in the cylinder, and in the union of its bottom face with the
part of the cylinder lying over the sphere. -/
private lemma ballRadialProjection_spec (p : I × closedBall (0 : E) 1) :
    (ballRadialProjection p).1 ∈ I ∧ (ballRadialProjection p).2 ∈ closedBall (0 : E) 1 ∧
      ((ballRadialProjection p).1 = 0 ∨ (ballRadialProjection p).2 ∈ sphere (0 : E) 1) := by
  have ht1 : (p.1 : ℝ) ≤ 1 := p.1.2.2
  have hn1 : ‖(p.2 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 p.2.2
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
      simp [norm_smul, ne_of_gt hnpos]
    rw [max_eq_left hn.le]
    refine ⟨?_, ?_, Or.inr ?_⟩
    · rw [Set.mem_Icc]
      exact ⟨div_nonneg (by linarith) hnpos.le, by rw [div_le_one hnpos]; linarith⟩
    · rw [mem_closedBall_zero_iff, hunit]
    · rw [mem_sphere_zero_iff_norm, hunit]

/-- The radial projection fixes the bottom face of the cylinder and the part of the cylinder
lying over the sphere. -/
private lemma ballRadialProjection_eq_self (p : I × closedBall (0 : E) 1)
    (hp : p ∈ cylinderExtensionDomain (Subtype.val ⁻¹' sphere (0 : E) 1)) :
    ballRadialProjection p = ((p.1 : ℝ), (p.2 : E)) := by
  have ht0 : (0 : ℝ) ≤ (p.1 : ℝ) := p.1.2.1
  rw [mem_cylinderExtensionDomain_iff] at hp
  by_cases ht : (p.1 : ℝ) ≤ 2 - 2 * ‖(p.2 : E)‖
  · -- The first branch applies, and the point lies on the bottom face of the cylinder.
    have hzero : (p.1 : ℝ) = 0 := by
      obtain h0 | hs := hp
      · exact congrArg Subtype.val h0
      · rw [mem_sphere_zero_iff_norm.1 hs] at ht
        linarith
    rw [ballRadialProjection, ite_eq_left ht, hzero]
    norm_num
  · -- The second branch applies, and the point lies over the sphere.
    have hn : ‖(p.2 : E)‖ = 1 := by
      obtain h0 | hs := hp
      · have hz : (p.1 : ℝ) = 0 := congrArg Subtype.val h0
        have hb : ‖(p.2 : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 p.2.2
        exact absurd (by rw [hz]; linarith) ht
      · exact mem_sphere_zero_iff_norm.1 hs
    rw [ballRadialProjection, ite_eq_right ht, hn, max_eq_left (by norm_num : (2 : ℝ)⁻¹ ≤ 1)]
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

/-- The retraction read off in the ambient coordinates of the cylinder. -/
private lemma ballCylinderRetraction_apply (p : I × closedBall (0 : E) 1) :
    ballCylinderRetraction p =
      (⟨(ballRadialProjection p).1, (ballRadialProjection_spec p).1⟩,
        ⟨(ballRadialProjection p).2, (ballRadialProjection_spec p).2.1⟩) := rfl

/-- **The unit sphere of a real seminormed space has the homotopy extension property inside the
closed unit ball**: the inclusion of the unit sphere is a closed cofibration. -/
theorem hasHomotopyExtensionProperty_sphere_closedBall :
    HasHomotopyExtensionProperty
      (Subtype.val ⁻¹' sphere (0 : E) 1 : Set (closedBall (0 : E) 1)) := by
  refine hasHomotopyExtensionProperty_of_retraction
    (isClosed_sphere.preimage continuous_subtype_val) (r := ballCylinderRetraction)
    (fun p => ?_) (fun p hp => ?_)
  · rw [mem_cylinderExtensionDomain_iff, ballCylinderRetraction_apply]
    obtain h0 | hs := (ballRadialProjection_spec p).2.2
    · exact Or.inl (Subtype.ext h0)
    · exact Or.inr hs
  · have h := ballRadialProjection_eq_self p hp
    rw [ballCylinderRetraction_apply]
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))

end TauCeti

namespace ContinuousMap

open Metric unitInterval

variable {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E] {Y : Type*} [TopologicalSpace Y]

/-- **A map out of the unit sphere is null-homotopic exactly when it extends over the closed unit
ball.** -/
theorem nullhomotopic_iff_exists_extension_closedBall (g : C(sphere (0 : E) 1, Y)) :
    g.Nullhomotopic ↔ ∃ G : C(closedBall (0 : E) 1, Y),
      ∀ y : sphere (0 : E) 1, G ⟨y, sphere_subset_closedBall y.2⟩ = g y := by
  constructor
  · -- Extend a homotopy from a constant map to `g` over the closed ball, starting at the constant
    -- map, and take its final stage.
    rintro ⟨c, hc⟩
    let H := hc.some.symm
    obtain ⟨K, -, hK⟩ :=
      TauCeti.hasHomotopyExtensionProperty_sphere_closedBall.exists_extension_of_isClosed
        (isClosed_sphere.preimage continuous_subtype_val) (ContinuousMap.const _ c)
        (H.toContinuousMap.comp ⟨fun p : I × (Subtype.val ⁻¹' sphere (0 : E) 1 :
          Set (closedBall (0 : E) 1)) ↦ (p.1, (⟨p.2.1.1, p.2.2⟩ : sphere (0 : E) 1)), by fun_prop⟩)
        fun a ↦ H.apply_zero _
    exact ⟨⟨fun x ↦ K (1, x), by fun_prop⟩, fun y ↦
      (hK 1 ⟨⟨y, sphere_subset_closedBall y.2⟩, y.2⟩).trans (H.apply_one y)⟩
  · -- The closed ball is contractible, so every map out of it is null-homotopic.
    rintro ⟨G, hG⟩
    have : ContractibleSpace (closedBall (0 : E) 1) :=
      (convex_closedBall 0 1).contractibleSpace ⟨0, mem_closedBall_self zero_le_one⟩
    let ι : C(sphere (0 : E) 1, closedBall (0 : E) 1) :=
      ⟨fun y ↦ ⟨y, sphere_subset_closedBall y.2⟩, by fun_prop⟩
    have hg : g = (G.comp (ContinuousMap.id _)).comp ι := by
      ext y
      exact (hG y).symm
    rw [hg]
    exact ((id_nullhomotopic _).comp_right G).comp_left ι

end ContinuousMap
