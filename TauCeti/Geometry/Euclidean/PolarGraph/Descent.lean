/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Arcosh
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# Descent of heights from the polar cover

A height descends uniquely to the projected domain if and only if all its deck separations
vanish on their overlaps. On a translation-invariant domain it suffices to check one turn.
Radial heights descend explicitly by taking the Euclidean norm, as for the half-catenoid.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- A polar height factors uniquely through the projection on its domain precisely when
all deck translates in the domain have zero height difference. -/
theorem existsUnique_height_iff_separation_eq_zero (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    (∃! v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω) ↔
      ∀ k : ℤ, ∀ p ∈ overlap Ω k, separation u k p = 0 := by
  constructor
  · rintro ⟨v, hv, _⟩ k p h
    obtain ⟨hp, hkp⟩ := mem_overlap_iff.mp h
    rw [separation_def, sub_eq_zero]
    have he : Set.imageFactorization projection Ω ⟨deckShift k p, hkp⟩ =
        Set.imageFactorization projection Ω ⟨p, hp⟩ := Subtype.ext (projection_deckShift k p)
    exact (congrFun hv ⟨_, hkp⟩).trans ((congrArg v he).trans (congrFun hv ⟨p, hp⟩).symm)
  · intro h
    have hf : (fun p : Ω ↦ u p).FactorsThrough (Set.imageFactorization projection Ω) := by
      intro p q hpq
      obtain ⟨k, hk⟩ := (projection_eq_iff p q).mp (congrArg Subtype.val hpq)
      have hz := h k p (mem_overlap_iff.mpr ⟨p.property, hk ▸ q.property⟩)
      rw [separation_def, ← hk, sub_eq_zero] at hz
      exact hz.symm
    obtain ⟨v, hv⟩ := (Function.factorsThrough_iff _).mp hf
    exact ⟨v, hv, fun w hw ↦ Set.imageFactorization_surjective.injective_comp_right
      (hw.symm.trans hv)⟩

/-- On a deck-invariant domain, agreement across a single turn already gives descent. -/
theorem existsUnique_height_of_separation_one_eq_zero {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hΩ : ∀ k : ℤ, Set.MapsTo (deckShift k) Ω Ω)
    (hu : ∀ p ∈ overlap Ω 1, separation u 1 p = 0) :
    ∃! v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω := by
  apply (existsUnique_height_iff_separation_eq_zero u Ω).mpr
  intro k p hp
  apply separation_eq_zero_of_deckShift_one_deckShift_eq
  intro m
  have hm := hΩ m (mem_overlap_iff.mp hp).1
  simpa only [separation_def, sub_eq_zero] using hu _ (mem_overlap_iff.mpr ⟨hm, hΩ 1 hm⟩)

/-- The image of a radial domain consists of points with the prescribed radii, excluding zero. -/
theorem image_projection_radius_preimage (s : Set ℝ) :
    projection '' (radius ⁻¹' s) = {z : ℂ | ‖z‖ ∈ s ∧ z ≠ 0} := by
  ext z
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨by simpa using hp, projection_ne_zero p⟩
  · rintro ⟨hs, hz⟩
    refine ⟨⟨(‖z‖, z.arg), norm_pos_iff.mpr hz⟩, ?_, ?_⟩
    · simpa only [Set.mem_preimage, radius_mk] using hs
    · simpa only [projection_def, radius_mk, angle_mk, Circle.coe_exp] using
        Complex.norm_mul_exp_arg_mul_I z

/-- The upper half-catenoid descends to the exterior of the closed unit disk with height
`arcosh ‖z‖`. -/
theorem halfCatenoid_height_descends :
    projection '' (radius ⁻¹' Set.Ioi 1) = {z : ℂ | 1 < ‖z‖} ∧
      (fun p ↦ Real.arcosh (radius p)) = (fun z : ℂ ↦ Real.arcosh ‖z‖) ∘ projection := by
  constructor
  · rw [image_projection_radius_preimage]
    ext z
    exact ⟨And.left, fun h ↦ ⟨h, norm_pos_iff.mp (lt_trans zero_lt_one h)⟩⟩
  · funext p
    simp

end TauCeti.PolarGraph
