/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# Descent of heights from the polar cover

A height descends uniquely to the projected domain if and only if all its deck separations
vanish on their overlaps. On a translation-invariant domain it suffices to check one turn.
-/

public noncomputable section

namespace TauCeti.PolarGraph

/-- A polar height factors through the projection on its domain precisely when
all deck translates in the domain have zero height difference. -/
theorem exists_height_iff_separation_eq_zero (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    (∃ v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω) ↔
      ∀ k : ℤ, ∀ p ∈ overlap Ω k, separation u k p = 0 := by
  constructor
  · rintro ⟨v, hv⟩ k p h
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
    exact (Function.factorsThrough_iff _).mp hf

/-- A descended polar height is unique on the projected domain. -/
theorem existsUnique_height_iff_separation_eq_zero (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    (∃! v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω) ↔
      ∀ k : ℤ, ∀ p ∈ overlap Ω k, separation u k p = 0 := by
  constructor
  · intro h
    exact (exists_height_iff_separation_eq_zero u Ω).mp h.exists
  · intro h
    obtain ⟨v, hv⟩ := (exists_height_iff_separation_eq_zero u Ω).mpr h
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

end TauCeti.PolarGraph
