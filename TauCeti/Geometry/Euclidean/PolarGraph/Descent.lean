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
theorem exists_descended_height_iff_separation_eq_zero (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    (∃ v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω) ↔
      ∀ k : ℤ, ∀ p ∈ overlap Ω k, separation u k p = 0 := by
  rw [← Function.factorsThrough_iff]
  have hprojection (p : Ω) :=
    congrFun (Set.imageFactorization_eq (f := projection) (s := Ω)) p
  simp only [Function.comp_apply] at hprojection
  constructor
  · intro h k p hp
    obtain ⟨hp, hkp⟩ := mem_overlap_iff.mp hp
    rw [separation_def, sub_eq_zero]
    apply h (a := ⟨deckShift k p, hkp⟩) (b := ⟨p, hp⟩)
    apply Subtype.ext
    simpa only [hprojection] using projection_deckShift k p
  · intro h p q hpq
    have he : projection p = projection q := by
      simpa only [hprojection] using congrArg Subtype.val hpq
    obtain ⟨k, hk⟩ := (projection_eq_iff p q).mp he
    have hz := h k p (mem_overlap_iff.mpr ⟨p.property, hk ▸ q.property⟩)
    rw [separation_def, ← hk, sub_eq_zero] at hz
    exact hz.symm

/-- A unique height on the projected domain pulls back to the original polar height
exactly when every deck separation vanishes on its overlap. -/
theorem existsUnique_descended_height_iff_separation_eq_zero
    (u : PolarPoint → ℝ) (Ω : Set PolarPoint) :
    (∃! v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω) ↔
      ∀ k : ℤ, ∀ p ∈ overlap Ω k, separation u k p = 0 := by
  constructor
  · intro h
    exact (exists_descended_height_iff_separation_eq_zero u Ω).mp h.exists
  · intro h
    obtain ⟨v, hv⟩ := (exists_descended_height_iff_separation_eq_zero u Ω).mpr h
    exact ⟨v, hv, fun w hw ↦ Set.imageFactorization_surjective.injective_comp_right
      (hw.symm.trans hv)⟩

/-- On a deck-invariant domain, agreement across a single turn already gives descent. -/
theorem existsUnique_descended_height_of_separation_one_eq_zero
    {u : PolarPoint → ℝ} {Ω : Set PolarPoint}
    (hΩ : ∀ k : ℤ, Set.MapsTo (deckShift k) Ω Ω)
    (hu : ∀ p ∈ overlap Ω 1, separation u 1 p = 0) :
    ∃! v : projection '' Ω → ℝ, (fun p : Ω ↦ u p) = v ∘ Set.imageFactorization projection Ω := by
  apply (existsUnique_descended_height_iff_separation_eq_zero u Ω).mpr
  intro k p hp
  apply separation_eq_zero_of_deckShift_one_deckShift_eq
  intro m
  have hm := hΩ m (mem_overlap_iff.mp hp).1
  simpa only [separation_def, sub_eq_zero] using hu _ (mem_overlap_iff.mpr ⟨hm, hΩ 1 hm⟩)

end TauCeti.PolarGraph
