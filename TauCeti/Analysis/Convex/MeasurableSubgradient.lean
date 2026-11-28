/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SubgradientImage
import TauCeti.MeasureTheory.MeasurableSpace.Selection

/-!
# Borel measurable subgradient selections

Every real function convex on an open subset `Ω` of a finite-dimensional real inner product space
admits a Borel measurable selection of subgradients relative to `Ω`
(`ConvexOn.exists_measurable_forall_add_inner_le`), obtained via the closed-graph measurable
selection theorem (`IsClosed.exists_measurable_forall_mem`). We also record a piecewise measurable
selection helper for the maximum of two measurable functions
(`TauCeti.exists_measurable_piecewise_subgradient_max`).
-/

public section

namespace TauCeti

open Set

/-- **Borel measurable subgradient selection.** Every real function `u` convex on an open subset `Ω`
of a finite-dimensional real inner product space admits a Borel measurable map `T : E → E` such that
`T x` is a subgradient of `u` relative to `Ω` at every `x ∈ Ω`. -/
theorem _root_.ConvexOn.exists_measurable_forall_add_inner_le {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    {Ω : Set E} {u : E → ℝ} (hΩ : IsOpen Ω) (hu : ConvexOn ℝ Ω u) :
    ∃ T : E → E, Measurable T ∧ ∀ x ∈ Ω, ∀ y ∈ Ω, u x + inner ℝ (y - x) (T x) ≤ u y := by
  classical
  let M : ↥Ω → Set E := fun x => {p : E | ∀ y ∈ Ω, u x + inner ℝ (y - x) p ≤ u y}
  have hclosed : IsClosed {q : ↥Ω × E | q.2 ∈ M q.1} := by
    have hEq : {q : ↥Ω × E | q.2 ∈ M q.1} =
        ⋂ y ∈ Ω, {q : ↥Ω × E | u q.1 + inner ℝ (y - q.1) q.2 ≤ u y} := by
      ext q
      simp [M]
    rw [hEq]
    exact isClosed_iInter fun y => isClosed_iInter fun _ =>
      isClosed_le (((hu.continuousOn hΩ).domRestrict.comp continuous_fst).add
        ((continuous_const.sub (continuous_subtypeVal.comp continuous_fst)).inner continuous_snd))
        continuous_const
  obtain ⟨S, hSm, hS⟩ := hclosed.exists_measurable_forall_mem
    fun x => hu.exists_forall_add_inner_le hΩ x.property
  refine ⟨fun x => if hx : x ∈ Ω then S ⟨x, hx⟩ else 0,
    hSm.dite measurable_const hΩ.measurableSet, fun x hx y hy => by
      simpa only [dite_eq_left hx] using hS ⟨x, hx⟩ y hy⟩

/-- **Piecewise measurable subgradient selection for a maximum of two functions.** Given two
measurable functions `u₁, u₂ : E → ℝ` and measurable maps `b₁, b₂ : E → E` that supply
subgradients of `max (u₁ ·) (u₂ ·)` wherever `u₂ ≤ u₁` (resp. `u₁ ≤ u₂`), there exist two
measurable subgradient selections `T₁, T₂` everywhere that coincide with `b₁` and `b₂` on the
tie locus `{x | u₁ x = u₂ x}`. -/
theorem exists_measurable_piecewise_subgradient_max {E : Type*} [SeminormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E]
    {u₁ u₂ : E → ℝ} {b₁ b₂ : E → E}
    (hu₁ : Measurable u₁) (hu₂ : Measurable u₂) (hb₁ : Measurable b₁) (hb₂ : Measurable b₂)
    (h₁ : ∀ x z, u₂ x ≤ u₁ x → max (u₁ x) (u₂ x) + inner ℝ (z - x) (b₁ x) ≤ max (u₁ z) (u₂ z))
    (h₂ : ∀ x z, u₁ x ≤ u₂ x → max (u₁ x) (u₂ x) + inner ℝ (z - x) (b₂ x) ≤ max (u₁ z) (u₂ z)) :
    ∃ T₁ T₂ : E → E, Measurable T₁ ∧ Measurable T₂ ∧
      (∀ x z, max (u₁ x) (u₂ x) + inner ℝ (z - x) (T₁ x) ≤ max (u₁ z) (u₂ z)) ∧
      (∀ x z, max (u₁ x) (u₂ x) + inner ℝ (z - x) (T₂ x) ≤ max (u₁ z) (u₂ z)) ∧
      (∀ x, u₁ x = u₂ x → T₁ x = b₁ x ∧ T₂ x = b₂ x) := by
  classical
  exact ⟨fun x => if u₂ x ≤ u₁ x then b₁ x else b₂ x, fun x => if u₁ x ≤ u₂ x then b₂ x else b₁ x,
    Measurable.ite (measurableSet_le hu₂ hu₁) hb₁ hb₂,
    Measurable.ite (measurableSet_le hu₁ hu₂) hb₂ hb₁,
    fun x z => by dsimp only; split_ifs with hx; exacts [h₁ x z hx, h₂ x z (le_of_not_ge hx)],
    fun x z => by dsimp only; split_ifs with hx; exacts [h₂ x z hx, h₁ x z (le_of_not_ge hx)],
    fun x heq => by simp [heq]⟩

end TauCeti
