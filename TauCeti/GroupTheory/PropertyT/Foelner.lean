/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Foelner

/-!
# Følner sets obstruct property (T) for infinite groups

For an infinite group with Følner sets, the counting-measure regular representation has
almost invariant unit vectors but no nonzero invariant vector. Hence the group does not
have property (T), with Hilbert spaces quantified in the universe of the group.

The reference is Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory

namespace Subgroup

universe u

/-- An infinite group with Følner sets does not have property (T), with Hilbert spaces
quantified in the universe of the group. -/
theorem not_relativePropertyT_top_of_hasFoelnerSets {G : Type u} [Group G] [Infinite G]
    (hG : TauCeti.HasFoelnerSets G) : ¬ (⊤ : Subgroup G).RelativePropertyT.{u} := by
  classical
  let : MeasurableSpace G := ⊤
  let ρ := (Measure.count : Measure G).leftRegular ℂ ℂ 2
  intro hT
  rw [relativePropertyT_def] at hT
  obtain ⟨v, hv, hfixed⟩ := hT (Lp ℂ 2 (Measure.count : Measure G)) ρ
    (Measure.isUnitary_leftRegular Measure.count)
    (Measure.hasAlmostInvariantVectors_count_leftRegular hG)
  have hmem : v ∈ ρ.invariants := fun g ↦ hfixed ⟨g, mem_top _⟩
  have hinv : ρ.invariants = ⊥ := Measure.invariants_count_leftRegular (by simp)
  exact hv (by simpa [hinv] using hmem)

end Subgroup
