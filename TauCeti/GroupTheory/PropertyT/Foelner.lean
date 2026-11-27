/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.PropertyT.Basic
public import TauCeti.RepresentationTheory.Continuous.LeftRegular.Foelner

/-!
# Følner sets obstruct relative property (T) for infinite subgroups

For a group with Følner sets, the counting-measure regular representation has almost invariant unit
vectors, whereas its restriction to any infinite subgroup has no nonzero invariant vector. Hence no
infinite subgroup has relative property (T), and in particular an infinite group with Følner sets
does not have property (T), with Hilbert spaces quantified in the universe of the group.

The reference is Bekka–de la Harpe–Valette, *Kazhdan's Property (T)*, Appendix G.5.

## Main results

* `Subgroup.not_relativePropertyT_of_hasFoelnerSets`: in a group with Følner sets, no infinite
  subgroup has relative property (T) in the group's universe.
* `Subgroup.not_relativePropertyT_top_of_hasFoelnerSets`: an infinite group with Følner sets does
  not have property (T) in its universe.
-/

public section

open MeasureTheory

namespace Subgroup

universe u

/-- In a group with Følner sets, no infinite subgroup has relative property (T), with Hilbert
spaces quantified in the universe of the group. -/
theorem not_relativePropertyT_of_hasFoelnerSets {G : Type u} [Group G]
    (hG : TauCeti.HasFoelnerSets G) {Λ : Subgroup G} [Infinite Λ] :
    ¬ Λ.RelativePropertyT.{u} := by
  classical
  let : MeasurableSpace G := ⊤
  let ρ := (Measure.count : Measure G).leftRegular ℂ ℂ 2
  intro hT
  rw [relativePropertyT_def] at hT
  obtain ⟨v, hv, hfixed⟩ := hT (Lp ℂ 2 (Measure.count : Measure G)) ρ
    (Measure.isUnitary_leftRegular Measure.count)
    (Measure.hasAlmostInvariantVectors_count_leftRegular hG)
  have hinv : (ρ.restrict Λ.subtype).invariants = ⊥ :=
    Measure.invariants_restrict_count_leftRegular Λ.subtype_injective (by simp)
  exact hv (by simpa [hinv] using hfixed)

/-- An infinite group with Følner sets does not have property (T), with Hilbert spaces
quantified in the universe of the group. -/
theorem not_relativePropertyT_top_of_hasFoelnerSets {G : Type u} [Group G] [Infinite G]
    (hG : TauCeti.HasFoelnerSets G) : ¬ (⊤ : Subgroup G).RelativePropertyT.{u} :=
  have : Infinite (⊤ : Subgroup G) := Infinite.of_injective _ (topEquiv (G := G)).symm.injective
  not_relativePropertyT_of_hasFoelnerSets hG

end Subgroup
