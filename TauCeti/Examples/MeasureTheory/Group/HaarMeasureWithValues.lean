/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Group.HaarMeasureWithValues.Basic
import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.UnitProOrder

/-!
# Examples of Haar measures with values in a ring

* On a discrete group, the measure normalised on the trivial subgroup counts the points of a
  finite set, over every semiring.
* No Haar measure on `ℤ_p` with values in `𝔽_p` gives `ℤ_p` volume `1`.
* The unnormalised zero measure is allowed, and none of its volumes is a unit over a nonzero
  semiring.
-/

open TopologicalSpace

namespace TauCeti.HaarMeasureWithValues

/-! ### Counting volume on a discrete group -/

section Discrete

variable {G : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G] [IsTopologicalGroup G]

example (A : Type*) [Semiring A] (K : CompactOpens G) :
    normalized A ⟨⊥, isOpen_discrete _⟩ (Set.finite_singleton 1).isCompact
      (by
        have : Subsingleton (⟨⊥, isOpen_discrete _⟩ : OpenSubgroup G) :=
          ⟨fun a b ↦ Subtype.ext
            ((Subgroup.mem_bot.1 a.property).trans (Subgroup.mem_bot.1 b.property).symm)⟩
        exact hasUnitProOrder_of_subsingleton) K = (K : Set G).ncard := by
  rw [normalized_apply _ _ K le_rfl fun k hk w hw ↦ by
      rwa [(Subgroup.mem_bot.1 hw : w = 1), mul_one]]
  have hinj : Function.Injective ((↑) : G → G ⧸ (⊥ : Subgroup G)) := fun a b hab ↦ by
    simpa [inv_mul_eq_one] using QuotientGroup.eq.1 hab
  simp [Set.ncard_image_of_injective _ hinj, Subgroup.relIndex_self]

end Discrete

/-! ### No `𝔽_p`-valued Haar measure of total volume `1` on `ℤ_p` -/

example (p : ℕ) [Fact p.Prime] (μ : HaarMeasureWithValues (ZMod p) (Multiplicative ℤ_[p])) :
    μ ((⊤ : OpenSubgroup (Multiplicative ℤ_[p])).toCompactOpens isCompact_univ) ≠ 1 := fun h1 ↦
  not_hasUnitProOrder_zmod_multiplicative_padicInt p <| hasUnitProOrder_top_iff.1 <|
    μ.hasUnitProOrder_of_isUnit ⊤ isCompact_univ (h1 ▸ isUnit_one)

/-! ### The zero measure -/

example (A : Type*) [Semiring A] [Nontrivial A] (G : Type*) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : CompactOpens G) :
    ¬ IsUnit ((0 : HaarMeasureWithValues A G) K) := by
  simp

end TauCeti.HaarMeasureWithValues
