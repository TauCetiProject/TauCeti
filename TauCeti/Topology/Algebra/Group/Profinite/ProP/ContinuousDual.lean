/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous characters and the pro-`p` Frattini subgroup

A continuous character to the additive group of `ZMod p` is either trivial or has kernel of
index `p`. Thus every continuous character of a profinite group factors through its Frattini
quotient. This is the character-theoretic input to describing the generator rank of a pro-`p`
group by its continuous `𝔽_p`-valued characters. The finite target is given its discrete
topology.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable [TopologicalSpace (Multiplicative (ZMod p))]
  [DiscreteTopology (Multiplicative (ZMod p))]
variable {G : Type u} [Group G] [TopologicalSpace G]

local instance : Fact (Nat.card (Multiplicative (ZMod p))).Prime := ⟨by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod p]
  exact Fact.out⟩

/-- The pro-`p` Frattini subgroup lies in the kernel of every continuous character to
`𝔽_p`. Equivalently, such a character descends to the Frattini quotient. -/
theorem _root_.ContinuousMonoidHom.proPFrattini_le_ker
    (f : G →ₜ* Multiplicative (ZMod p)) : proPFrattini p G ≤ f.ker := by
  by_cases hf : ∀ x, f x = 1
  · intro x hx
    -- Membership in the kernel is the equation defining the kernel subgroup.
    change f x = 1
    exact hf x
  · push Not at hf
    have hrange : f.toMonoidHom.range = ⊤ := by
      rcases (f.toMonoidHom.range).eq_bot_or_eq_top_of_prime_card with hbot | htop
      · obtain ⟨x, hx⟩ := hf
        rw [MonoidHom.range_eq_bot_iff] at hbot
        have hfx : f x = 1 := by
          simpa using congrArg (fun k : G →* Multiplicative (ZMod p) => k x) hbot
        exact (hx hfx).elim
      · exact htop
    have hopen : IsOpen (f.ker : Set G) := by
      -- The kernel is the preimage of the identity in the discrete target.
      change IsOpen (f ⁻¹' ({1} : Set (Multiplicative (ZMod p))))
      exact (isOpen_discrete {1}).preimage f.continuous
    let U : OpenNormalSubgroup G :=
      { toOpenSubgroup := ⟨f.ker, hopen⟩
        isNormal' := inferInstance }
    have hindex : U.toSubgroup.index = p := by
      -- Unfolding this local open normal subgroup exposes the homomorphism kernel.
      change f.toMonoidHom.ker.index = p
      rw [Subgroup.index_ker, hrange]
      simp
    exact proPFrattini_le hindex

/-- Every continuous character to `𝔽_p` factors uniquely through the pro-`p` Frattini
quotient. -/
theorem _root_.ContinuousMonoidHom.existsUnique_frattiniQuotient_lift
    [IsTopologicalGroup G] (f : G →ₜ* Multiplicative (ZMod p)) :
    ∃! g : (G ⧸ proPFrattini p G) →ₜ* Multiplicative (ZMod p),
      g.toMonoidHom.comp (QuotientGroup.mk' (proPFrattini p G)) = f.toMonoidHom := by
  have hker := ContinuousMonoidHom.proPFrattini_le_ker f
  let g₀ := QuotientGroup.lift (proPFrattini p G) f.toMonoidHom hker
  have hcomp : g₀.comp (QuotientGroup.mk' (proPFrattini p G)) = f.toMonoidHom :=
    QuotientGroup.lift_comp_mk' _ _ _
  have hcontinuous : Continuous g₀ := by
    apply QuotientGroup.isOpenQuotientMap_mk.continuous_comp_iff.mp
    -- The quotient lift composes back to `f` along the quotient map.
    change Continuous (fun x : G ↦
      QuotientGroup.lift (proPFrattini p G) f.toMonoidHom hker (QuotientGroup.mk x))
    simp only [QuotientGroup.lift_mk']
    exact f.continuous
  let g : (G ⧸ proPFrattini p G) →ₜ* Multiplicative (ZMod p) := ⟨g₀, hcontinuous⟩
  refine ⟨g, hcomp, ?_⟩
  intro g' hg'
  apply ContinuousMonoidHom.toMonoidHom_injective
  apply QuotientGroup.monoidHom_ext
  exact hg'.trans hcomp.symm

end TauCeti
