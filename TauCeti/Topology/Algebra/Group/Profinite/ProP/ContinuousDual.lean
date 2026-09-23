/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
public import TauCeti.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous characters and the pro-`p` Frattini subgroup

A continuous homomorphism to a discrete group of cardinality `p` is either trivial or has kernel
of index `p`. Thus every continuous character into the multiplicative encoding
`Multiplicative (ZMod p)` of `𝔽_p` factors through the pro-`p` Frattini quotient. This is the
character-theoretic input to describing the generator rank of a pro-`p` group by its continuous
`𝔽_p`-valued characters. The lift uses the quotient topology.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime]
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The pro-`p` Frattini subgroup lies in the kernel of every continuous homomorphism to a
discrete group of cardinality `p`. -/
theorem proPFrattini_le_ker {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    proPFrattini p G ≤ f.ker := by
  by_cases hf : ∀ x, f x = 1
  · intro x hx
    exact MonoidHom.mem_ker.mpr (hf x)
  · have hrange : f.toMonoidHom.range = ⊤ := by
      rcases (f.toMonoidHom.range).eq_bot_or_eq_top_of_prime_card
          (hp := ⟨hH ▸ Fact.out⟩) with hbot | htop
      · rw [MonoidHom.range_eq_bot_iff] at hbot
        exact (hf fun x => by simpa using DFunLike.congr_fun hbot x).elim
      · exact htop
    have hopen : IsOpen (f.ker : Set G) := by
      rw [MonoidHom.coe_ker]
      exact (isOpen_discrete {1}).preimage f.continuous
    have hindex : f.toMonoidHom.ker.index = p := by
      rw [Subgroup.index_ker, hrange]
      simp [hH]
    exact proPFrattini_le (U := ⟨⟨f.ker, hopen⟩, inferInstance⟩) hindex

/-- Precomposition with the Frattini quotient projection identifies continuous homomorphisms
from the quotient with continuous homomorphisms from `G` for a discrete target of cardinality
`p`. -/
def frattiniQuotientHomEquiv {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) :
    ((G ⧸ proPFrattini p G) →ₜ* H) ≃ (G →ₜ* H) :=
  (ContinuousMonoidHom.quotientHomEquiv (proPFrattini p G)).trans
    (Equiv.subtypeUnivEquiv fun f => proPFrattini_le_ker hH f)

/-- Evaluation of precomposition with the Frattini quotient projection. -/
@[simp]
theorem frattiniQuotientHomEquiv_apply {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p)
    (g : (G ⧸ proPFrattini p G) →ₜ* H) :
    frattiniQuotientHomEquiv hH g =
      g.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G)) := by
  dsimp [frattiniQuotientHomEquiv]
  exact ContinuousMonoidHom.quotientHomEquiv_apply_coe _ _

/-- Evaluation of the inverse Frattini quotient homomorphism equivalence. -/
@[simp]
theorem frattiniQuotientHomEquiv_symm_apply {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p)
    (f : G →ₜ* H) :
    (frattiniQuotientHomEquiv hH).symm f =
      ContinuousMonoidHom.quotientLift (proPFrattini p G) f
        (proPFrattini_le_ker hH f) := by
  dsimp [frattiniQuotientHomEquiv]
  exact ContinuousMonoidHom.quotientHomEquiv_symm_apply _ _

/-- Continuous homomorphisms to a discrete group of cardinality `p` factor uniquely through the
pro-`p` Frattini quotient. -/
theorem existsUnique_frattiniQuotient_lift {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    ∃! g : (G ⧸ proPFrattini p G) →ₜ* H,
      g.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G)) = f := by
  simpa only [frattiniQuotientHomEquiv_apply] using
    (frattiniQuotientHomEquiv hH).bijective.existsUnique f

end TauCeti
