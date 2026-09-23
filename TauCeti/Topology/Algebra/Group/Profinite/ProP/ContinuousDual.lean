/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Frattini
public import TauCeti.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Instances.ZMod
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Continuous characters and the pro-`p` Frattini subgroup

A continuous homomorphism to a discrete group of cardinality `p` is either trivial or has kernel
of index `p`. Thus every continuous character to `𝔽_p` factors through the pro-`p` Frattini
quotient. This is the character-theoretic input to describing the generator rank of a pro-`p`
group by its continuous `𝔽_p`-valued characters. The lift uses the quotient topology.

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
theorem _root_.ContinuousMonoidHom.proPFrattini_le_ker {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    proPFrattini p G ≤ f.ker := by
  by_cases hf : ∀ x, f x = 1
  · intro x hx
    exact MonoidHom.mem_ker.mpr (hf x)
  · push Not at hf
    have hrange : f.toMonoidHom.range = ⊤ := by
      rcases (f.toMonoidHom.range).eq_bot_or_eq_top_of_prime_card
          (hp := ⟨hH ▸ Fact.out⟩) with hbot | htop
      · obtain ⟨x, hx⟩ := hf
        rw [MonoidHom.range_eq_bot_iff] at hbot
        have hfx : f x = 1 := by
          simpa using congrArg (fun k : G →* H => k x) hbot
        exact (hx hfx).elim
      · exact htop
    have hopen : IsOpen (f.ker : Set G) := by
      rw [MonoidHom.coe_ker]
      exact (isOpen_discrete {1}).preimage f.continuous
    have hindex : f.toMonoidHom.ker.index = p := by
      rw [Subgroup.index_ker, hrange]
      simp [hH]
    exact proPFrattini_le (U := ⟨⟨f.ker, hopen⟩, inferInstance⟩) hindex

/-- The continuous homomorphism induced on the pro-`p` Frattini quotient by a continuous
homomorphism to a discrete group of cardinality `p`. -/
def _root_.ContinuousMonoidHom.frattiniQuotientLift {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    (G ⧸ proPFrattini p G) →ₜ* H := by
  have hker := ContinuousMonoidHom.proPFrattini_le_ker hH f
  let g₀ := QuotientGroup.lift (proPFrattini p G) f.toMonoidHom hker
  have hcomp : ⇑g₀ ∘ QuotientGroup.mk = f := by
    funext x
    exact QuotientGroup.lift_mk' _ _ _
  exact ⟨g₀, (QuotientGroup.isQuotientMap_mk (proPFrattini p G)).continuous_iff.mpr
    (hcomp ▸ f.continuous)⟩

/-- Evaluation of the induced homomorphism on a class represented by `x`. -/
@[simp]
theorem _root_.ContinuousMonoidHom.frattiniQuotientLift_mk {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) (x : G) :
    ContinuousMonoidHom.frattiniQuotientLift hH f (x : G ⧸ proPFrattini p G) = f x :=
  QuotientGroup.lift_mk' (N := proPFrattini p G) (φ := f.toMonoidHom)
    (HN := ContinuousMonoidHom.proPFrattini_le_ker hH f) x

/-- Composition with the quotient projection recovers the original homomorphism. -/
@[simp]
theorem _root_.ContinuousMonoidHom.frattiniQuotientLift_comp_quotientMk {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    (ContinuousMonoidHom.frattiniQuotientLift hH f).comp
      (ContinuousMonoidHom.quotientMk (proPFrattini p G)) = f := by
  ext x
  simp

/-- A continuous homomorphism on the quotient with the same values on representatives as `f`
equals `frattiniQuotientLift hH f`. -/
theorem _root_.ContinuousMonoidHom.frattiniQuotientLift_unique {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H)
    (g : (G ⧸ proPFrattini p G) →ₜ* H)
    (hg : ∀ x : G, g (x : G ⧸ proPFrattini p G) = f x) :
    g = ContinuousMonoidHom.frattiniQuotientLift hH f := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proPFrattini p G) q
  exact hg x

/-- Continuous homomorphisms to a discrete group of cardinality `p` factor uniquely through the
pro-`p` Frattini quotient. -/
theorem _root_.ContinuousMonoidHom.existsUnique_frattiniQuotient_lift {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) (f : G →ₜ* H) :
    ∃! g : (G ⧸ proPFrattini p G) →ₜ* H,
      g.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G)) = f := by
  refine ⟨ContinuousMonoidHom.frattiniQuotientLift hH f, by simp, ?_⟩
  intro g hg
  apply ContinuousMonoidHom.frattiniQuotientLift_unique hH f
  intro x
  have hx := congrArg (fun k : G →ₜ* H => k x) hg
  simpa using hx

/-- Precomposition with the Frattini quotient projection identifies continuous homomorphisms
from the quotient with continuous homomorphisms from `G` for a discrete target of cardinality
`p`. -/
def _root_.ContinuousMonoidHom.frattiniQuotientHomEquiv {H : Type*} [Group H]
    [TopologicalSpace H] [DiscreteTopology H] (hH : Nat.card H = p) :
    ((G ⧸ proPFrattini p G) →ₜ* H) ≃ (G →ₜ* H) where
  toFun f := f.comp (ContinuousMonoidHom.quotientMk (proPFrattini p G))
  invFun f := ContinuousMonoidHom.frattiniQuotientLift hH f
  left_inv f := by
    apply ContinuousMonoidHom.ext
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proPFrattini p G) q
    simp
  right_inv f := by simp

end TauCeti
