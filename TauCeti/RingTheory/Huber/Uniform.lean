/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Huber.RingOfDefinition
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.Topology.Algebra.Ring.Ideal

/-!
# Uniform Huber rings

A topological ring `A` is *uniform* when its set `A°` of power-bounded elements is bounded
(Hansen–Kedlaya, Definition 2.3). Uniformity is the hypothesis of the Buzzard–Verberkmoes
sheafiness criterion: if every rational localisation of a complete Tate ring is uniform, then the
structure presheaf of its adic spectrum is a sheaf, with no noetherian hypothesis.

For a Huber ring, `A°` is always an open subring, so by Wedhorn's Lemma 6.2 uniformity says
exactly that `A°` is itself a ring of definition. In a uniform Tate ring every nilpotent element
lies in the closure of zero, so a Hausdorff uniform Tate ring is reduced: a Hausdorff Tate ring with
a nonzero nilpotent element is not uniform.

## Main definitions

* `TauCeti.Huber.IsUniform`: the power-bounded elements form a bounded set.

## Main results

* `TauCeti.Huber.isUniform_iff_exists_pairOfDefinition_ringOfDefinition_eq`: a Huber ring is
  uniform exactly when `A°` is a ring of definition.
* `TauCeti.Huber.isUniform_iff_of_ringEquiv`: uniformity transports along topological ring
  isomorphisms.
* `TauCeti.Huber.IsUniform.nilradical_le_closure_bot`: in a uniform Tate ring every nilpotent
  element lies in the closure of zero.
* `TauCeti.Huber.IsUniform.isReduced`: a Hausdorff uniform Tate ring is reduced.

Discrete rings are uniform (`TauCeti.Huber.IsUniform.of_discreteTopology`), and so are normed
division rings, by `TauCeti.Huber.IsUniform.of_normedDivisionRing` in
`TauCeti.RingTheory.Huber.Normed`.

## References

* D. Hansen, K. S. Kedlaya, *Sheafiness criteria for Huber rings*, Definition 2.3.
* K. Buzzard, A. Verberkmoes, *Stably uniform affinoids are sheafy*, J. reine angew. Math. 740
  (2018).
* [Wedhorn, *Adic Spaces*][wedhorn_adic], Lemma 6.2 and Corollary 6.4.
-/

public section

open Filter Topology

namespace TauCeti.Huber

section Defs

variable (A : Type*) [MonoidWithZero A] [TopologicalSpace A]

/-- A topological ring is *uniform* when its power-bounded elements form a bounded set
(Hansen–Kedlaya, Definition 2.3). -/
class IsUniform : Prop where
  /-- The set `A°` of power-bounded elements is bounded. -/
  isBounded_setOf_isPowerBounded : IsBounded {a : A | IsPowerBounded a}

variable {A}

/-- Unfolding lemma for `TauCeti.Huber.IsUniform`. -/
theorem isUniform_iff : IsUniform A ↔ IsBounded {a : A | IsPowerBounded a} :=
  ⟨fun h ↦ h.1, fun h ↦ ⟨h⟩⟩

/-- **Discrete rings are uniform**: in the discrete topology every set is bounded. -/
instance (priority := 100) IsUniform.of_discreteTopology [DiscreteTopology A] : IsUniform A :=
  ⟨isBounded_of_discreteTopology _⟩

end Defs

section Transport

variable {A B : Type*} [Semiring A] [Semiring B] [TopologicalSpace A] [TopologicalSpace B]

/-- **Uniformity transports along a topological ring isomorphism.** -/
theorem isUniform_iff_of_ringEquiv (e : A ≃+* B) (he : Continuous e) (he' : Continuous e.symm) :
    IsUniform A ↔ IsUniform B := by
  have himage : e '' {a : A | IsPowerBounded a} = {b : B | IsPowerBounded b} := by
    ext b
    obtain ⟨a, rfl⟩ := e.surjective b
    simp [isPowerBounded_ringEquiv_iff e he he']
  rw [isUniform_iff, isUniform_iff, ← himage, isBounded_image_ringEquiv_iff e he he']

/-- A topological ring isomorphic to a uniform one is uniform. -/
theorem IsUniform.of_ringEquiv [IsUniform A] (e : A ≃+* B) (he : Continuous e)
    (he' : Continuous e.symm) : IsUniform B :=
  (isUniform_iff_of_ringEquiv e he he').mp ‹_›

end Transport

section Nonarchimedean

variable {A : Type*} [CommRing A] [TopologicalSpace A] [NonarchimedeanRing A]

/-- A nonarchimedean ring is uniform exactly when its power-bounded subring `A°` is bounded. -/
theorem isUniform_iff_isBounded_powerBoundedSubring :
    IsUniform A ↔ IsBounded (powerBoundedSubring A : Set A) := by
  rw [isUniform_iff]
  exact Iff.of_eq (congrArg IsBounded (Set.ext fun _ ↦ mem_powerBoundedSubring.symm))

/-- In a uniform nonarchimedean ring the power-bounded subring `A°` is bounded. -/
theorem IsUniform.isBounded_powerBoundedSubring [IsUniform A] :
    IsBounded (powerBoundedSubring A : Set A) :=
  isUniform_iff_isBounded_powerBoundedSubring.mp ‹_›

end Nonarchimedean

section Huber

variable {A : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

/-- **A Huber ring is uniform exactly when `A°` is a ring of definition**, that is, when some pair
of definition has `A°` as its ring. -/
theorem isUniform_iff_exists_pairOfDefinition_ringOfDefinition_eq [IsHuberRing A] :
    IsUniform A ↔ ∃ Q : PairOfDefinition A, Q.ringOfDefinition = powerBoundedSubring A := by
  rw [exists_pairOfDefinition_ringOfDefinition_eq_iff, isUniform_iff_isBounded_powerBoundedSubring]
  exact ⟨fun h ↦ ⟨isOpen_powerBoundedSubring A, h⟩, And.right⟩

/-- **In a uniform Tate ring every nilpotent element lies in the closure of zero.** -/
theorem IsUniform.nilradical_le_closure_bot [IsTateRing A] [IsUniform A] :
    nilradical A ≤ (⊥ : Ideal A).closure := by
  intro a ha
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  obtain ⟨u, rfl⟩ := hϖ.isUnit
  -- `a` lies in every neighbourhood `U` of zero, that is, `a ⤳ 0`: choose `V` with `V · A° ⊆ U`
  -- and `n` with `ϖⁿ ∈ V`; then `a = ϖⁿ · (ϖ⁻ⁿ a)` with `ϖ⁻ⁿ a` nilpotent, hence power-bounded.
  have hspec : a ⤳ 0 := by
    rw [specializes_iff_pure, pure_le_iff]
    intro U hU
    obtain ⟨V, hV, hVU⟩ := isBounded_iff.mp (IsUniform.isBounded_setOf_isPowerBounded (A := A))
      U hU
    obtain ⟨n, hn⟩ := (hϖ.isTopologicallyNilpotent.eventually_mem hV).exists
    have hpb : IsPowerBounded ((↑u⁻¹ : A) ^ n * a) :=
      .of_isTopologicallyNilpotent
        ((Commute.all _ a).isNilpotent_mul_left ha).isTopologicallyNilpotent
    have heq : (u : A) ^ n * ((↑u⁻¹ : A) ^ n * a) = a := by
      rw [← mul_assoc, ← mul_pow, Units.mul_inv, one_pow, one_mul]
    exact heq ▸ hVU (Set.mul_mem_mul hn hpb)
  rw [← SetLike.mem_coe, Ideal.coe_closure, Submodule.bot_coe, ← specializes_iff_mem_closure]
  exact hspec.symm

/-- **A Hausdorff uniform Tate ring is reduced.** -/
theorem IsUniform.isReduced [IsTateRing A] [IsUniform A] [T0Space A] : IsReduced A := by
  refine ⟨fun a ha ↦ ?_⟩
  have h := IsUniform.nilradical_le_closure_bot (A := A) (mem_nilradical.mpr ha)
  rwa [Ideal.closure_eq_of_isClosed _ (by simp), Ideal.mem_bot] at h

end Huber

end TauCeti.Huber
