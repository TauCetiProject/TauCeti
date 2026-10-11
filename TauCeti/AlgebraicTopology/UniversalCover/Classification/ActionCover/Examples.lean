/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic

/-!
# Examples of covers attached to fundamental-group sets

The balanced-product construction applies to arbitrary actions, including the singleton action.
In that case its associated cover is the identity cover of the base. This gives a concrete check
that the construction recovers the trivial one-sheeted cover.
-/

public section
noncomputable section

open Topology

universe u

namespace TauCeti.UniversalCover

variable {X : Type u} [TopologicalSpace X] (x₀ : X)

/-- The projection of the singleton associated cover is injective. Its fibers are the
universal-cover orbits, and the singleton label adds no further identifications. -/
theorem actionCoverPUnitProj_injective :
    Function.Injective (actionCoverProj x₀ PUnit) := by
  intro a b hab
  obtain ⟨p, rfl⟩ := Quotient.exists_rep a
  obtain ⟨q, rfl⟩ := Quotient.exists_rep b
  have hp : actionCoverProj x₀ PUnit (Quotient.mk _ p) = proj p.1 := by
    simpa [BalancedProduct.mk] using actionCoverProj_mk x₀ PUnit p.1 p.2
  have hq : actionCoverProj x₀ PUnit (Quotient.mk _ q) = proj q.1 := by
    simpa [BalancedProduct.mk] using actionCoverProj_mk x₀ PUnit q.1 q.2
  have hpq : proj p.1 = proj q.1 := by simpa only [hp, hq] using hab
  obtain ⟨g, hg⟩ := (proj_eq_iff_mem_orbit (x₀ := x₀)).mp hpq
  apply Quotient.sound
  exact ⟨g, by simpa using Prod.ext hg (Subsingleton.elim (g • q.2) p.2)⟩

variable [LocallyPathConnectedSpace X] [PathConnectedSpace X]
  [SemilocallySimplyConnectedSpace X]

/-- The associated cover of the singleton action is homeomorphic to its base by the covering
projection. -/
abbrev actionCoverPUnitHomeomorph : ActionCover x₀ PUnit ≃ₜ X := by
  have hsurj : Function.Surjective (actionCoverProj x₀ PUnit) := by
    intro y
    obtain ⟨e, he⟩ := (UniversalCover.proj_surjective (x₀ := x₀)) y
    refine ⟨BalancedProduct.mk (FundamentalGroup X x₀) e PUnit.unit, ?_⟩
    simp [he]
  exact Equiv.toHomeomorphOfContinuousOpen
    (Equiv.ofBijective (actionCoverProj x₀ PUnit)
      ⟨actionCoverPUnitProj_injective x₀, hsurj⟩)
    (continuous_actionCoverProj x₀ PUnit)
    (isCoveringMap_actionCoverProj x₀ PUnit).isOpenMap

/-- The singleton-cover homeomorphism is the projection of the associated cover. -/
@[simp]
theorem actionCoverPUnitHomeomorph_apply (z : ActionCover x₀ PUnit) :
    actionCoverPUnitHomeomorph x₀ z = actionCoverProj x₀ PUnit z :=
  rfl

/-- On quotient representatives, the singleton-cover homeomorphism is the endpoint projection. -/
@[simp]
theorem actionCoverPUnitHomeomorph_mk (e : UniversalCover x₀) (a : PUnit) :
    actionCoverPUnitHomeomorph x₀ (BalancedProduct.mk (FundamentalGroup X x₀) e a) = proj e := by
  rw [actionCoverPUnitHomeomorph_apply, actionCoverProj_mk]

end TauCeti.UniversalCover
