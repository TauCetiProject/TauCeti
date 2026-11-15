/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.UniversalCover.Classification.ActionCover.Basic
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Connectedness of the cover attached to an action

The associated cover of a fundamental-group set has path-connected total space exactly when
the action on its labels is transitive and the label set is nonempty. The general criterion for
a covering map reduces connectedness to transitivity of monodromy on one fibre; the canonical
fibre equivalence identifies that monodromy with the given action.
-/

public section
noncomputable section

open Topology

universe u

namespace TauCeti.UniversalCover

variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
  [LocallyPathConnectedSpace X] [SemilocallySimplyConnectedSpace X]
  (x₀ : X) (A : Type u) [MulAction (FundamentalGroup X x₀) A]
  [TopologicalSpace A] [DiscreteTopology A]

/-- The monodromy action on the fibre of the associated action cover. -/
local instance actionCoverFiberMulAction :
    MulAction (FundamentalGroup X x₀) (actionCoverProj x₀ A ⁻¹' {x₀}) :=
  (isCoveringMap_actionCoverProj x₀ A).fundamentalGroupMulAction x₀

/-- The cover attached to a fundamental-group set is path connected exactly when the label set
is nonempty and the action on it is transitive. -/
theorem pathConnectedSpace_actionCover_iff :
    PathConnectedSpace (ActionCover x₀ A) ↔
      Nonempty A ∧ MulAction.IsPretransitive (FundamentalGroup X x₀) A := by
  let hp := isCoveringMap_actionCoverProj x₀ A
  rw [IsCoveringMap.pathConnectedSpace_iff hp x₀]
  constructor
  · rintro ⟨⟨e⟩, htrans⟩
    have hA : Nonempty A := ⟨(actionCoverFiberEquiv x₀ A).symm e⟩
    refine ⟨hA, ?_⟩
    apply MulAction.IsPretransitive.mk
    intro a b
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq (actionCoverFiberEquiv x₀ A a)
      (actionCoverFiberEquiv x₀ A b)
    refine ⟨g, (actionCoverFiberEquiv x₀ A).injective ?_⟩
    rw [← monodromy_actionCoverFiberEquiv]
    exact hg
  · rintro ⟨⟨a₀⟩, htrans⟩
    refine ⟨⟨actionCoverFiberEquiv x₀ A a₀⟩, ?_⟩
    apply MulAction.IsPretransitive.mk
    intro e e'
    let a := (actionCoverFiberEquiv x₀ A).symm e
    let b := (actionCoverFiberEquiv x₀ A).symm e'
    obtain ⟨g, hg⟩ := htrans.exists_smul_eq a b
    refine ⟨g, ?_⟩
    have he : e = actionCoverFiberEquiv x₀ A a := by simp [a]
    have he' : e' = actionCoverFiberEquiv x₀ A b := by simp [b]
    calc
      g • e = g • actionCoverFiberEquiv x₀ A a := by rw [he]
      _ = actionCoverFiberEquiv x₀ A (g • a) :=
        monodromy_actionCoverFiberEquiv x₀ A g a
      _ = actionCoverFiberEquiv x₀ A b := congrArg (actionCoverFiberEquiv x₀ A) hg
      _ = e' := he'.symm

end TauCeti.UniversalCover
