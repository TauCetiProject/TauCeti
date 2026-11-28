/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Basic
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.LocallyConstant.Basic

import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Compactness.Compact

/-!
# Orbit local constancy and continuity of equivariant maps for actions with open stabilizers

Let `Γ` be a topological group acting on a type `Ω` with open point stabilizers. Then every orbit
map `g ↦ g • x` is locally constant and every predicate on `g • x` cuts out a closed subset of `Γ`.
When `Γ` is compact and acts faithfully on `Ω`, any map `φ : Γ' → Γ` equivariant along an
injective map `j : Ω → Ω'` from another action with open stabilizers is automatically continuous.

## Main results

* `TauCeti.isLocallyConstant_smul_of_isOpen_stabilizer`: each orbit map `g ↦ g • x` is locally
  constant.
* `TauCeti.isClosed_setOf_smul_of_isOpen_stabilizer`: `{g : Γ | P (g • x)}` is closed.
* `TauCeti.continuous_of_equivariant_injective`: an equivariant map `φ : Γ' → Γ` along an
  injective `j : Ω → Ω'` is continuous when `Γ` is compact and acts faithfully with open
  stabilizers.

## References

* `grh-lean`, https://github.com/lsernau/grh-lean (commit
  `72fead102f663d5c7a407964a13dc0cf9d977207`), file
  `src/Lib/ClassField/Places/ProfiniteGalois.lean` (declarations `New.isLocallyConstant_smul`,
  `New.isClosed_setOf_smul`, `New.continuous_of_equivariant_emb`); Apache 2.0, Copyright 2026
  Anthropic, PBC.
-/

public section

namespace TauCeti

/-- If a topological group `Γ` acts on `Ω` and the stabilizer of `x : Ω` is open, then the orbit
map `g ↦ g • x` is locally constant. -/
theorem isLocallyConstant_smul_of_isOpen_stabilizer {Γ Ω : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [MulAction Γ Ω] {x : Ω}
    (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) :
    IsLocallyConstant fun g : Γ ↦ g • x := by
  have : DiscreteTopology (Γ ⧸ MulAction.stabilizer Γ x) :=
    QuotientGroup.discreteTopology hx
  exact .of_discrete (MulAction.ofQuotientStabilizer Γ x)

/-- If a topological group `Γ` acts on `Ω` and the stabilizer of `x : Ω` is open, then for any
predicate `P : Ω → Prop`, the set `{g : Γ | P (g • x)}` is closed in `Γ`. -/
theorem isClosed_setOf_smul_of_isOpen_stabilizer {Γ Ω : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [MulAction Γ Ω] {x : Ω}
    (hx : IsOpen (MulAction.stabilizer Γ x : Set Γ)) (P : Ω → Prop) :
    IsClosed {g : Γ | P (g • x)} :=
  isOpen_compl_iff.mp (isLocallyConstant_smul_of_isOpen_stabilizer hx {y : Ω | ¬P y})

/-- Let `Γ` be a compact topological group acting faithfully on `Ω` with open point stabilizers,
and let `Γ'` be a topological group acting on `Ω'` with open point stabilizers. If `j : Ω → Ω'` is
injective and `φ : Γ' → Γ` satisfies `j (φ g • x) = g • j x` for all `g` and `x`, then `φ` is
continuous. -/
theorem continuous_of_equivariant_injective {Γ Γ' Ω Ω' : Type*} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [MulAction Γ Ω] [FaithfulSMul Γ Ω]
    [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [MulAction Γ' Ω']
    (h_open : ∀ x : Ω, IsOpen (MulAction.stabilizer Γ x : Set Γ))
    (h_open' : ∀ y : Ω', IsOpen (MulAction.stabilizer Γ' y : Set Γ'))
    {j : Ω → Ω'} (hj : Function.Injective j) {φ : Γ' → Γ}
    (hφ : ∀ (g : Γ') (x : Ω), j (φ g • x) = g • j x) :
    Continuous φ := by
  let : TopologicalSpace Ω := ⊥
  have : DiscreteTopology Ω := ⟨rfl⟩
  have h_emb : Topology.IsClosedEmbedding fun (g : Γ) (x : Ω) ↦ g • x :=
    (continuous_pi fun x ↦ (isLocallyConstant_smul_of_isOpen_stabilizer (h_open x)).continuous)
      |>.isClosedEmbedding fun g g' h_eq ↦ eq_of_smul_eq_smul (congrFun h_eq)
  refine h_emb.continuous_iff.mpr (continuous_pi fun x ↦ IsLocallyConstant.continuous ?_)
  have h_const : IsLocallyConstant fun g : Γ' ↦ j (φ g • x) := by
    simpa only [hφ] using isLocallyConstant_smul_of_isOpen_stabilizer (h_open' (j x))
  exact h_const.desc _ j hj

end TauCeti
