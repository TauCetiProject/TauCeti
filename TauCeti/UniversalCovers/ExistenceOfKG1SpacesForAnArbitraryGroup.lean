/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Topology.Connected.PathConnected
public import Mathlib.Topology.Homotopy.HomotopyGroup

/-!
# Roadmap: UniversalCovers
Target: Existence of `K(G, 1)` spaces for an arbitrary group.
<!--tauceti-target:v1
  {"focus":"UniversalCovers",
   "id":"UniversalCovers.Existence_of__K_G__1___spaces_for_an_arbitrary_group"}-->
-/

public section

open scoped Topology Topology.Homotopy unitInterval

namespace UniversalCovers

/-- An Eilenberg–MacLane space `K(G, 1)` representation for a group `G`:
a path-connected pointed topological space whose fundamental group `π₁` is isomorphic to `G`,
and whose higher homotopy groups `π_n` for `n ≥ 2` are all trivial. -/
structure EilenbergMacLaneOne (G : Type*) [Group G] where
  /-- The underlying topological space. -/
  Space : Type
  /-- Topology on the space. -/
  [top : TopologicalSpace Space]
  /-- Path-connectedness: an Eilenberg-MacLane space is connected. -/
  [pathConnected : PathConnectedSpace Space]
  /-- Chosen basepoint of the space. -/
  basepoint : Space
  /-- Group isomorphism between the fundamental group `π₁` and `G`. -/
  piOneIso : π_ 1 Space basepoint ≃* G
  /-- Triviality of higher homotopy groups `π_n` for `n ≥ 2`. -/
  higherHomotopyTrivial : ∀ (n : ℕ), Subsingleton (π_ (n + 2) Space basepoint)

attribute [instance] EilenbergMacLaneOne.top EilenbergMacLaneOne.pathConnected

/-- Any generalized loop in `PUnit` is uniquely equal to the constant loop. -/
lemma genLoop_punit_unique (k : ℕ) (f : Ω^ (Fin k) PUnit PUnit.unit) :
    f = GenLoop.const := by
  apply GenLoop.ext
  intro t
  rfl

/-- Every homotopy group of the singleton space `PUnit` is a subsingleton. -/
instance punit_homotopyGroup_subsingleton (k : ℕ) :
    Subsingleton (π_ k PUnit PUnit.unit) := ⟨by
  intro a b
  induction a using Quotient.inductionOn with
  | _ f =>
    induction b using Quotient.inductionOn with
    | _ g =>
      have hf : f = GenLoop.const := genLoop_punit_unique k f
      have hg : g = GenLoop.const := genLoop_punit_unique k g
      rw [hf, hg]⟩

/-- The unique group isomorphism between `π₁` of `PUnit` and `PUnit`. -/
noncomputable def punitMulEquivPUnit : π_ 1 PUnit PUnit.unit ≃* PUnit where
  toFun _ := PUnit.unit
  invFun _ := 1
  left_inv x := Subsingleton.elim _ x
  right_inv x := Subsingleton.elim _ x
  map_mul' _ _ := rfl

/-- Path-connectedness instance for `PUnit`. -/
instance punitPathConnectedSpace : PathConnectedSpace PUnit :=
  PathConnectedSpace.mk ⟨PUnit.unit⟩ (fun x _ => ⟨Path.refl x⟩)

/-- Concrete construction of an Eilenberg-MacLane `K(G, 1)` space for the trivial group. -/
noncomputable def eilenbergMacLaneOneTrivial : EilenbergMacLaneOne PUnit where
  Space := PUnit
  basepoint := PUnit.unit
  piOneIso := punitMulEquivPUnit
  higherHomotopyTrivial := fun n => punit_homotopyGroup_subsingleton (n + 2)

/-- Unconditional existence of an Eilenberg-MacLane `K(G, 1)` space for the trivial group. -/
theorem exists_eilenberg_maclane_one_trivial :
    Nonempty (EilenbergMacLaneOne PUnit) :=
  ⟨eilenbergMacLaneOneTrivial⟩

/-- Transporting an Eilenberg-MacLane `K(G, 1)` space along an isomorphism of groups. -/
noncomputable def ofMulEquiv {G H : Type*} [Group G] [Group H]
    (K : EilenbergMacLaneOne G) (e : G ≃* H) : EilenbergMacLaneOne H where
  Space := K.Space
  basepoint := K.basepoint
  piOneIso := K.piOneIso.trans e
  higherHomotopyTrivial := K.higherHomotopyTrivial

/-- Existence of an Eilenberg-MacLane `K(G, 1)` space for any group with a single element. -/
theorem exists_eilenberg_maclane_one_of_subsingleton
    (G : Type*) [Group G] [Subsingleton G] : Nonempty (EilenbergMacLaneOne G) := by
  have e : PUnit.{1} ≃* G := {
    toFun := fun _ => 1
    invFun := fun _ => PUnit.unit
    left_inv := fun _ => Subsingleton.elim _ _
    right_inv := fun x => Subsingleton.elim _ x
    map_mul' := fun _ _ => (Subsingleton.elim _ _).symm
  }
  exact ⟨ofMulEquiv eilenbergMacLaneOneTrivial e⟩

/-- For any group `G` admitting a `K(G, 1)` space, its fundamental group is isomorphic to `G`. -/
theorem em_space_fundamental_group {G : Type*} [Group G] (K : EilenbergMacLaneOne G) :
    Nonempty (π_ 1 K.Space K.basepoint ≃* G) :=
  ⟨K.piOneIso⟩

/-- All higher homotopy groups of a `K(G, 1)` space are trivial. -/
theorem em_space_higher_homotopy_trivial {G : Type*} [Group G] (K : EilenbergMacLaneOne G)
    (n : ℕ) : Subsingleton (π_ (n + 2) K.Space K.basepoint) :=
  K.higherHomotopyTrivial n

end UniversalCovers
