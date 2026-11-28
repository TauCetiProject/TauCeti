/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.RightFibration.KanComplex
import TauCeti.AlgebraicTopology.SimplicialSet.WeakHomotopyEquivalence.TrivialFibration

/-!
# Fibrewise tests for trivial right fibrations

A right fibration `f : X ⟶ Y` over a further simplicial set `S` is a trivial fibration
exactly when its restrictions to the fibres over every vertex of `S` are trivial
fibrations. If the fibres of `Y ⟶ S` are Kan complexes, the test is equivalently
that each restriction is an intrinsic weak homotopy equivalence. In particular,
this applies when `Y ⟶ S` is a right fibration. The same tests hold for left
fibrations, with no further hypothesis on the base `S`.

This permits testing relative slice restrictions on their Kan fibres, rather than
on the generally non-Kan total slice. No model structure or straightening theorem
is used. The argument uses the contractible-fibre test for right fibrations
(Lurie, *Higher Topos Theory*, Lemma 2.1.3.4).
-/

public section

universe u

open CategoryTheory Limits MorphismProperty Simplicial HomotopicalAlgebra

namespace SSet

open modelCategoryQuillen

variable {X Y S : SSet.{u}}

private theorem
    rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map_of_isWeaklyContractible_fiber
    (f : X ⟶ Y) (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q)
    (hf : (∀ y : Y _⦋0⦌, IsWeaklyContractible (fiber f y : SSet.{u})) →
      (monomorphisms SSet.{u}).rlp f) :
    (monomorphisms SSet.{u}).rlp f ↔
      ∀ s : S _⦋0⦌, (monomorphisms SSet.{u}).rlp (fiber.map f hq s) := by
  refine ⟨fun h s ↦ (monomorphisms SSet.{u}).rlp.of_isPullback
    (fiber.isPullback_map f hq s) h, fun h ↦ hf ?_⟩
  exact fun y ↦ fiber.isWeaklyContractible_of_rlp_map f p hq y (h (p.app _ y))

private theorem forall_rlp_monomorphisms_iff_forall_isWeakHomotopyEquivalence_fiber_map
    (f : X ⟶ Y) (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q)
    (hp : ∀ s : S _⦋0⦌, KanComplex (fiber p s : SSet.{u}))
    (hf : ∀ s : S _⦋0⦌, KanComplex (fiber p s : SSet.{u}) →
      Fibration (fiber.map f hq s)) :
    (∀ s : S _⦋0⦌, (monomorphisms SSet.{u}).rlp (fiber.map f hq s)) ↔
      ∀ s : S _⦋0⦌, IsWeakHomotopyEquivalence (fiber.map f hq s) := by
  apply forall_congr'
  intro s
  have := hp s
  have := hf s (hp s)
  exact rlp_monomorphisms_iff_isWeakHomotopyEquivalence _

namespace RightFibration

/-- A right fibration over `S` is a trivial fibration exactly when the induced map
on each fibre over a vertex of `S` is a trivial fibration. The further map `p` to
`S` need not be a fibration. -/
theorem rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map (f : X ⟶ Y) [RightFibration f]
    (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q) :
    (monomorphisms SSet.{u}).rlp f ↔
      ∀ s : S _⦋0⦌, (monomorphisms SSet.{u}).rlp (fiber.map f hq s) := by
  exact rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map_of_isWeaklyContractible_fiber
    f p hq
    (rlp_monomorphisms_iff_isWeaklyContractible_fiber f).2

/-- For a right fibration over `S`, if the fibres of `Y ⟶ S` are Kan complexes,
triviality is detected by intrinsic weak homotopy equivalences on these fibres. -/
theorem rlp_monomorphisms_iff_forall_isWeakHomotopyEquivalence_fiber_map
    (f : X ⟶ Y) [RightFibration f] (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q)
    (hp : ∀ s : S _⦋0⦌, KanComplex (fiber p s : SSet.{u})) :
    (monomorphisms SSet.{u}).rlp f ↔
      ∀ s : S _⦋0⦌, IsWeakHomotopyEquivalence (fiber.map f hq s) := by
  rw [rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map f p hq]
  apply forall_rlp_monomorphisms_iff_forall_isWeakHomotopyEquivalence_fiber_map f p hq hp
  intro s hs
  have := hs
  have : RightFibration (fiber.map f hq s) :=
    .of_isPullback (fiber.isPullback_map f hq s)
  exact RightFibration.fibration_of_kanComplex (fiber.map f hq s)

end RightFibration

namespace LeftFibration

/-- A left fibration over `S` is a trivial fibration exactly when the induced map
on each fibre over a vertex of `S` is a trivial fibration. -/
theorem rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map (f : X ⟶ Y) [LeftFibration f]
    (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q) :
    (monomorphisms SSet.{u}).rlp f ↔
      ∀ s : S _⦋0⦌, (monomorphisms SSet.{u}).rlp (fiber.map f hq s) := by
  exact rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map_of_isWeaklyContractible_fiber
    f p hq
    (rlp_monomorphisms_iff_isWeaklyContractible_fiber f).2

/-- For a left fibration over `S`, if the fibres of `Y ⟶ S` are Kan complexes,
triviality is detected by intrinsic weak homotopy equivalences on these fibres. -/
theorem rlp_monomorphisms_iff_forall_isWeakHomotopyEquivalence_fiber_map
    (f : X ⟶ Y) [LeftFibration f] (p : Y ⟶ S) {q : X ⟶ S} (hq : f ≫ p = q)
    (hp : ∀ s : S _⦋0⦌, KanComplex (fiber p s : SSet.{u})) :
    (monomorphisms SSet.{u}).rlp f ↔
      ∀ s : S _⦋0⦌, IsWeakHomotopyEquivalence (fiber.map f hq s) := by
  rw [rlp_monomorphisms_iff_forall_rlp_monomorphisms_fiber_map f p hq]
  apply forall_rlp_monomorphisms_iff_forall_isWeakHomotopyEquivalence_fiber_map f p hq hp
  intro s hs
  have := hs
  have : LeftFibration (fiber.map f hq s) :=
    .of_isPullback (fiber.isPullback_map f hq s)
  exact LeftFibration.fibration_of_kanComplex (fiber.map f hq s)

end LeftFibration

end SSet
