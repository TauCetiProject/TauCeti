/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Quiver.ConnectedComponent
public import Mathlib.Data.Fintype.EquivFin

/-!
# The reachability order on strongly connected components

Mathlib's `Quiver.StronglyConnectedComponent V` is the quotient of the vertices of a quiver by
mutual reachability. Reachability itself descends to this quotient: one component lies below
another when some, equivalently every, vertex of the first has a path to some, equivalently
every, vertex of the second. Mutual reachability is exactly equality of components, so this is a
partial order, the condensation order of the quiver. It is finite when the vertices are.

## Main definitions

* `Quiver.StronglyConnectedComponent.instPartialOrder`: components ordered by reachability.

## Main results

* `Quiver.StronglyConnectedComponent.mk_le_mk`: the component of `a` lies below that of `b`
  exactly when there is a path from `a` to `b`.
* `Quiver.StronglyConnectedComponent.mk_surjective` and `Quiver.StronglyConnectedComponent.ind`:
  every component is the component of a vertex.
-/

public section

namespace Quiver.StronglyConnectedComponent

universe v u

variable {V : Type u} [Quiver.{v} V]

theorem mk_surjective :
    Function.Surjective (StronglyConnectedComponent.mk : V → StronglyConnectedComponent V) :=
  @Quotient.mk'_surjective _ (stronglyConnectedSetoid V)

/-- Induction on strongly connected components: a property of components holds for all of them
when it holds for the component of every vertex. -/
@[elab_as_elim]
protected theorem ind {β : StronglyConnectedComponent V → Prop}
    (h : ∀ v : V, β (StronglyConnectedComponent.mk v)) (C : StronglyConnectedComponent V) : β C :=
  Quotient.ind h C

/-- Strongly connected components are ordered by reachability: `C ≤ D` when there is a path from
a vertex of `C` to a vertex of `D`. Mutually reachable vertices have equal components, so this
order is antisymmetric. -/
instance instPartialOrder : PartialOrder (StronglyConnectedComponent V) where
  le := @Quotient.lift₂ _ _ _ (stronglyConnectedSetoid V) (stronglyConnectedSetoid V)
    (fun a b ↦ Nonempty (Path a b)) fun _ _ _ _ ⟨⟨p⟩, ⟨p'⟩⟩ ⟨⟨q⟩, ⟨q'⟩⟩ ↦
      propext ⟨fun ⟨r⟩ ↦ ⟨(p'.comp r).comp q⟩, fun ⟨r⟩ ↦ ⟨(p.comp r).comp q'⟩⟩
  le_refl C := Quotient.inductionOn C fun _ ↦ ⟨Path.nil⟩
  le_trans C D E := Quotient.inductionOn₃ C D E fun _ _ _ ⟨p⟩ ⟨q⟩ ↦ ⟨p.comp q⟩
  le_antisymm C D := Quotient.inductionOn₂ C D fun _ _ hab hba ↦ Quotient.sound ⟨hab, hba⟩

/-- The component of `a` lies below that of `b` exactly when there is a path from `a` to `b`. -/
@[simp]
theorem mk_le_mk {a b : V} :
    StronglyConnectedComponent.mk a ≤ (StronglyConnectedComponent.mk b :
      StronglyConnectedComponent V) ↔ Nonempty (Path a b) :=
  Iff.rfl

instance instFinite [Finite V] : Finite (StronglyConnectedComponent V) :=
  Quotient.finite _

end Quiver.StronglyConnectedComponent
