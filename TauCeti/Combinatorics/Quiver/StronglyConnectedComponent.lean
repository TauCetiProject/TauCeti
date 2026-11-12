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

The strongly connected components of a quiver are the classes of vertices joined by paths in both
directions. Reachability descends to them: one component is below another when some, equivalently
every, vertex of the first has a path to some, equivalently every, vertex of the second. This
relation is a partial order, the reachability order of the condensation of the quiver, and the
components are finite in number when the vertices are. This order organizes, for instance, the
minimum cuts of a network through the strongly connected components of its residual network.

## Main results

* `Quiver.StronglyConnectedComponent.instPartialOrder`: strongly connected components are
  partially ordered by reachability.
* `Quiver.StronglyConnectedComponent.mk_le_mk`: the component of `a` is below that of `b` exactly
  when there is a path from `a` to `b`.
* `Quiver.StronglyConnectedComponent.mk_surjective`: every component contains a vertex.
-/

public section

namespace Quiver.StronglyConnectedComponent

variable {V : Type*} [Quiver V]

/-- Every strongly connected component contains a vertex. -/
theorem mk_surjective :
    Function.Surjective (StronglyConnectedComponent.mk : V → StronglyConnectedComponent V) :=
  fun C ↦ Quotient.inductionOn C fun a ↦ ⟨a, rfl⟩

instance [Finite V] : Finite (StronglyConnectedComponent V) :=
  Quotient.finite _

/-- Strongly connected components are partially ordered by reachability: `C ≤ D` when a vertex of
`C` has a path to a vertex of `D`. -/
instance instPartialOrder : PartialOrder (StronglyConnectedComponent V) where
  le := Quotient.lift₂ (s₁ := stronglyConnectedSetoid V) (s₂ := stronglyConnectedSetoid V)
    (fun a b ↦ Nonempty (Path a b)) fun _ _ _ _ ⟨⟨p⟩, ⟨p'⟩⟩ ⟨⟨q⟩, ⟨q'⟩⟩ ↦
      propext ⟨fun ⟨r⟩ ↦ ⟨p'.comp (r.comp q)⟩, fun ⟨r⟩ ↦ ⟨p.comp (r.comp q')⟩⟩
  le_refl C := Quotient.inductionOn C fun _ ↦ ⟨Path.nil⟩
  le_trans C D E := Quotient.inductionOn₃ C D E fun _ _ _ ⟨p⟩ ⟨q⟩ ↦ ⟨p.comp q⟩
  le_antisymm C D := Quotient.inductionOn₂ C D fun _ _ hab hba ↦ Quotient.sound ⟨hab, hba⟩

/-- The component of `a` is below the component of `b` exactly when there is a path from `a` to
`b`. -/
@[simp]
theorem mk_le_mk {a b : V} :
    StronglyConnectedComponent.mk a ≤ StronglyConnectedComponent.mk b ↔ Nonempty (Path a b) :=
  Iff.rfl

end Quiver.StronglyConnectedComponent
