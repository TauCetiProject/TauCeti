/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.WeakHomotopyEquivalence

/-!
# Homotopy groups of totally disconnected spaces

In positive dimensions, every homotopy group of a totally disconnected space is trivial
(`HomotopyGroup.subsingleton_of_totallyDisconnectedSpace`): a generalized loop is constant, since
the cube is connected, and it sends the nonempty boundary of the cube to the base point.

Consequently a map `f : X → Y` out of a totally disconnected space which meets every path
component of `Y` exactly once is a weak homotopy equivalence as soon as the positive-dimensional
homotopy groups of `Y` vanish at the points of its image
(`ContinuousMap.isWeakHomotopyEquivalence_of_totallyDisconnectedSpace`). Taking for `X` the path
components of `Y` with the discrete topology, this says that a space whose path components are
weakly contractible is weakly equivalent to the discrete space of its path components.

## Main results

* `HomotopyGroup.subsingleton_of_totallyDisconnectedSpace`: `π_n(X, x)` is trivial for a totally
  disconnected space `X` and `n ≥ 1`.
* `ContinuousMap.isWeakHomotopyEquivalence_of_totallyDisconnectedSpace`: a map from a totally
  disconnected space meeting each path component of the target exactly once, at points where the
  positive-dimensional homotopy groups vanish, is a weak homotopy equivalence.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 4.1.
-/

public section

open scoped unitInterval Topology Topology.Homotopy
open Topology.Homotopy

namespace HomotopyGroup

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- In positive dimensions, every homotopy group of a totally disconnected space is a
subsingleton: a generalized loop is constant, since the cube is connected, and it sends the
nonempty boundary of the cube to the base point. -/
instance subsingleton_of_totallyDisconnectedSpace [Nonempty N] [TotallyDisconnectedSpace X] :
    Subsingleton (HomotopyGroup N X x) := by
  -- A point of the boundary of the cube, at which every generalized loop takes the value `x`.
  have hb : (fun _ ↦ 0 : I^N) ∈ Cube.boundary N := ⟨Classical.arbitrary N, Or.inl rfl⟩
  have hconst (p : Ω^ N X x) (y : I^N) : p y = x := by
    have hpre := (isPreconnected_univ (α := I^N)).image p p.1.continuous.continuousOn
    exact (hpre.subsingleton (Set.mem_image_of_mem p (Set.mem_univ y))
      (Set.mem_image_of_mem p (Set.mem_univ _))).trans (GenLoop.boundary p _ hb)
  exact ⟨fun a b ↦ Quotient.inductionOn₂ a b fun f g ↦
    congrArg _ (GenLoop.ext f g fun y ↦ (hconst f y).trans (hconst g y).symm)⟩

end HomotopyGroup

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- **A map out of a totally disconnected space onto the path components.** Let `f : X → Y` be a
map from a totally disconnected space which meets every path component of `Y`, and meets each of
them at most once. If the positive-dimensional homotopy groups of `Y` vanish at the points of the
image of `f`, then `f` is a weak homotopy equivalence. -/
theorem isWeakHomotopyEquivalence_of_totallyDisconnectedSpace [TotallyDisconnectedSpace X]
    (f : C(X, Y)) (hsurj : ∀ y, ∃ x, Joined (f x) y) (hinj : ∀ a b, Joined (f a) (f b) → a = b)
    (hY : ∀ (n : ℕ) (x : X), Subsingleton (π_ (n + 1) Y (f x))) : f.IsWeakHomotopyEquivalence :=
  isWeakHomotopyEquivalence_iff_joined.2 ⟨hsurj, fun a b h ↦ hinj a b h ▸ Joined.refl a,
    fun n x ↦ ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun _ ↦ ⟨1, (hY n x).elim _ _⟩⟩⟩

end ContinuousMap
