/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Homotopy
public import Mathlib.AlgebraicTopology.SimplicialSet.PiZero

/-!
# Connected components of simplicial sets

Complements to Mathlib's connected components `SSet.π₀` of a simplicial set. Homotopic maps
induce the same map on connected components (`SSet.Homotopy.mapπ₀_eq`), so the comparison maps
of a simplicial homotopy equivalence induce mutually inverse bijections on them. The connected
components of a discrete simplicial set are its vertices (`SSet.constπ₀Equiv`), lifting a simplicial
set to a larger universe does not change its connected components (`SSet.π₀UliftEquiv`), and a
simplicial set whose vertices form a `w`-small type has `w`-small connected components.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Chapter I, §§6–7.
-/

public section

universe w v u

open CategoryTheory Simplicial

namespace SSet

variable {X Y : SSet.{u}}

/-- Homotopic maps of simplicial sets induce the same map on connected components: the homotopy
provides an edge from the image of each vertex under the first map to its image under the
second. -/
lemma Homotopy.mapπ₀_eq {f g : X ⟶ Y} (H : Homotopy f g) : mapπ₀ f = mapπ₀ g := by
  funext c
  obtain ⟨x, rfl⟩ := π₀.mk_surjective c
  exact π₀.sound (Edge.ofSimplicialObjectHomotopy H.toSimplicialObjectHomotopy x)

/-- A simplicial set whose vertices form a `w`-small type has `w`-small connected components. -/
instance small_π₀ [Small.{w} (X _⦋0⦌)] : Small.{w} (π₀ X) :=
  small_of_surjective π₀.mk_surjective

variable (ι : Type u)

/-- The connected components of the discrete simplicial set on `ι` are the elements of `ι`: its
faces are identities, so an edge joins a vertex only to itself. -/
def constπ₀Equiv : π₀ ((Functor.const SimplexCategoryᵒᵖ).obj ι) ≃ ι where
  toFun := π₀.lift id fun _ _ e ↦ e.src_eq.symm.trans e.tgt_eq
  invFun := π₀.mk (X := (Functor.const SimplexCategoryᵒᵖ).obj ι)
  left_inv c := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective c
    rfl
  right_inv _ := rfl

/-- The component of a vertex of a discrete simplicial set is that vertex. -/
@[simp]
lemma constπ₀Equiv_mk (i : ι) :
    constπ₀Equiv ι (π₀.mk (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i) = i :=
  (rfl)

/-- An element of `ι` is the component of the corresponding vertex. -/
@[simp]
lemma constπ₀Equiv_symm_apply (i : ι) :
    (constπ₀Equiv ι).symm i = π₀.mk (X := (Functor.const SimplexCategoryᵒᵖ).obj ι) i :=
  (rfl)

variable (X) in
/-- Lifting a simplicial set to a larger universe does not change its connected components. -/
def π₀UliftEquiv : π₀ (uliftFunctor.{v}.obj X) ≃ π₀ X where
  toFun := π₀.lift (fun x ↦ π₀.mk x.down) fun _ _ e ↦
    π₀.sound (Edge.mk e.edge.down (congrArg ULift.down e.src_eq)
      (congrArg ULift.down e.tgt_eq))
  invFun := π₀.lift (fun x ↦ π₀.mk (ULift.up x)) fun _ _ e ↦
    π₀.sound (Edge.mk (ULift.up e.edge) (congrArg ULift.up e.src_eq)
      (congrArg ULift.up e.tgt_eq))
  left_inv c := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective c
    rfl
  right_inv c := by
    obtain ⟨x, rfl⟩ := π₀.mk_surjective c
    rfl

/-- The component of a lifted vertex corresponds to the component of the vertex. -/
@[simp]
lemma π₀UliftEquiv_mk (x : (uliftFunctor.{v}.obj X) _⦋0⦌) :
    π₀UliftEquiv X (π₀.mk x) = π₀.mk x.down :=
  (rfl)

/-- The component of a vertex corresponds to the component of the lifted vertex. -/
@[simp]
lemma π₀UliftEquiv_symm_mk (x : X _⦋0⦌) :
    (π₀UliftEquiv X).symm (π₀.mk x) = π₀.mk (X := uliftFunctor.{v}.obj X) (ULift.up x) :=
  (rfl)

end SSet
