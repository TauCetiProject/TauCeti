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

Connected components commute with finite products: two vertices of `X ⊗ Y` lie in the same
component exactly when both of their coordinates do (`SSet.π₀ProdEquiv`). Hence the functor
`SSet.π₀Functor` preserves finite products and is monoidal for the Cartesian monoidal structures,
with `μ` sending a pair of components to the component of the pair (`SSet.μ_π₀Functor_mk`). This is
what makes `π₀` of the mapping simplicial sets of a simplicially enriched category into a category.

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

section Prod

open Limits MonoidalCategory CartesianMonoidalCategory

variable (X Y : SSet.{u})

/-- The connected components of a product of simplicial sets are the pairs of connected components
of the factors. -/
def π₀ProdEquiv : π₀ (X ⊗ Y) ≃ π₀ X × π₀ Y where
  toFun c := (mapπ₀ (fst X Y) c, mapπ₀ (snd X Y) c)
  invFun c := π₀.lift (fun x ↦ π₀.lift (fun y ↦ π₀.mk (X := X ⊗ Y) (x, y))
      (fun _ _ e ↦ π₀.sound (Edge.mk ((Edge.id x).edge, e.edge)
        (Prod.ext (Edge.id x).src_eq e.src_eq) (Prod.ext (Edge.id x).tgt_eq e.tgt_eq))) c.2)
    (fun _ _ e ↦ by
      induction c.2 using π₀.rec with | mk y => ?_
      exact π₀.sound (Edge.mk (e.edge, (Edge.id y).edge)
        (Prod.ext e.src_eq (Edge.id y).src_eq) (Prod.ext e.tgt_eq (Edge.id y).tgt_eq))) c.1
  left_inv c := by
    induction c using π₀.rec with | mk z => rfl
  right_inv c := by
    obtain ⟨a, b⟩ := c
    induction a using π₀.rec with | mk x => ?_
    induction b using π₀.rec with | mk y => rfl

/-- The component of a vertex of a product is the pair of components of its coordinates. -/
@[simp]
lemma π₀ProdEquiv_mk (z : (X ⊗ Y) _⦋0⦌) :
    π₀ProdEquiv X Y (π₀.mk z) = (π₀.mk z.1, π₀.mk z.2) :=
  (rfl)

/-- A pair of components is the component of the pair of their representatives. -/
@[simp]
lemma π₀ProdEquiv_symm_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    (π₀ProdEquiv X Y).symm (π₀.mk x, π₀.mk y) = π₀.mk (X := X ⊗ Y) (x, y) :=
  (rfl)

/-- The comparison map `π₀ (X ⊗ Y) ⟶ π₀ X ⊗ π₀ Y` is an isomorphism. -/
instance isIso_prodComparison_π₀Functor :
    IsIso (CartesianMonoidalCategory.prodComparison π₀Functor X Y) := by
  rw [isIso_iff_bijective]
  have : ⇑(ConcreteCategory.hom (CartesianMonoidalCategory.prodComparison π₀Functor X Y)) =
      π₀ProdEquiv X Y := by
    funext c
    induction c using π₀.rec
    rfl
  exact this ▸ (π₀ProdEquiv X Y).bijective

/-- The terminal simplicial set has a single connected component. -/
instance isIso_terminalComparison_π₀Functor :
    IsIso (CartesianMonoidalCategory.terminalComparison π₀Functor.{u}) := by
  rw [isIso_iff_bijective]
  refine ⟨fun a b _ ↦ ?_, fun _ ↦ ⟨π₀.mk PUnit.unit, rfl⟩⟩
  induction a using π₀.rec
  induction b using π₀.rec
  rfl

/-- Taking connected components preserves finite products of simplicial sets. -/
instance π₀Functor.preservesFiniteProducts : PreservesFiniteProducts π₀Functor.{u} :=
  have := preservesLimitsOfShape_discrete_walkingPair_of_isIso_prodComparison π₀Functor.{u}
  have := preservesLimit_empty_of_isIso_terminalComparison π₀Functor.{u}
  have := preservesLimitsOfShape_pempty_of_preservesTerminal π₀Functor.{u}
  .of_preserves_binary_and_terminal _

/-- The functor of connected components is monoidal for the Cartesian monoidal structures. -/
noncomputable instance π₀Functor.monoidal : π₀Functor.{u}.Monoidal := .ofChosenFiniteProducts _

/-- The terminal simplicial set has at most one connected component. -/
instance : Subsingleton (π₀ (𝟙_ SSet.{u})) where
  allEq a b := by
    induction a using π₀.rec
    induction b using π₀.rec
    rfl

/-- The unit of `π₀Functor` is the unique component of the terminal simplicial set. -/
@[simp]
lemma ε_π₀Functor_apply (x : 𝟙_ (Type u)) :
    Functor.LaxMonoidal.ε π₀Functor.{u} x = π₀.mk (X := 𝟙_ SSet.{u}) PUnit.unit :=
  Subsingleton.elim (α := π₀ (𝟙_ SSet.{u})) _ _

/-- The tensorator of `π₀Functor` sends a pair of components to the component of the pair. -/
@[simp]
lemma μ_π₀Functor_mk (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    Functor.LaxMonoidal.μ π₀Functor X Y (π₀.mk x, π₀.mk y) = π₀.mk (X := X ⊗ Y) (x, y) := by
  -- Both sides of `lift_μ` unfold, at the component of `(x, y)`, to the two sides of the goal.
  exact ConcreteCategory.congr_hom (Functor.Monoidal.lift_μ π₀Functor (fst X Y) (snd X Y))
    (π₀.mk (X := X ⊗ Y) (x, y))

end Prod

end SSet
