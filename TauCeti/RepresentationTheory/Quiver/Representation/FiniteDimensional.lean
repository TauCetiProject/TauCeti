/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Representation.OfModule

/-!
# Finite-dimensional quiver representations

A representation of a quiver is **pointwise finite-dimensional** when the vector space it puts at
every vertex is finite-dimensional. This file defines that property, `TauCeti.IsFinDim`, proves
that it transports along an isomorphism, that over a finite quiver the morphisms between two such
representations form a finite-dimensional space, and shows that a path algebra module
finite-dimensional over the base field gives such a representation.

## Main definitions

* `TauCeti.IsFinDim`: a representation is finite-dimensional at every vertex.

## Main results

* `TauCeti.IsFinDim.of_iso`: pointwise finite-dimensionality transports along an isomorphism.
* `TauCeti.IsFinDim.finiteDimensional_hom`: over a finite quiver, the morphisms between two
  pointwise finite-dimensional representations form a finite-dimensional space.
* `TauCeti.isFinDim_quiverRepFunctor_obj`: finite-dimensionality passes from a module to its
  associated representation.

## Implementation notes

`IsFinDim` is stated vertex by vertex rather than as a single finiteness of the total space: the
category of representations is a functor category, with no ambient module to be finite over, and
over an infinite vertex set the two conditions genuinely differ. Over a finite quiver they agree,
and that is the setting the theory is meant for. `TauCeti.IsFinDim.finiteDimensional_hom` is where
the finiteness of the vertex set is what makes the difference: a morphism of representations is a
family of linear maps indexed by the vertices, and the space of such families is
finite-dimensional only when there are finitely many vertices.

## References

This implements the `IsFinDim` part of the "finite representation type" item of Layer 5 of
`TauCetiRoadmap/RepresentationTheory/QuiverRepresentations/README.md`; the property itself is
finite-dimensionality of representations, and is used well before that layer's theory.
-/

public section

namespace TauCeti

open CategoryTheory
open scoped ModuleCat

universe u v w t

/-- **Pointwise finite-dimensionality** of a quiver representation: the vector space at every
vertex is finite-dimensional. Over a finite quiver this is total finite-dimensionality, and it is
the finiteness condition under which the indecomposables can be counted; the functor category
itself contains infinite-dimensional objects. -/
def IsFinDim (k : Type u) (Q : Type v) [Field k] [Quiver.{w} Q]
    (M : QuiverRep.{u, v, w, t} k Q) : Prop :=
  ∀ v : Paths Q, FiniteDimensional k (M.obj v)

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The elimination and introduction rule for `TauCeti.IsFinDim`**: it is finite-dimensionality
at every vertex. -/
@[simp]
theorem isFinDim_iff {M : QuiverRep.{u, v, w, t} k Q} :
    IsFinDim k Q M ↔ ∀ v : Paths Q, FiniteDimensional k (M.obj v) :=
  Iff.rfl

/-- Finite-dimensionality at each vertex transports along an isomorphism of representations. -/
theorem IsFinDim.of_iso {M N : QuiverRep.{u, v, w, t} k Q} (h : IsFinDim k Q M) (e : M ≅ N) :
    IsFinDim k Q N := by
  intro v
  have := h v
  exact (e.app v).toLinearEquiv.finiteDimensional

/-- **Morphisms between pointwise finite-dimensional representations of a finite quiver form a
finite-dimensional space.** Taking components embeds `M ⟶ N` into the product over the vertices of
the spaces of linear maps `M.obj v →ₗ[k] N.obj v`, which is finite-dimensional because the vertex
set is finite and each factor is. -/
theorem IsFinDim.finiteDimensional_hom [Finite Q] {M N : QuiverRep.{u, v, w, t} k Q}
    (hM : IsFinDim k Q M) (hN : IsFinDim k Q N) : FiniteDimensional k (M ⟶ N) := by
  -- The objects of `Paths Q` are the vertices of `Q`.
  have : Finite (Paths Q) := inferInstanceAs (Finite Q)
  have (v : Paths Q) : FiniteDimensional k (M.obj v) := hM v
  have (v : Paths Q) : FiniteDimensional k (N.obj v) := hN v
  have (v : Paths Q) : FiniteDimensional k (M.obj v ⟶ N.obj v) :=
    Module.Finite.equiv (ModuleCat.homLinearEquiv (S := k)).symm
  -- Taking components is `k`-linear, because both the addition and the scalar action of the
  -- functor category are defined vertexwise.
  let component : (M ⟶ N) →ₗ[k] (∀ v : Paths Q, (M.obj v ⟶ N.obj v)) :=
    { toFun f := f.app
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  exact Module.Finite.of_injective component fun _ _ h ↦ NatTrans.ext h

variable (k Q) [Finite Q]

/-- A path algebra module finite-dimensional over the base field gives a representation with
finite-dimensional vertex spaces. -/
theorem isFinDim_quiverRepFunctor_obj (M : ModuleCat (pathAlgebra k Q))
    (hM : FiniteDimensional k M) :
    IsFinDim k Q ((quiverRepFunctor k Q).obj M) := by
  have := hM
  rw [isFinDim_iff]
  intro v
  -- The objects of `Paths Q` are the vertices of `Q`.
  change Q at v
  rw [quiverRepFunctor_obj, quiverRepOfModule_obj]
  infer_instance

end TauCeti
