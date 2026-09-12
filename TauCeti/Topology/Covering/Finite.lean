/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Covering.Category
public import TauCeti.Topology.Homotopy.Monodromy.Basic

/-!
# Finite covering spaces

A covering space is *finite* when all of its fibres are finite. This file records that condition
as a property of an object of `TopCat / X` and names the resulting full subcategory
`TauCeti.FiniteCoveringSpace X`, as an instance of `TauCeti.CoveringSpace.FullSubcategory`.

That general type carries the shared API, which is used here rather than restated; the module
docstring of `TauCeti.Topology.Covering.Category` says how its members are named. What this file
adds is the finiteness property, the constructor family and the inclusion functor — which are
given again because they pin `P` down to finiteness — and
`TauCeti.FiniteCoveringSpace.finite_fiber`, recording finiteness of every fibre as an instance.

Finiteness of all fibres is one condition rather than infinitely many as soon as the base is path
connected: monodromy along a path is a bijection between the fibres over its endpoints, so the
fibres over any two points of a path component are in bijection. That is
`TauCeti.coveringFiberEquiv`, from `TauCeti.Topology.Homotopy.Monodromy.Basic`, and
`TauCeti.hasFiniteFibers_of_finite_fiber` is the resulting one-point criterion.

Finite covers are the covering-space side of the Galois-category picture: the fibre over a
basepoint is a finite set with an action of `π₁`, and it is only for finite covers that the fibre
functor lands in `FintypeCat`.

## Main declarations

* `TauCeti.Over.hasFiniteFibers` and `TauCeti.Over.hasFiniteFibers_iff`: the property of an
  object of `TopCat / X` that all fibres of its structure morphism are finite, and its
  membership lemma.
* `TauCeti.FiniteCoveringSpace`: finite covering spaces over `X`.
* `TauCeti.FiniteCoveringSpace.mk`, `mk_coe`, `mk_proj`, `forget_obj_mk` and `forget`: the
  constructor, its computation lemmas and the inclusion into all covering spaces. The rest of the
  API is `TauCeti.CoveringSpace.FullSubcategory`'s.
* `TauCeti.FiniteCoveringSpace.finite_fiber`: every fibre of a finite covering space is finite.
* `TauCeti.hasFiniteFibers_of_finite_fiber`: over a path-connected base, one finite fibre makes
  all fibres finite.
-/

public section

universe u v

namespace TauCeti

open CategoryTheory

section Fibers

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X] {p : E → X}

/-- Over a path-connected base, a covering map with one finite fibre has all fibres finite. -/
theorem finite_fiber_of_finite_fiber [PathConnectedSpace X] (hp : IsCoveringMap p) {x₀ : X}
    (h : Finite ↥(p ⁻¹' {x₀})) (x : X) : Finite ↥(p ⁻¹' {x}) :=
  have := h
  Finite.of_equiv _
    (coveringFiberEquiv hp (Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x₀ x)))

end Fibers

namespace Over

/-- The property of an object of `TopCat / X` that all fibres of its structure morphism are
finite. -/
def hasFiniteFibers (X : TopCat.{u}) : ObjectProperty (CategoryTheory.Over X) :=
  fun p => ∀ x : X, Finite ↥(⇑p.hom ⁻¹' {x})

/-- Membership in the finite-fibre property of objects of `TopCat / X`. -/
@[simp]
theorem hasFiniteFibers_iff {X : TopCat.{u}} {p : CategoryTheory.Over X} :
    hasFiniteFibers X p ↔ ∀ x : X, Finite ↥(⇑p.hom ⁻¹' {x}) :=
  Iff.rfl

end Over

/-- The category of finite covering spaces over `X`: covering maps to `X` all of whose fibres are
finite, and continuous maps commuting with the projections to `X`. -/
abbrev FiniteCoveringSpace (X : TopCat.{u}) : Type _ :=
  CoveringSpace.FullSubcategory X (Over.hasFiniteFibers X)

namespace FiniteCoveringSpace

variable {X : TopCat.{u}}

/-- The fully faithful inclusion of finite covering spaces into all covering spaces. -/
abbrev forget (X : TopCat.{u}) : FiniteCoveringSpace X ⥤ CoveringSpace X :=
  CoveringSpace.FullSubcategory.forget X _

/-- Construct a finite covering space from a covering map with finite fibres. -/
def mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) : FiniteCoveringSpace X :=
  CoveringSpace.FullSubcategory.mk p hp (Over.hasFiniteFibers_iff.2 hfin)

@[simp]
theorem mk_coe {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) : (mk p hp hfin : TopCat) = E :=
  -- The `_` is the finiteness proof that `mk` supplies; the generic lemma applies because `mk`
  -- unfolds to the generic constructor. A `rfl` cannot: this theorem is exported, so it may only
  -- unfold definitions whose bodies are exposed, and `mk`'s is not.
  CoveringSpace.FullSubcategory.mk_coe p hp _

@[simp]
theorem mk_proj {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) :
    (mk p hp hfin).proj = eqToHom (mk_coe p hp hfin) ≫ p :=
  CoveringSpace.FullSubcategory.mk_proj p hp _

@[simp]
theorem forget_obj_mk {E : TopCat.{u}} (p : E ⟶ X) (hp : _root_.IsCoveringMap p)
    (hfin : ∀ x : X, Finite ↥(⇑p ⁻¹' {x})) :
    (forget X).obj (mk p hp hfin) = CoveringSpace.mk p hp :=
  CoveringSpace.FullSubcategory.forget_obj_mk p hp _

/-- Every fibre of a finite covering space is finite. -/
instance finite_fiber (p : FiniteCoveringSpace X) (x : X) : Finite ↥(⇑p.proj ⁻¹' {x}) :=
  Over.hasFiniteFibers_iff.1 p.prop_obj x

end FiniteCoveringSpace

/-- **Over a path-connected base one finite fibre makes a covering space finite.** -/
theorem hasFiniteFibers_of_finite_fiber {X : TopCat.{u}} [PathConnectedSpace X]
    (p : CoveringSpace X) (x₀ : X) (h : Finite ↥(⇑p.proj ⁻¹' {x₀})) :
    Over.hasFiniteFibers X p.obj :=
  Over.hasFiniteFibers_iff.2 fun x => finite_fiber_of_finite_fiber p.isCoveringMap_proj h x

end TauCeti
