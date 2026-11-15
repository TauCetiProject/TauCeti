/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.FundamentalGroupoid.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.ULift

/-!
# Fundamental groupoid and universe lifts of simplicial sets

Lifting vertices, edges, and composition `2`-simplices along `SSet.uliftFunctor` yields
`SSet.Edge.ulift`, `SSet.Edge.CompStruct.ulift`, and the canonical functor
`SSet.uliftFundamentalGroupoid X : SSet.FundamentalGroupoid X ⥤`
`SSet.FundamentalGroupoid (SSet.uliftFunctor.obj X)`.

## Main declarations

* `SSet.Edge.ulift`: lift of an edge of `X` to an edge of `SSet.uliftFunctor.obj X`.
* `SSet.Edge.CompStruct.ulift`: lift of a composition `2`-simplex to `SSet.uliftFunctor.obj X`.
* `SSet.uliftFundamentalGroupoid`: canonical functor
  `SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid (SSet.uliftFunctor.obj X)`.

## References

* P. G. Goerss and J. F. Jardine, *Simplicial Homotopy Theory*, Progress in Mathematics 174,
  Birkhäuser, 1999, Section I.7.
-/

public section

open CategoryTheory Simplicial

namespace SSet

universe w u'

/-- Lifting an edge `e : X.Edge x₀ x₁` to an edge of `uliftFunctor.{w, u'}.obj X`. -/
def Edge.ulift {X : SSet.{u'}} {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (uliftFunctor.{w, u'}.obj X).Edge (X.uliftFunctorObjEquiv (Opposite.op ⦋0⦌) x₀)
      (X.uliftFunctorObjEquiv (Opposite.op ⦋0⦌) x₁) where
  edge := X.uliftFunctorObjEquiv (Opposite.op ⦋1⦌) e.edge
  src_eq := (uliftFunctor_obj_map_uliftFunctorObjEquiv.{w} X (SimplexCategory.δ 1).op e.edge).trans
    (congrArg (X.uliftFunctorObjEquiv.{w} (Opposite.op ⦋0⦌)) e.src_eq)
  tgt_eq := (uliftFunctor_obj_map_uliftFunctorObjEquiv.{w} X (SimplexCategory.δ 0).op e.edge).trans
    (congrArg (X.uliftFunctorObjEquiv.{w} (Opposite.op ⦋0⦌)) e.tgt_eq)

@[simp]
lemma Edge.ulift_edge {X : SSet.{u'}} {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    e.ulift.{w}.edge = X.uliftFunctorObjEquiv (Opposite.op ⦋1⦌) e.edge := (rfl)

/-- Lifting a composition `2`-simplex `h : Edge.CompStruct e₀₁ e₁₂ e₀₂` to
`uliftFunctor.{w, u'}.obj X`. -/
def Edge.CompStruct.ulift {X : SSet.{u'}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    Edge.CompStruct e₀₁.ulift.{w} e₁₂.ulift.{w} e₀₂.ulift.{w} where
  simplex := X.uliftFunctorObjEquiv (Opposite.op ⦋2⦌) h.simplex
  d₂ := (uliftFunctor_obj_map_uliftFunctorObjEquiv.{w} X (SimplexCategory.δ 2).op h.simplex).trans
    (congrArg (X.uliftFunctorObjEquiv.{w} (Opposite.op ⦋1⦌)) h.d₂)
  d₀ := (uliftFunctor_obj_map_uliftFunctorObjEquiv.{w} X (SimplexCategory.δ 0).op h.simplex).trans
    (congrArg (X.uliftFunctorObjEquiv.{w} (Opposite.op ⦋1⦌)) h.d₀)
  d₁ := (uliftFunctor_obj_map_uliftFunctorObjEquiv.{w} X (SimplexCategory.δ 1).op h.simplex).trans
    (congrArg (X.uliftFunctorObjEquiv.{w} (Opposite.op ⦋1⦌)) h.d₁)

@[simp]
lemma Edge.CompStruct.ulift_simplex {X : SSet.{u'}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (h : Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    h.ulift.{w}.simplex = X.uliftFunctorObjEquiv (Opposite.op ⦋2⦌) h.simplex := (rfl)

-- `@[expose]` is required by `module` so dependent morphism equalities over
-- `(uliftFundamentalGroupoid X).obj` typecheck in downstream public statements.
/-- The canonical functor
`SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid (uliftFunctor.{w, u'}.obj X)` induced by
lifting vertices and edges along `uliftFunctor`. -/
@[expose, implicit_reducible]
def uliftFundamentalGroupoid (X : SSet.{u'}) :
    SSet.FundamentalGroupoid X ⥤ SSet.FundamentalGroupoid (uliftFunctor.{w, u'}.obj X) :=
  FundamentalGroupoid.desc (fun x ↦ .mk (X.uliftFunctorObjEquiv (Opposite.op ⦋0⦌) x))
    (fun e ↦ FundamentalGroupoid.homMk e.ulift)
    (fun h ↦ h.ulift.homMk_comp)

@[simp]
lemma uliftFundamentalGroupoid_obj_mk (X : SSet.{u'}) (x : X _⦋0⦌) :
    (uliftFundamentalGroupoid.{w} X).obj (.mk x) =
      .mk (X.uliftFunctorObjEquiv (Opposite.op ⦋0⦌) x) := (rfl)

@[simp]
lemma uliftFundamentalGroupoid_map_homMk (X : SSet.{u'}) {x y : X _⦋0⦌} (e : X.Edge x y) :
    (uliftFundamentalGroupoid.{w} X).map (FundamentalGroupoid.homMk e) =
      FundamentalGroupoid.homMk e.ulift :=
  FundamentalGroupoid.desc_map_homMk _ _ (fun h ↦ h.ulift.homMk_comp) e

end SSet
