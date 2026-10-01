/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor

/-!
# Compatible families over a terminal object

For a family of maps `π i : X i ⟶ B` to a terminal object `B`, every pair of maps into two members
of the family agrees after composing with `π`. So a family of elements `x i ∈ P(X i)` of a presheaf
of types `P` is compatible exactly when, for every pair `k : Fin 2 → I`, the restrictions of
`x (k 0)` and `x (k 1)` to the product of `X (k 0)` and `X (k 1)` agree. This is the form the
compatibility condition takes in degree `1` of the Čech complex.

## Main results

* `CategoryTheory.Presieve.Arrows.compatible_iff_of_isTerminal`: the characterisation above.
-/

public section

universe w v u t

open CategoryTheory Limits Opposite

namespace CategoryTheory.Presieve.Arrows

variable {C : Type u} [Category.{v} C] [HasProductsOfShape (Fin 2) C] {P : Cᵒᵖ ⥤ Type w}
  {I : Type t} {X : I → C} {B : C}

/-- A family of elements indexed by maps `π i : X i ⟶ B` to a terminal object is compatible
exactly when its restrictions agree on the product `∏ᶜ fun j ↦ X (k j)` of every pair of members
`k : Fin 2 → I`. Unlike `Presieve.Arrows.pullbackCompatible_iff`, it needs only products of two
objects, and the products are indexed as in the Čech complex `CategoryTheory.cechComplexFunctor`. -/
theorem compatible_iff_of_isTerminal (hB : IsTerminal B) (π : ∀ i, X i ⟶ B)
    (x : ∀ i, P.obj (op (X i))) :
    Compatible P π x ↔ ∀ k : Fin 2 → I, P.map (Pi.π (fun j ↦ X (k j)) 1).op (x (k 1)) =
      P.map (Pi.π (fun j ↦ X (k j)) 0).op (x (k 0)) := by
  refine ⟨fun h k ↦ h (k 1) (k 0) _ _ _ (hB.hom_ext _ _), fun h i j Z gi gj _ ↦ ?_⟩
  -- restrict the condition for the pair `(j, i)` along the map into the product given by `gj`, `gi`
  have := congrArg (P.map (Pi.lift (Fin.cons gj fun _ ↦ gi)).op) (h (Fin.cons j fun _ ↦ i))
  simp only [← Functor.map_comp_apply, ← op_comp, Pi.lift_comp_π] at this
  exact this

end CategoryTheory.Presieve.Arrows
