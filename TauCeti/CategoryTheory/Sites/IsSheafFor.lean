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
# Compatible families over a terminal object, and over a meet-semilattice

For a family of maps `π i : X i ⟶ B` to a terminal object `B`, every pair of maps into two members
of the family agrees after composing with `π`. So a family of elements `x i ∈ P(X i)` of a presheaf
of types `P` is compatible exactly when, for every pair `k : Fin 2 → I`, the restrictions of
`x (k 0)` and `x (k 1)` to the product of `X (k 0)` and `X (k 1)` agree. This is the form the
compatibility condition takes in degree `1` of the Čech complex.

In a meet-semilattice, such as the opens of a topological space, there is at most one morphism
between two objects, and two members `X i`, `X j` of a family have the greatest lower bound
`X i ⊓ X j`. So a family of elements is compatible exactly when the restrictions of `x i` and
`x j` to `X i ⊓ X j` agree.

## Main results

* `CategoryTheory.Presieve.Arrows.compatible_iff_of_isTerminal`: the characterisation above.
* `CategoryTheory.Presieve.Arrows.compatible_homOfLE_iff`: compatibility in a meet-semilattice is
  agreement on pairwise meets.
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

section SemilatticeInf

variable {X : Type u} [SemilatticeInf X] {P : Xᵒᵖ ⥤ Type w} {I : Type t} {Y : I → X} {B : X}

/-- **Compatibility in a meet-semilattice is agreement on pairwise meets.** For members `Y i ≤ B`
of a meet-semilattice, such as opens of a topological space, a family of elements
`x i ∈ P(Y i)` of a presheaf of types is compatible exactly when, for all `i` and `j`, the
restrictions of `x i` and `x j` to `Y i ⊓ Y j` agree. -/
theorem compatible_homOfLE_iff (hY : ∀ i, Y i ≤ B) (x : ∀ i, P.obj (op (Y i))) :
    Compatible P (fun i ↦ homOfLE (hY i)) x ↔ ∀ i j,
      P.map (homOfLE inf_le_left : Y i ⊓ Y j ⟶ Y i).op (x i) =
        P.map (homOfLE inf_le_right : Y i ⊓ Y j ⟶ Y j).op (x j) := by
  refine ⟨fun h i j ↦ h i j _ _ _ (Subsingleton.elim _ _), fun h i j Z gi gj _ ↦ ?_⟩
  -- both maps out of `Z` factor through `Y i ⊓ Y j`, and morphisms in a preorder are unique
  have hZ : Z ≤ Y i ⊓ Y j := le_inf gi.le gj.le
  rw [show gi = homOfLE hZ ≫ homOfLE inf_le_left from Subsingleton.elim _ _,
    show gj = homOfLE hZ ≫ homOfLE inf_le_right from Subsingleton.elim _ _, op_comp, op_comp,
    Functor.map_comp_apply, Functor.map_comp_apply, h i j]

end SemilatticeInf

end CategoryTheory.Presieve.Arrows
