/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.Flasque.Locality
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.Topology.Sheaves.Limits

/-!
# Finite products of flasque sheaves and local twists

A presheaf is flasque when all of its restriction maps are epimorphisms. This file shows that
flasqueness is stable under finite products, for presheaves and sheaves valued in a category with
zero morphisms and finite biproducts, such as abelian groups or modules over a ring. The
restriction maps of a product of presheaves are the products of the restriction maps, and in such a
category a finite product of epimorphisms is an epimorphism (`CategoryTheory.Limits.Pi.map_epi`).

Combined with the locality of flasqueness in the form `TopCat.Sheaf.isFlasque_of_locally_iso` (a
sheaf which is locally isomorphic to a flasque sheaf is flasque), this gives the criterion used for
twisted and vector-bundle-valued coefficients: a sheaf which is locally isomorphic to a finite
power of a flasque sheaf `F`, such as the tensor product of `F` with a locally constant sheaf which
is locally free of finite rank, is flasque (`TopCat.Sheaf.isFlasque_of_locally_iso_pi`).

## Main declarations

* `TopCat.Presheaf.isFlasque_piObj`: a finite product of flasque presheaves is flasque;
* `TopCat.Sheaf.isFlasque_piObj`: a finite product of flasque sheaves is flasque;
* `TopCat.Sheaf.isFlasque_of_locally_iso_pi`: a sheaf which is locally isomorphic to a finite
  power of a flasque sheaf is flasque.

## References

* R. Godement, *Topologie algébrique et théorie des faisceaux*, Chapitre II, §3.
* G. E. Bredon, *Sheaf Theory*, Chapter II, §5.
-/

public section

universe u w

open CategoryTheory Limits Opposite TopologicalSpace Topology

namespace TopCat

variable {X : TopCat.{u}}

namespace Presheaf

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
  {J : Type w} [Finite J]

/-- A finite product of flasque presheaves valued in a category with zero morphisms and finite
biproducts is flasque. -/
instance isFlasque_piObj (F : J → Presheaf C X) [∀ j, (F j).IsFlasque] : (∏ᶜ F).IsFlasque where
  epi {U V} i := by
    -- Under `piObjIso`, the restriction map of the product is the product of restriction maps.
    have : (∏ᶜ F).map i =
        (piObjIso F U).hom ≫ Limits.Pi.map (fun j ↦ (F j).map i) ≫ (piObjIso F V).inv := by
      rw [← Category.assoc, Iso.eq_comp_inv]
      ext j
      simp [piObjIso_hom_comp_π]
    rw [this]
    infer_instance

end Presheaf

namespace Sheaf

/-- A finite product of flasque sheaves valued in a category with zero morphisms and finite
biproducts is flasque. -/
instance isFlasque_piObj {C : Type*} [Category* C] [HasZeroMorphisms C] [HasFiniteBiproducts C]
    {J : Type w} [Finite J] (F : J → Sheaf C X) [∀ j, (F j).IsFlasque] : (∏ᶜ F).IsFlasque :=
  -- Products of sheaves are computed in presheaves.
  have : (∏ᶜ fun j ↦ (Sheaf.forget C X).obj (F j)).IsFlasque :=
    Presheaf.isFlasque_piObj fun j ↦ (F j).obj
  .of_iso (PreservesProduct.iso (Sheaf.forget C X) F).symm

section Locality

variable {C : Type*} [Category.{u} C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]
  [(CategoryTheory.forget C).PreservesEpimorphisms]

include FC CC

/-- A sheaf which is locally isomorphic to a finite power of a flasque sheaf `F` is flasque: if
every point has an open neighbourhood `W` on which the sheaf is isomorphic to `(F|_W)ⁿ` for some
`n`, then it is flasque. -/
theorem isFlasque_of_locally_iso_pi [HasZeroMorphisms C] [HasFiniteBiproducts C] (F : Sheaf C X)
    [F.IsFlasque] (G : Sheaf C X)
    (h : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∃ n : ℕ,
      Nonempty ((W.isOpenEmbedding.sheafPullback C).obj G ≅
        ∏ᶜ fun _ : Fin n ↦ (W.isOpenEmbedding.sheafPullback C).obj F)) :
    G.IsFlasque :=
  G.isFlasque_of_locally_iso fun x ↦
    have ⟨W, hxW, _, he⟩ := h x
    ⟨W, hxW, _, inferInstance, he⟩

end Locality

end Sheaf

end TopCat
