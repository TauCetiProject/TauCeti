/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction
public import TauCeti.AlgebraicTopology.Quasicategory.HomotopyCategory
public import TauCeti.AlgebraicTopology.SimplicialSet.StrictSegal

/-!
# The essential image of the nerve

A simplicial set is isomorphic to the nerve of a category exactly when it is strict Segal
(`SSet.mem_essImage_nerveFunctor_iff`): nerves are strict Segal, and conversely a strict Segal
simplicial set `X` is the nerve of its homotopy category `X.HomotopyCategory`. Equivalently, the
unit `X ⟶ nerve X.HomotopyCategory` of Mathlib's adjunction `nerveAdjunction` is an isomorphism
exactly when `X` is strict Segal (`SSet.isIso_nerveAdjunction_unit_app_iff`).

The point is that the morphisms of the homotopy category of a strict Segal simplicial set are
exactly its edges (`SSet.HomotopyCategory.homMk_bijective`). A strict Segal simplicial set is a
quasicategory (Mathlib's `SSet.StrictSegal.quasicategory'`), so every morphism of its homotopy
category is represented by an edge (`SSet.HomotopyCategory.homMk_surjective`), and two edges that
represent the same morphism are related by a triangle whose spine is an identity followed by the
first edge (`SSet.HomotopyCategory.homMk_eq_homMk_iff`). In a strict Segal simplicial set that
triangle is degenerate, so the two edges are equal.

Hence the morphism from the `2`-truncation of `X` to the `2`-truncated nerve of its homotopy
category that corresponds to the identity functor under Mathlib's
`SSet.Truncated.HomotopyCategory.functorEquiv` is bijective on edges, so it is an isomorphism
(`SSet.Truncated.isIso_of_bijective_app_one`). Strict Segal simplicial sets and nerves are
`2`-coskeletal, which extends the isomorphism to all dimensions.

## Main results

* `SSet.HomotopyCategory.homMk_bijective`: in a strict Segal simplicial set, the edges from `x` to
  `y` are the morphisms from `x` to `y` in the homotopy category.
* `SSet.isIso_homToNerveMk_id`: for strict Segal `X`, the morphism from the `2`-truncation of `X`
  to the `2`-truncated nerve of `X.HomotopyCategory` given by the identity functor is an
  isomorphism.
* `SSet.mem_essImage_nerveFunctor_iff`: a simplicial set is isomorphic to the nerve of a category
  exactly when it is strict Segal.
* `SSet.isIso_nerveAdjunction_unit_app_iff`: the unit of `nerveAdjunction` at `X` is an isomorphism
  exactly when `X` is strict Segal.

## References

* G. Segal, *Classifying spaces and spectral sequences*, Publ. Math. IHÉS 34 (1968), 105--112.
-/

public section

open CategoryTheory Simplicial SimplexCategory.Truncated

universe u

namespace SSet

variable {X : SSet.{u}} [X.IsStrictSegal]

namespace HomotopyCategory

/-- In a strict Segal simplicial set, two parallel edges representing the same morphism of the
homotopy category are equal. -/
lemma homMk_injective {x y : X _⦋0⦌} :
    Function.Injective (homMk : Edge x y → (mk x ⟶ mk y)) := fun e e' h ↦
  (Edge.CompStruct.idComp e).eq_of_isStrictSegal ((homMk_eq_homMk_iff e e').1 h).some

/-- In a strict Segal simplicial set, the edges from `x` to `y` are exactly the morphisms from `x`
to `y` in the homotopy category. -/
theorem homMk_bijective {x y : X _⦋0⦌} :
    Function.Bijective (homMk : Edge x y → (mk x ⟶ mk y)) :=
  ⟨homMk_injective, homMk_surjective⟩

/-- In a strict Segal simplicial set, two edges define the same arrow of the homotopy category
exactly when they are equal as `1`-simplices. -/
lemma arrowMk_homMk_eq_arrowMk_homMk_iff {x y x' y' : X _⦋0⦌} {e : Edge x y}
    {e' : Edge x' y'} : Arrow.mk (homMk e) = Arrow.mk (homMk e') ↔ e.edge = e'.edge := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨h₁, h₂, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 h
    obtain rfl : x = x' := congr_arg objEquiv h₁
    obtain rfl : y = y' := congr_arg objEquiv h₂
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at h
    rw [homMk_injective h]
  · exact Truncated.HomotopyCategory.congr_arrowMk_homMk e.toTruncated e'.toTruncated h

end HomotopyCategory

open HomotopyCategory in
/-- For a strict Segal simplicial set `X`, the morphism from the `2`-truncation of `X` to the
`2`-truncated nerve of its homotopy category corresponding to the identity functor is an
isomorphism. -/
instance isIso_homToNerveMk_id :
    IsIso (Truncated.HomotopyCategory.homToNerveMk (𝟭 X.HomotopyCategory)) := by
  refine Truncated.isIso_of_bijective_app_one (n := 1) _ ⟨fun s t h ↦ ?_, fun A ↦ ?_⟩
  · -- Mathlib's `homToNerveMk_app_one` would apply here, but its statement mentions an auxiliary
    -- proof private to its module, which the kernel rejects outside Mathlib.
    replace h :=
      (Truncated.HomotopyCategory.homToNerveMk_app_edge _ (Edge.mk' s).toTruncated).symm.trans
        (h.trans (Truncated.HomotopyCategory.homToNerveMk_app_edge _ (Edge.mk' t).toTruncated))
    exact (arrowMk_homMk_eq_arrowMk_homMk_iff (e := Edge.mk' s) (e' := Edge.mk' t)).1
      (congr_arg ComposableArrows.arrowEquiv h)
  · obtain ⟨x, y, f, rfl⟩ := ComposableArrows.mk₁_surjective A
    induction x with | mk x => ?_
    induction y with | mk y => ?_
    obtain ⟨e, rfl⟩ := homMk_surjective f
    exact ⟨e.edge, Truncated.HomotopyCategory.homToNerveMk_app_edge _ e.toTruncated⟩

/-- A simplicial set is isomorphic to the nerve of a category exactly when it is strict Segal. See
`SSet.isIso_nerveAdjunction_unit_app_iff` for the isomorphism `X ≅ nerve X.HomotopyCategory`. -/
@[simp]
theorem mem_essImage_nerveFunctor_iff {X : SSet.{u}} :
    nerveFunctor.{u, u}.essImage X ↔ X.IsStrictSegal := by
  refine ⟨fun ⟨C, ⟨e⟩⟩ ↦ IsStrictSegal.of_iso (X := nerve C) e,
    fun _ ↦ ⟨Cat.of X.HomotopyCategory, ⟨?_⟩⟩⟩
  -- Both sides are `2`-coskeletal, and their `2`-truncations are identified by the unit.
  exact (SimplicialObject.isoCoskOfIsCoskeletal X 2 ≪≫
    (Truncated.cosk 2).mapIso
      (asIso (Truncated.HomotopyCategory.homToNerveMk (𝟭 X.HomotopyCategory))) ≪≫
    (Nerve.cosk₂Iso.app (Cat.of X.HomotopyCategory)).symm).symm

/-- The unit `X ⟶ nerve X.HomotopyCategory` of the adjunction between simplicial sets and
categories is an isomorphism exactly when `X` is strict Segal. -/
theorem isIso_nerveAdjunction_unit_app_iff {X : SSet.{u}} :
    IsIso (nerveAdjunction.unit.app X) ↔ X.IsStrictSegal :=
  nerveAdjunction.isIso_unit_app_iff_mem_essImage.trans mem_essImage_nerveFunctor_iff

/-- The unit `X ⟶ nerve X.HomotopyCategory` of the adjunction between simplicial sets and
categories is an isomorphism when `X` is strict Segal. -/
instance isIso_nerveAdjunction_unit_app : IsIso (nerveAdjunction.unit.app X) :=
  isIso_nerveAdjunction_unit_app_iff.2 ‹_›

end SSet
