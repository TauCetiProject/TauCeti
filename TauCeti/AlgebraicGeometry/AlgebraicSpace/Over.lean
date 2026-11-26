/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Category
public import TauCeti.CategoryTheory.MorphismProperty.Representable.Over
public import TauCeti.CategoryTheory.ObjectProperty.Over
public import TauCeti.CategoryTheory.Sites.Over.Yoneda

/-!
# Algebraic spaces over a base scheme

For a scheme `S`, an *algebraic space over `S`* is a presheaf of sets `P` on the category
`Over S` of schemes over `S` which is a sheaf for the fppf topology, whose diagonal is
representable by schemes over `S`, and which admits an étale atlas: a scheme `U` over `S` with a
morphism `h_U ⟶ P` whose base changes along morphisms `h_T ⟶ P` from schemes over `S` are
represented by étale surjective morphisms of schemes (Stacks, Definition 65.6.1 (025Y)). This is
the predicate `IsAlgebraicSpaceOver S`.

Presheaves on `Over S` are presheaves on schemes lying over `h_S`
(`TauCeti.overYonedaEquivPresheafOver`), and under this correspondence a presheaf on `Over S` is
an algebraic space over `S` exactly when the presheaf on schemes is an algebraic space
(`CategoryTheory.Over.isAlgebraicSpaceOver_overYonedaEquivPresheafOver_iff`). Hence
`AlgSpace.overEquiv S` identifies algebraic spaces over the algebraic space `h_S` with algebraic
spaces over `S` in the sense of the Stacks Project.

## Main definitions

* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpaceOver S P`: the presheaf `P` on `Over S` is
  an algebraic space over `S`.
* `TauCeti.AlgebraicGeometry.Spaces.AlgSpace.overEquiv S`: algebraic spaces over `h_S` are
  equivalent to the full subcategory of presheaves on `Over S` satisfying
  `IsAlgebraicSpaceOver S`. Its functor and inverse are compared with those of
  `TauCeti.overYonedaEquivPresheafOver S` by `AlgSpace.overEquiv_functor_comp_ι` and
  `AlgSpace.overEquiv_inverse_comp_overPost`.

## Main results

* `CategoryTheory.Over.isAlgebraicSpaceOver_overYonedaEquivPresheafOver_iff`: a presheaf `F` on
  schemes over `h_S` is an algebraic space if and only if the corresponding presheaf on `Over S`
  is an algebraic space over `S`.

## References

* [Stacks Project, Definition 65.6.1](https://stacks.math.columbia.edu/tag/025Y)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

/-- A presheaf of sets `P` on the category of schemes over `S` is an *algebraic space over `S`*
if it is a sheaf for the fppf topology, its diagonal is representable by schemes over `S`, and it
admits an étale atlas: a morphism `h_U ⟶ P` from a scheme over `S` whose base changes along
morphisms from schemes over `S` are represented by étale surjective morphisms of schemes
(Stacks, Definition 65.6.1 (025Y)). -/
structure IsAlgebraicSpaceOver (S : Scheme.{u}) (P : (Over S)ᵒᵖ ⥤ Type u) : Prop where
  /-- An algebraic space over `S` is a sheaf for the fppf topology on schemes over `S`. -/
  isSheaf : Presheaf.IsSheaf (Scheme.fppfTopology.over S) P
  /-- An algebraic space over `S` has diagonal representable by schemes over `S`. -/
  representableDiagonal : yoneda.relativelyRepresentable (diag P)
  /-- An algebraic space over `S` admits an étale atlas by a scheme over `S`. -/
  exists_etaleAtlas : ∃ (U : Over S) (a : yoneda.obj U ⟶ P),
    MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale (Over.forget S)) a ∧
      MorphismProperty.presheaf (MorphismProperty.inverseImage @Surjective (Over.forget S)) a

namespace IsAlgebraicSpaceOver

variable {S : Scheme.{u}}

/-- Being an algebraic space over `S` is invariant under isomorphism of presheaves. -/
theorem of_iso {P Q : (Over S)ᵒᵖ ⥤ Type u} (e : P ≅ Q) (hP : IsAlgebraicSpaceOver S P) :
    IsAlgebraicSpaceOver S Q where
  isSheaf := (Presheaf.isSheaf_of_iso_iff e).1 hP.isSheaf
  representableDiagonal := Functor.relativelyRepresentable.diag_iff.2 fun _ g ↦ by
    simpa using MorphismProperty.comp_mem _ _ e.hom
      (Functor.relativelyRepresentable.diag_iff.1 hP.representableDiagonal (g ≫ e.inv))
      (Functor.relativelyRepresentable.of_isIso _ e.hom)
  exists_etaleAtlas := by
    obtain ⟨U, a, he, hs⟩ := hP.exists_etaleAtlas
    exact ⟨U, a ≫ e.hom, (MorphismProperty.relative_respectsIso _).postcomp _ e.hom _ he,
      (MorphismProperty.relative_respectsIso _).postcomp _ e.hom _ hs⟩

instance : ObjectProperty.IsClosedUnderIsomorphisms
    (IsAlgebraicSpaceOver S : ObjectProperty ((Over S)ᵒᵖ ⥤ Type u)) where
  of_iso e h := h.of_iso e

end IsAlgebraicSpaceOver

section overYoneda

variable {S : Scheme.{u}} (F : Over (yoneda.obj S))

/-- A presheaf on schemes over `h_S` is an fppf sheaf exactly when the corresponding presheaf
on `Over S` is. -/
theorem _root_.CategoryTheory.Over.isSheaf_fppfTopology_overYonedaEquivPresheafOver_iff :
    Presheaf.IsSheaf (Scheme.fppfTopology.over S)
        ((overYonedaEquivPresheafOver S).functor.obj F) ↔
      Presheaf.IsSheaf Scheme.fppfTopology F.left := by
  rw [isSheaf_iff_isSheaf_of_type, isSheaf_iff_isSheaf_of_type]
  exact GrothendieckTopology.isSheaf_overYonedaEquivPresheafOver_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).1 (Scheme.fppfTopology.yoneda.obj S).property) F

/-- A presheaf on schemes over `h_S` has representable diagonal exactly when the corresponding
presheaf on `Over S` has diagonal representable by schemes over `S`. -/
theorem _root_.CategoryTheory.Over.representableDiagonal_overYonedaEquivPresheafOver_iff :
    yoneda.relativelyRepresentable (diag ((overYonedaEquivPresheafOver S).functor.obj F)) ↔
      RepresentableDiagonal F.left := by
  rw [Functor.relativelyRepresentable.diag_iff, representableDiagonal_iff]
  constructor
  · intro h U g
    exact (Over.relativelyRepresentable_overYonedaEquivPresheafOverHomEquiv_iff
      (Over.postHomMk g)).1 (h _)
  · intro h Y g
    obtain ⟨g, rfl⟩ := (Over.overYonedaEquivPresheafOverHomEquiv Y F).surjective g
    exact (Over.relativelyRepresentable_overYonedaEquivPresheafOverHomEquiv_iff g).2 (h g.left)

/-- A presheaf on schemes over `h_S` has an étale atlas exactly when the corresponding presheaf
on `Over S` has an étale atlas by a scheme over `S`. -/
theorem _root_.CategoryTheory.Over.exists_etaleAtlas_overYonedaEquivPresheafOver_iff :
    (∃ (U : Over S) (a : yoneda.obj U ⟶ (overYonedaEquivPresheafOver S).functor.obj F),
      MorphismProperty.presheaf (MorphismProperty.inverseImage @Etale (Over.forget S)) a ∧
        MorphismProperty.presheaf (MorphismProperty.inverseImage @Surjective (Over.forget S)) a) ↔
      ∃ (U : Scheme.{u}) (a : yoneda.obj U ⟶ F.left), EtaleAtlas a := by
  constructor
  · rintro ⟨Y, a, he, hs⟩
    obtain ⟨g, rfl⟩ := (Over.overYonedaEquivPresheafOverHomEquiv Y F).surjective a
    exact ⟨Y.left, g.left,
      (MorphismProperty.presheaf_overYonedaEquivPresheafOverHomEquiv_iff _ g).1 he,
      (MorphismProperty.presheaf_overYonedaEquivPresheafOverHomEquiv_iff _ g).1 hs⟩
  · rintro ⟨U, a, ha⟩
    exact ⟨_, _, (MorphismProperty.presheaf_overYonedaEquivPresheafOverHomEquiv_iff _
        (Over.postHomMk a)).2 ha.etale,
      (MorphismProperty.presheaf_overYonedaEquivPresheafOverHomEquiv_iff _
        (Over.postHomMk a)).2 ha.surjective⟩

/-- A presheaf on schemes lying over `h_S` is an algebraic space exactly when the corresponding
presheaf on `Over S` is an algebraic space over `S`. -/
theorem _root_.CategoryTheory.Over.isAlgebraicSpaceOver_overYonedaEquivPresheafOver_iff :
    IsAlgebraicSpaceOver S ((overYonedaEquivPresheafOver S).functor.obj F) ↔
      IsAlgebraicSpace F.left :=
  ⟨fun h ↦ ⟨F.isSheaf_fppfTopology_overYonedaEquivPresheafOver_iff.1 h.isSheaf,
      F.representableDiagonal_overYonedaEquivPresheafOver_iff.1 h.representableDiagonal,
      F.exists_etaleAtlas_overYonedaEquivPresheafOver_iff.1 h.exists_etaleAtlas⟩,
    fun h ↦ ⟨F.isSheaf_fppfTopology_overYonedaEquivPresheafOver_iff.2 h.isSheaf,
      F.representableDiagonal_overYonedaEquivPresheafOver_iff.2 h.representableDiagonal,
      F.exists_etaleAtlas_overYonedaEquivPresheafOver_iff.2 h.exists_etaleAtlas⟩⟩

end overYoneda

namespace AlgSpace

/-- Algebraic spaces over the algebraic space `h_S` of a scheme `S` are equivalent to algebraic
spaces over `S`: presheaves on schemes over `S` satisfying `IsAlgebraicSpaceOver S`. -/
noncomputable def overEquiv (S : Scheme.{u}) :
    Over (ofScheme.obj S) ≌
      ObjectProperty.FullSubcategory
        (IsAlgebraicSpaceOver S : ObjectProperty ((Over S)ᵒᵖ ⥤ Type u)) :=
  (ObjectProperty.overFullSubcategoryEquiv _ (ofScheme.obj S)).trans
    ((overYonedaEquivPresheafOver S).congrFullSubcategory
      (by ext F; exact F.isAlgebraicSpaceOver_overYonedaEquivPresheafOver_iff))

/-- `overEquiv S` is the comparison of over categories of a full subcategory followed by the
restriction of `TauCeti.overYonedaEquivPresheafOver S` to algebraic spaces. -/
theorem overEquiv_def (S : Scheme.{u}) :
    overEquiv S = (ObjectProperty.overFullSubcategoryEquiv _ (ofScheme.obj S)).trans
      ((overYonedaEquivPresheafOver S).congrFullSubcategory
        (by ext F; exact F.isAlgebraicSpaceOver_overYonedaEquivPresheafOver_iff)) :=
  (rfl)

/-- The algebraic space over `S` attached to an algebraic space `Y` over `h_S` is the presheaf on
`Over S` attached to the presheaf `Y` over `h_S`. -/
@[simp]
theorem overEquiv_functor_obj_obj (S : Scheme.{u}) (Y : Over (ofScheme.obj S)) :
    ((overEquiv S).functor.obj Y).obj =
      (overYonedaEquivPresheafOver S).functor.obj (Over.mk Y.hom.hom) :=
  (rfl)

/-- After forgetting the full-subcategory wrappers, the functor of `overEquiv S` is
`Over.post toPresheaf` followed by `TauCeti.overYonedaEquivPresheafOver S`. -/
theorem overEquiv_functor_comp_ι (S : Scheme.{u}) :
    (overEquiv S).functor ⋙ ObjectProperty.ι _ =
      Over.post toPresheaf ⋙ (overYonedaEquivPresheafOver S).functor :=
  (rfl)

/-- After forgetting the full-subcategory wrappers, the inverse of `overEquiv S` is the inverse
of `TauCeti.overYonedaEquivPresheafOver S`. -/
theorem overEquiv_inverse_comp_overPost (S : Scheme.{u}) :
    (overEquiv S).inverse ⋙ Over.post toPresheaf =
      ObjectProperty.ι _ ⋙ (overYonedaEquivPresheafOver S).inverse :=
  (rfl)

end AlgSpace

end TauCeti.AlgebraicGeometry.Spaces
