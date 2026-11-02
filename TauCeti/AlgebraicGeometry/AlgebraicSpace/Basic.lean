/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!
# Algebraic spaces

An *algebraic space* is a presheaf of sets `F` on the big category of schemes which is a sheaf
for the fppf topology, whose diagonal `F ⟶ F ⨯ F` is representable by schemes, and which admits
an *étale atlas*: a scheme `U` with a morphism `h_U ⟶ F` that is representable by schemes and
whose base change along every `h_T ⟶ F` is an étale surjective morphism of schemes (Stacks,
Definition 65.6.1 (025Y)). This file defines the three predicates and their elementary API.

Representability of a morphism of presheaves is Mathlib's `Functor.relativelyRepresentable` for
the Yoneda embedding, and being étale and surjective after every base change is Mathlib's
`MorphismProperty.presheaf`. By Mathlib's `Functor.relativelyRepresentable.diag_iff`, the diagonal
of `F` is representable exactly when every morphism `h_U ⟶ F` from a scheme is. Every scheme is
an algebraic space, with no separatedness hypothesis.

## Main definitions

* `TauCeti.AlgebraicGeometry.SchemePresheaf`: presheaves of sets on the category of schemes.
* `TauCeti.AlgebraicGeometry.Spaces.RepresentableDiagonal F`: the diagonal of `F` is representable
  by schemes.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas a`: a morphism `a : h_U ⟶ F` from a scheme is
  representable by étale surjective morphisms of schemes.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace F`: `F` is an fppf sheaf with representable
  diagonal and an étale atlas.

## Main results

* `TauCeti.AlgebraicGeometry.Spaces.representableDiagonal_iff`: the diagonal of `F` is
  representable if and only if every morphism from a scheme to `F` is.
* `TauCeti.AlgebraicGeometry.Spaces.etaleAtlas_yoneda_map_iff`: for a morphism of schemes `f`,
  `h_f` is an étale atlas if and only if `f` is étale and surjective.
* `TauCeti.AlgebraicGeometry.Spaces.EtaleAtlas.yoneda_map_comp`: precomposing an étale atlas with
  an étale surjective morphism of schemes gives an étale atlas.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.yoneda_obj` and
  `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.of_isRepresentable`: every scheme, and every
  representable presheaf, is an algebraic space.
* `TauCeti.AlgebraicGeometry.Spaces.IsAlgebraicSpace.of_iso`: being an algebraic space is
  invariant under isomorphism of presheaves.

## References

* [Stacks Project, Definition 65.6.1](https://stacks.math.columbia.edu/tag/025Y)
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- Presheaves of sets on the category of schemes. Algebraic spaces are the presheaves
satisfying `Spaces.IsAlgebraicSpace`. -/
abbrev SchemePresheaf := Scheme.{u}ᵒᵖ ⥤ Type u

namespace Spaces

/-- The diagonal `F ⟶ F ⨯ F` of a presheaf on schemes is representable by schemes: its base
change along every morphism `h_T ⟶ F ⨯ F` from a scheme is a morphism of schemes. -/
def RepresentableDiagonal (F : SchemePresheaf.{u}) : Prop :=
  yoneda.relativelyRepresentable (diag F)

/-- Unfolds `RepresentableDiagonal F` to its defining statement about the diagonal `diag F`. -/
theorem representableDiagonal_iff_diag {F : SchemePresheaf.{u}} :
    RepresentableDiagonal F ↔ yoneda.relativelyRepresentable (diag F) :=
  Iff.rfl

/-- The diagonal of `F` is representable exactly when every morphism from a scheme to `F` is
representable by schemes. -/
theorem representableDiagonal_iff {F : SchemePresheaf.{u}} :
    RepresentableDiagonal F ↔
      ∀ ⦃U : Scheme.{u}⦄ (g : yoneda.obj U ⟶ F), yoneda.relativelyRepresentable g :=
  Functor.relativelyRepresentable.diag_iff

/-- If the diagonal of `F` is representable, then every morphism from a scheme to `F` is
representable by schemes. -/
theorem RepresentableDiagonal.relativelyRepresentable {F : SchemePresheaf.{u}}
    (hF : RepresentableDiagonal F) {U : Scheme.{u}} (g : yoneda.obj U ⟶ F) :
    yoneda.relativelyRepresentable g :=
  representableDiagonal_iff.1 hF g

/-- The functor of points of a scheme has representable diagonal. No separatedness hypothesis
is needed: the base changes of the diagonal are fibre products of schemes. -/
theorem RepresentableDiagonal.yoneda_obj (X : Scheme.{u}) :
    RepresentableDiagonal (yoneda.obj X) :=
  representableDiagonal_iff.2 fun _ g ↦ by
    simpa using Functor.relativelyRepresentable.map yoneda (yoneda.preimage g)

/-- Having representable diagonal is invariant under isomorphism of presheaves. -/
theorem RepresentableDiagonal.of_iso {F G : SchemePresheaf.{u}} (e : F ≅ G)
    (hF : RepresentableDiagonal F) : RepresentableDiagonal G :=
  representableDiagonal_iff.2 fun _ g ↦ by
    simpa using MorphismProperty.comp_mem _ _ e.hom (hF.relativelyRepresentable (g ≫ e.inv))
      (Functor.relativelyRepresentable.of_isIso _ e.hom)

/-- A morphism `a : h_U ⟶ F` from a scheme is an *étale atlas* if it is representable by schemes
and its base change along every morphism `h_T ⟶ F` from a scheme is an étale surjective morphism
of schemes. -/
structure EtaleAtlas {F : SchemePresheaf.{u}} {U : Scheme.{u}} (a : yoneda.obj U ⟶ F) : Prop where
  /-- The base changes of an étale atlas along morphisms from schemes are étale. -/
  etale : MorphismProperty.presheaf @Etale a
  /-- The base changes of an étale atlas along morphisms from schemes are surjective. -/
  surjective : MorphismProperty.presheaf @Surjective a

namespace EtaleAtlas

variable {F : SchemePresheaf.{u}} {U : Scheme.{u}} {a : yoneda.obj U ⟶ F}

/-- An étale atlas is representable by schemes. -/
theorem relativelyRepresentable (ha : EtaleAtlas a) : yoneda.relativelyRepresentable a :=
  ha.etale.rep

/-- The base change of an étale atlas along a morphism from a scheme is étale. -/
theorem etale_snd (ha : EtaleAtlas a) {T : Scheme.{u}} (g : yoneda.obj T ⟶ F) :
    Etale (ha.relativelyRepresentable.snd g) :=
  ha.etale.property_snd g

/-- The base change of an étale atlas along a morphism from a scheme is surjective. -/
theorem surjective_snd (ha : EtaleAtlas a) {T : Scheme.{u}} (g : yoneda.obj T ⟶ F) :
    Surjective (ha.relativelyRepresentable.snd g) :=
  ha.surjective.property_snd g

/-- A morphism from a scheme that is representable by schemes, with étale and surjective base
changes along every morphism from a scheme, is an étale atlas. -/
theorem of_snd (hr : yoneda.relativelyRepresentable a)
    (he : ∀ ⦃T : Scheme.{u}⦄ (g : yoneda.obj T ⟶ F), Etale (hr.snd g))
    (hs : ∀ ⦃T : Scheme.{u}⦄ (g : yoneda.obj T ⟶ F), Surjective (hr.snd g)) :
    EtaleAtlas a :=
  -- Instance search does not derive `RespectsIso` for étale morphisms from their stability
  -- under base change.
  have : MorphismProperty.RespectsIso @Etale.{u} :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  ⟨MorphismProperty.relative_of_snd hr he, MorphismProperty.relative_of_snd hr hs⟩

/-- Composing an étale atlas with an isomorphism of presheaves gives an étale atlas. -/
theorem comp_iso (ha : EtaleAtlas a) {G : SchemePresheaf.{u}} (e : F ≅ G) :
    EtaleAtlas (a ≫ e.hom) :=
  ⟨(MorphismProperty.relative_respectsIso _).postcomp _ e.hom _ ha.etale,
    (MorphismProperty.relative_respectsIso _).postcomp _ e.hom _ ha.surjective⟩

end EtaleAtlas

/-- For a morphism of schemes `f : U ⟶ X`, the induced morphism of functors of points
`h_U ⟶ h_X` is an étale atlas if and only if `f` is étale and surjective. -/
@[simp]
theorem etaleAtlas_yoneda_map_iff {U X : Scheme.{u}} (f : U ⟶ X) :
    EtaleAtlas (yoneda.map f) ↔ Etale f ∧ Surjective f :=
  ⟨fun ha ↦ ⟨MorphismProperty.of_relative_map ha.etale,
      MorphismProperty.of_relative_map ha.surjective⟩,
    fun ⟨hf, hs⟩ ↦ ⟨MorphismProperty.relative_map hf, MorphismProperty.relative_map hs⟩⟩

/-- An isomorphism from the functor of points of a scheme is an étale atlas. -/
theorem EtaleAtlas.of_isIso {F : SchemePresheaf.{u}} {U : Scheme.{u}} (a : yoneda.obj U ⟶ F)
    [IsIso a] : EtaleAtlas a := by
  simpa using ((etaleAtlas_yoneda_map_iff (𝟙 U)).2 ⟨inferInstance, inferInstance⟩).comp_iso
    (asIso a)

/-- Precomposing an étale atlas with an étale surjective morphism of schemes gives an étale
atlas. -/
theorem EtaleAtlas.yoneda_map_comp {F : SchemePresheaf.{u}} {U V : Scheme.{u}}
    {a : yoneda.obj U ⟶ F} (ha : EtaleAtlas a) (f : V ⟶ U) [Etale f] [Surjective f] :
    EtaleAtlas (yoneda.map f ≫ a) := by
  -- Instance search does not recover the parents `IsStableUnderComposition` of the
  -- `IsMultiplicative` instances of étale and surjective morphisms, nor see through
  -- `MorphismProperty.presheaf`, so provide the relative instances locally.
  have : MorphismProperty.IsStableUnderComposition @Etale.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : MorphismProperty.IsStableUnderComposition @Surjective.{u} :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have : (MorphismProperty.presheaf @Etale.{u}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition (F := yoneda) (P := @Etale.{u})
  have : (MorphismProperty.presheaf @Surjective.{u}).IsStableUnderComposition :=
    MorphismProperty.relative_isStableUnderComposition (F := yoneda) (P := @Surjective.{u})
  have hf := (etaleAtlas_yoneda_map_iff f).2 ⟨‹_›, ‹_›⟩
  exact ⟨MorphismProperty.comp_mem _ _ _ hf.etale ha.etale,
    MorphismProperty.comp_mem _ _ _ hf.surjective ha.surjective⟩

/-- A presheaf on schemes is an *algebraic space* if it is a sheaf for the fppf topology, its
diagonal is representable by schemes, and it admits an étale atlas (Stacks, Definition 65.6.1
(025Y)). -/
structure IsAlgebraicSpace (F : SchemePresheaf.{u}) : Prop where
  /-- An algebraic space is a sheaf for the fppf topology. -/
  isSheaf : Presheaf.IsSheaf Scheme.fppfTopology F
  /-- An algebraic space has representable diagonal. -/
  representableDiagonal : RepresentableDiagonal F
  /-- An algebraic space admits an étale atlas. -/
  exists_etaleAtlas : ∃ (U : Scheme.{u}) (a : yoneda.obj U ⟶ F), EtaleAtlas a

namespace IsAlgebraicSpace

/-- Being an algebraic space is invariant under isomorphism of presheaves. -/
theorem of_iso {F G : SchemePresheaf.{u}} (e : F ≅ G) (hF : IsAlgebraicSpace F) :
    IsAlgebraicSpace G where
  isSheaf := (Presheaf.isSheaf_of_iso_iff e).1 hF.isSheaf
  representableDiagonal := hF.representableDiagonal.of_iso e
  exists_etaleAtlas := by
    obtain ⟨U, a, ha⟩ := hF.exists_etaleAtlas
    exact ⟨U, a ≫ e.hom, ha.comp_iso e⟩

/-- The functor of points of a scheme is an algebraic space. -/
theorem yoneda_obj (X : Scheme.{u}) : IsAlgebraicSpace (yoneda.obj X) where
  isSheaf := (Scheme.fppfTopology.yoneda.obj X).property
  representableDiagonal := .yoneda_obj X
  exists_etaleAtlas := ⟨X, 𝟙 _, .of_isIso _⟩

/-- A representable presheaf on schemes is an algebraic space. -/
theorem of_isRepresentable (F : SchemePresheaf.{u}) [F.IsRepresentable] : IsAlgebraicSpace F :=
  (yoneda_obj F.reprX).of_iso F.reprW

end IsAlgebraicSpace

end Spaces

end TauCeti.AlgebraicGeometry
