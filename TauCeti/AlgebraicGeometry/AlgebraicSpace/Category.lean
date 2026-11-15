/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AlgebraicSpace.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Limits.Yoneda

/-!
# The category of algebraic spaces

`Spaces.AlgSpace` is the full subcategory of presheaves on schemes consisting of algebraic
spaces. The functor `AlgSpace.ofScheme` embeds schemes fully faithfully, and morphisms from
an embedded scheme to a space are identified with its sections by `AlgSpace.homFromSchemeEquiv`.
This lets schemes serve as test objects without choosing an atlas.

The embedded empty scheme is initial, using the empty fppf covering. The embedded spectrum of
the integers is terminal. In particular, these are the geometric initial and terminal objects,
even though the initial presheaf itself is not a sheaf on the empty scheme.

The construction uses Mathlib's `ObjectProperty.FullSubcategory`, its functor lifting API,
and the Yoneda lemma. See the Stacks Project, Definition 65.6.1 (025Y) and Section 65.7 (02X0).
-/

public section

open CategoryTheory Limits Opposite

namespace TauCeti.AlgebraicGeometry.Spaces

open _root_.AlgebraicGeometry

universe u

/-- Algebraic spaces, with natural transformations of their presheaves as morphisms. -/
abbrev AlgSpace :=
  ObjectProperty.FullSubcategory (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u})

namespace AlgSpace

/-- The fully faithful inclusion of algebraic spaces into presheaves on schemes. -/
abbrev toPresheaf : AlgSpace.{u} ⥤ SchemePresheaf.{u} :=
  ObjectProperty.ι (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u})

/-- A scheme regarded as an algebraic space through its functor of points. The functor is
exposed so that morphisms involving its objects have the usual Yoneda source and target. -/
@[expose]
def ofScheme : Scheme.{u} ⥤ AlgSpace.{u} :=
  ObjectProperty.lift (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) yoneda
    IsAlgebraicSpace.yoneda_obj

@[simp]
lemma ofScheme_obj_obj (X : Scheme.{u}) : (ofScheme.obj X).obj = yoneda.obj X :=
  (rfl)

@[simp]
lemma ofScheme_map_hom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (ofScheme.map f).hom = yoneda.map f :=
  (rfl)

instance : ofScheme.{u}.Full :=
  inferInstanceAs ((ObjectProperty.lift
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) yoneda
      IsAlgebraicSpace.yoneda_obj).Full)

instance : ofScheme.{u}.Faithful :=
  inferInstanceAs ((ObjectProperty.lift
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) yoneda
      IsAlgebraicSpace.yoneda_obj).Faithful)

/-- Forgetting the algebraic-space structure of the scheme embedding gives the Yoneda functor. -/
def ofSchemeCompToPresheafIso : ofScheme.{u} ⋙ toPresheaf ≅ yoneda :=
  ObjectProperty.liftCompιIso (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u}) yoneda
    IsAlgebraicSpace.yoneda_obj

@[simp]
lemma ofSchemeCompToPresheafIso_hom_app (X : Scheme.{u}) :
    ofSchemeCompToPresheafIso.hom.app X = 𝟙 (yoneda.obj X) :=
  (rfl)

@[simp]
lemma ofSchemeCompToPresheafIso_inv_app (X : Scheme.{u}) :
    ofSchemeCompToPresheafIso.inv.app X = 𝟙 (yoneda.obj X) :=
  (rfl)

/-- Morphisms from the algebraic space of a scheme are sections over that scheme. -/
noncomputable def homFromSchemeEquiv (X : Scheme.{u}) (F : AlgSpace.{u}) :
    (ofScheme.obj X ⟶ F) ≃ F.obj.obj (op X) :=
  ((ObjectProperty.fullyFaithfulι
    (IsAlgebraicSpace : ObjectProperty SchemePresheaf.{u})).homEquiv).trans yonedaEquiv

-- As for `yonedaEquiv_apply`, explicit evaluation is not a simp normal form:
-- keep the equivalence visible so that its naturality lemmas can simplify composites.
lemma homFromSchemeEquiv_apply (X : Scheme.{u}) (F : AlgSpace.{u})
    (f : ofScheme.obj X ⟶ F) :
    homFromSchemeEquiv X F f = f.hom.app (op X) (𝟙 X) :=
  (rfl)

@[simp]
lemma homFromSchemeEquiv_symm_app (X : Scheme.{u}) (F : AlgSpace.{u})
    (x : F.obj.obj (op X)) (T : Scheme.{u}) (f : T ⟶ X) :
    ((homFromSchemeEquiv X F).symm x).hom.app (op T) f = F.obj.map f.op x :=
  (rfl)

/-- The section corresponding to a morphism restricts by precomposing with a scheme morphism. -/
-- Use explicitly: the postcomposition simp lemma already simplifies this composite.
lemma homFromSchemeEquiv_precomp {X Y : Scheme.{u}} (f : X ⟶ Y) (F : AlgSpace.{u})
    (g : ofScheme.obj Y ⟶ F) :
    homFromSchemeEquiv X F (ofScheme.map f ≫ g) =
      F.obj.map f.op (homFromSchemeEquiv Y F g) := by
  exact (yonedaEquiv_naturality g.hom f).symm

/-- The section corresponding to a morphism is natural in the target algebraic space. -/
@[simp]
lemma homFromSchemeEquiv_postcomp (X : Scheme.{u}) {F G : AlgSpace.{u}}
    (f : ofScheme.obj X ⟶ F) (g : F ⟶ G) :
    homFromSchemeEquiv X G (f ≫ g) = g.hom.app (op X) (homFromSchemeEquiv X F f) :=
  (rfl)

/-- A terminal scheme remains terminal as an algebraic space. -/
noncomputable def isTerminalOfScheme {X : Scheme.{u}} (hX : IsTerminal X) :
    IsTerminal (ofScheme.obj X) :=
  IsTerminal.isTerminalOfObj toPresheaf _ (hX.isTerminalObj yoneda X)

/-- The spectrum of the integers, lifted to the scheme universe, is a terminal algebraic space. -/
noncomputable def specZIsTerminal :
    IsTerminal (ofScheme.obj (Spec (.of (ULift.{u} ℤ)))) :=
  isTerminalOfScheme specULiftZIsTerminal

noncomputable instance : HasTerminal AlgSpace.{u} :=
  specZIsTerminal.hasTerminal

/-- The empty scheme is an initial algebraic space: every fppf sheaf has exactly one section
over it. -/
noncomputable def emptyIsInitial : IsInitial (ofScheme.obj (∅ : Scheme.{u})) := by
  let e (F : AlgSpace.{u}) := homFromSchemeEquiv (∅ : Scheme.{u}) F
  let h (F : AlgSpace.{u}) := Types.isTerminalEquivUnique _
    (Sheaf.isTerminalOfBotCover ⟨F.obj, F.property.isSheaf⟩ ∅
      (Scheme.bot_mem_grothendieckTopology (∅ : Scheme.{u})))
  exact IsInitial.ofUniqueHom (fun F ↦ (e F).symm (h F).default)
    (fun F f ↦ (e F).injective (by simpa using (h F).uniq (e F f)))

noncomputable instance : HasInitial AlgSpace.{u} :=
  emptyIsInitial.hasInitial

end AlgSpace

end TauCeti.AlgebraicGeometry.Spaces
