/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Sites.Descent.IsPrestack

/-!
# The fibres of the Hom-sheafification of a pseudofunctor

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
The stackification of `F` is obtained by Hom-sheafification followed by adjoining descent data
(Stacks, Section 02ZM). The second step, for prestacks, is
`TauCeti.CategoryTheory.Sites.Descent.Stackification.Basic`. This file constructs the fibres of
the first step for an arbitrary `F`, whose presheaves of morphisms `F.presheafHom M N` need not
be sheaves.

The fibre over `U` has the objects of `F` over `U`, and its morphisms from `M` to `N` are the
sections over the terminal object `Over.mk (𝟙 U)` of the sheafification of `F.presheafHom M N`
for `J.over U`. Composition is induced by composition of local morphisms, through the
compatibility of sheafification with finite products. Concretely, the presheaves
`F.presheafHom M N` enrich the fibre of `F` over `U` in presheaves of types on `Over U`
(`HomEnriched`), the functor `sheafifySections J U` (sheafify, then take sections over the
terminal object) preserves finite products and so is monoidal, and the fibre `Fibre J F U` is the
category obtained by transporting the enrichment along it (Mathlib's `TransportEnrichment`).

The comparison functor `toFibre J F U` from the fibre of `F` is the identity on objects and sends
a morphism to its image in the sheafification. For a prestack it is an equivalence
(`toFibreEquivalence`).

## Main declarations

* `TauCeti.Stack.Prestackification.HomEnriched`: the fibre of `F` over `U`, enriched in
  presheaves of types on `Over U` by `F.presheafHom`.
* `TauCeti.Stack.Prestackification.sheafifySections`: sheafification followed by sections over
  the terminal object, a monoidal functor.
* `TauCeti.Stack.Prestackification.Fibre`: the fibre over `U` of the Hom-sheafification of `F`.
* `TauCeti.Stack.Prestackification.Fibre.homMk`: the morphism given by a local morphism, and
  `Fibre.homMk_comp`, `Fibre.id_eq`, which compute composition and identities.
* `TauCeti.Stack.Prestackification.toFibre`: the comparison functor from the fibre of `F`, and
  `toFibreEquivalence`, the equivalence it gives for a prestack.

## References

* [Stacks Project, Section 02ZM](https://stacks.math.columbia.edu/tag/02ZM)
-/

@[expose] public section

noncomputable section

universe v' u' v u

open CategoryTheory Limits Opposite MonoidalCategory Bicategory Pseudofunctor
  LocallyDiscreteOpToCat

namespace CategoryTheory.Pseudofunctor

variable {C : Type u} [Category.{v} C] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}) {S : C}

/-- The identification of morphisms of `F` over `S` with sections of `F.presheafHom` over the
terminal object sends identities to identities. -/
lemma presheafHomObjHomEquiv_id (M : F.obj (.mk (op S))) :
    F.presheafHomObjHomEquiv (𝟙 M) = 𝟙 _ := by
  refine (presheafHomObjHomEquiv_apply F (𝟙 M)).trans ?_
  simp [← Cat.Hom₂.comp_app]

/-- The identification of morphisms of `F` over `S` with sections of `F.presheafHom` over the
terminal object is compatible with composition. -/
lemma presheafHomObjHomEquiv_comp {M N P : F.obj (.mk (op S))} (φ : M ⟶ N) (ψ : N ⟶ P) :
    F.presheafHomObjHomEquiv (φ ≫ ψ) =
      F.presheafHomObjHomEquiv φ ≫ F.presheafHomObjHomEquiv ψ := by
  refine (presheafHomObjHomEquiv_apply F (φ ≫ ψ)).trans ?_
  refine Eq.trans ?_ (congrArg₂ (· ≫ ·) (presheafHomObjHomEquiv_apply F φ).symm
    (presheafHomObjHomEquiv_apply F ψ).symm)
  simp [← Cat.Hom₂.comp_app_assoc]

end CategoryTheory.Pseudofunctor

namespace TauCeti.Stack.Prestackification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

section

variable {F} {U : C}

/-- Composition of local morphisms, as a morphism of presheaves on `Over U`. -/
def presheafHomComp (M N P : F.obj (.mk (op U))) :
    F.presheafHom M N ⊗ F.presheafHom N P ⟶ F.presheafHom M P where
  app T := TypeCat.ofHom fun p ↦ p.1 ≫ p.2
  naturality T T' g := by
    ext ⟨f, g⟩
    exact (pullHom_comp _ _ _ _ _ _).symm

/-- Identities of local morphisms, as a morphism of presheaves on `Over U`. -/
def presheafHomId (M : F.obj (.mk (op U))) : 𝟙_ ((Over U)ᵒᵖ ⥤ Type v') ⟶ F.presheafHom M M where
  app T := TypeCat.ofHom fun _ ↦ 𝟙 _
  naturality T T' g := by
    ext p
    simp

end

/-- The fibre of `F` over `U`, as a type synonym carrying the enrichment in presheaves of types
on `Over U` given by the presheaves of morphisms `F.presheafHom`. -/
def HomEnriched (U : C) : Type u' := F.obj (.mk (op U))

instance instEnrichedCategoryHomEnriched (U : C) :
    EnrichedCategory ((Over U)ᵒᵖ ⥤ Type v') (HomEnriched F U) where
  Hom M N := F.presheafHom (S := U) M N
  id M := presheafHomId M
  comp M N P := presheafHomComp M N P
  id_comp M N := by
    ext T f
    exact Category.id_comp f
  comp_id M N := by
    ext T f
    exact Category.comp_id f
  assoc M N P Q := by
    ext T ⟨f, g, h⟩
    exact Category.assoc f g h

section

variable (U : C) [HasSheafify (J.over U) (Type v')]

/-- The functor sending a presheaf of types on `Over U` to the sections of its sheafification
over the terminal object `Over.mk (𝟙 U)`. -/
def sheafifySections : ((Over U)ᵒᵖ ⥤ Type v') ⥤ Type v' :=
  presheafToSheaf (J.over U) (Type v') ⋙ sheafToPresheaf _ _ ⋙
    (evaluation _ _).obj (op (Over.mk (𝟙 U)))

instance preservesFiniteProducts_sheafifySections :
    PreservesFiniteProducts (sheafifySections J U) := by
  dsimp [sheafifySections]
  infer_instance

/-- The monoidal structure of `sheafifySections J U`, from its preservation of finite products. -/
instance monoidalSheafifySections : (sheafifySections J U).Monoidal := .ofChosenFiniteProducts _

/-- The value at the terminal object of the unit of sheafification. -/
def toSheafifySections : (evaluation _ _).obj (op (Over.mk (𝟙 U))) ⟶ sheafifySections J U where
  app P := (toSheafify (J.over U) P).app _
  naturality P Q f := by
    simp [sheafifySections, ← NatTrans.comp_app, toSheafify_naturality]

end

/-- The fibre over `U` of the Hom-sheafification of `F`: its objects are those of `F` over `U`,
and its morphisms from `M` to `N` are the sections over the terminal object of the
sheafification of `F.presheafHom M N`. -/
def Fibre (U : C) [HasSheafify (J.over U) (Type v')] : Type u' :=
  TransportEnrichment (sheafifySections J U) (HomEnriched F U)

instance instEnrichedCategoryFibre (U : C) [HasSheafify (J.over U) (Type v')] :
    EnrichedCategory (Type v') (Fibre J F U) :=
  inferInstanceAs (EnrichedCategory (Type v')
    (TransportEnrichment (sheafifySections J U) (HomEnriched F U)))

instance instCategoryFibre (U : C) [HasSheafify (J.over U) (Type v')] :
    Category.{v'} (Fibre J F U) :=
  categoryOfEnrichedCategoryType _

variable {J F} {U : C} [HasSheafify (J.over U) (Type v')]

/-- An object of `F` over `U` as an object of the fibre of the Hom-sheafification. -/
def Fibre.mk (M : F.obj (.mk (op U))) : Fibre J F U := M

/-- The object of `F` underlying an object of the fibre of the Hom-sheafification. -/
def Fibre.obj (M : Fibre J F U) : F.obj (.mk (op U)) := M

@[simp]
lemma Fibre.mk_obj (M : F.obj (.mk (op U))) : (Fibre.mk (J := J) M).obj = M := rfl

@[simp]
lemma Fibre.obj_mk (M : Fibre J F U) : Fibre.mk M.obj = M := rfl


open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The monoidal structure of `sheafifySections J U` is compatible with the unit of
sheafification: the pair of images of `x` and `y` corresponds to the image of `(x, y)`. -/
lemma μ_toSheafifySections {P Q : (Over U)ᵒᵖ ⥤ Type v'} (x : P.obj (op (Over.mk (𝟙 U))))
    (y : Q.obj (op (Over.mk (𝟙 U)))) :
    μ (sheafifySections J U) P Q ((toSheafifySections J U).app P x,
      (toSheafifySections J U).app Q y) =
      (toSheafifySections J U).app (P ⊗ Q) ((x, y) : (P ⊗ Q).obj (op (Over.mk (𝟙 U)))) := by
  set G := sheafifySections J U
  set η := toSheafifySections J U
  let z : (P ⊗ Q).obj (op (Over.mk (𝟙 U))) := (x, y)
  change _ = η.app (P ⊗ Q) z
  have h₁ := ConcreteCategory.congr_hom (Functor.OplaxMonoidal.δ_fst G P Q) (η.app (P ⊗ Q) z)
  have h₂ := ConcreteCategory.congr_hom (Functor.OplaxMonoidal.δ_snd G P Q) (η.app (P ⊗ Q) z)
  have n₁ := ConcreteCategory.congr_hom (η.naturality (CartesianMonoidalCategory.fst P Q)) z
  have n₂ := ConcreteCategory.congr_hom (η.naturality (CartesianMonoidalCategory.snd P Q)) z
  have := ConcreteCategory.congr_hom (Functor.Monoidal.δ_μ G P Q) (η.app (P ⊗ Q) z)
  simp only [ConcreteCategory.comp_apply, ConcreteCategory.id_apply] at h₁ h₂ n₁ n₂ this
  rw [← this]
  congr 1
  refine Prod.ext ?_ ?_
  · exact (h₁.trans n₁.symm).symm
  · exact (h₂.trans n₂.symm).symm

/-- The morphisms of the fibre of the Hom-sheafification are the sections over the terminal
object of the sheafified presheaves of morphisms of `F`. -/
def Fibre.homEquiv (M N : Fibre J F U) :
    (M ⟶ N) ≃ (sheafifySections J U).obj (F.presheafHom M.obj N.obj) :=
  Equiv.refl _

lemma Fibre.homEquiv_comp {M N P : Fibre J F U} (f : M ⟶ N) (g : N ⟶ P) :
    Fibre.homEquiv M P (f ≫ g) = (μ (sheafifySections J U) _ _ ≫ (sheafifySections J U).map
      (presheafHomComp M.obj N.obj P.obj)) ((Fibre.homEquiv M N f, Fibre.homEquiv N P g) :
        (_ ⊗ _)) := rfl

/-- The morphism of the fibre of the Hom-sheafification given by a morphism `x` of `F` over `U`,
written as a section over the terminal object of `F.presheafHom M N`. -/
def Fibre.homMk {M N : Fibre J F U} (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U)))) :
    M ⟶ N :=
  (Fibre.homEquiv M N).symm ((toSheafifySections J U).app _ x)

lemma Fibre.homMk_comp {M N P : Fibre J F U}
    (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U))))
    (y : (F.presheafHom N.obj P.obj).obj (op (Over.mk (𝟙 U)))) :
    Fibre.homMk x ≫ Fibre.homMk y = Fibre.homMk (M := M) (N := P) (x ≫ y) := by
  apply (Fibre.homEquiv M P).injective
  rw [Fibre.homEquiv_comp, ConcreteCategory.comp_apply]
  simp only [Fibre.homMk, Equiv.apply_symm_apply]
  rw [μ_toSheafifySections]
  exact (ConcreteCategory.congr_hom ((toSheafifySections J U).naturality
    (presheafHomComp M.obj N.obj P.obj))
    ((x, y) : (F.presheafHom M.obj N.obj ⊗ F.presheafHom N.obj P.obj).obj _)).symm

lemma Fibre.id_eq (M : Fibre J F U) : 𝟙 M = Fibre.homMk (𝟙 _) := by
  apply (Fibre.homEquiv M M).injective
  simp only [Fibre.homMk, Equiv.apply_symm_apply]
  set G := sheafifySections J U
  have hsub : ∀ a b : G.obj (𝟙_ _), a = b := fun a b ↦ by
    rw [← ConcreteCategory.id_apply (X := G.obj (𝟙_ _)) a,
      ← ConcreteCategory.id_apply (X := G.obj (𝟙_ _)) b, ← Functor.Monoidal.η_ε G,
      ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    rfl
  change (ε G ≫ G.map (presheafHomId M.obj)) PUnit.unit = _
  rw [ConcreteCategory.comp_apply, hsub (ε G PUnit.unit)
    ((toSheafifySections J U).app (𝟙_ ((Over U)ᵒᵖ ⥤ Type v')) PUnit.unit)]
  exact (ConcreteCategory.congr_hom ((toSheafifySections J U).naturality
    (presheafHomId M.obj)) _).symm

variable (J F U) in
/-- The comparison functor from the fibre of `F` over `U` to the fibre of its
Hom-sheafification. It is the identity on objects. -/
def toFibre : F.obj (.mk (op U)) ⥤ Fibre J F U where
  obj M := Fibre.mk M
  map φ := Fibre.homMk (F.presheafHomObjHomEquiv φ)
  map_id M := by
    rw [Fibre.id_eq]
    exact congrArg _ (presheafHomObjHomEquiv_id F M)
  map_comp φ ψ := by
    rw [Fibre.homMk_comp]
    exact congrArg _ (presheafHomObjHomEquiv_comp F φ ψ)

@[simp]
lemma toFibre_obj (M : F.obj (.mk (op U))) : (toFibre J F U).obj M = Fibre.mk M := rfl

lemma toFibre_map {M N : F.obj (.mk (op U))} (φ : M ⟶ N) :
    (toFibre J F U).map φ = Fibre.homMk (F.presheafHomObjHomEquiv φ) := rfl

instance essSurj_toFibre : (toFibre J F U).EssSurj where
  mem_essImage M := ⟨M.obj, ⟨Iso.refl _⟩⟩

/-- For a prestack, the comparison functor is bijective on morphisms. -/
lemma toFibre_map_bijective [F.IsPrestack J] (M N : F.obj (.mk (op U))) :
    Function.Bijective ((toFibre J F U).map : (M ⟶ N) → _) := by
  have := isIso_toSheafify (J.over U) (IsPrestack.isSheaf J M N)
  have hη : Function.Bijective ((toSheafifySections J U).app (F.presheafHom M N)) :=
    (isIso_iff_bijective _).1 (inferInstanceAs (IsIso ((toSheafify (J.over U) _).app _)))
  exact (Fibre.homEquiv (Fibre.mk M) (Fibre.mk N)).symm.bijective.comp
    (hη.comp F.presheafHomObjHomEquiv.bijective)

instance full_toFibre [F.IsPrestack J] : (toFibre J F U).Full where
  map_surjective := (toFibre_map_bijective _ _).2

instance faithful_toFibre [F.IsPrestack J] : (toFibre J F U).Faithful where
  map_injective h := (toFibre_map_bijective _ _).1 h

variable (J F U) in
/-- For a prestack `F`, the comparison functor from the fibre of `F` over `U` to the fibre of
its Hom-sheafification is an equivalence. -/
def toFibreEquivalence [F.IsPrestack J] : F.obj (.mk (op U)) ≌ Fibre J F U :=
  have : (toFibre J F U).IsEquivalence := { }
  (toFibre J F U).asEquivalence

end TauCeti.Stack.Prestackification
end
