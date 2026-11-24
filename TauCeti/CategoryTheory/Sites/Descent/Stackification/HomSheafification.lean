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
terminal object) preserves finite products and so is monoidal, and the fibre `Fiber J F U` is the
category obtained by transporting the enrichment along it (Mathlib's `TransportEnrichment`).

The comparison functor `toFiber J F U` from the fibre of `F` is the identity on objects and sends
a morphism to its image in the sheafification. For a prestack it is an equivalence
(`toFiberEquivalence`).

## Main declarations

* `TauCeti.Stack.Prestackification.HomEnriched`: the fibre of `F` over `U`, enriched in
  presheaves of types on `Over U` by `F.presheafHom`.
* `TauCeti.Stack.Prestackification.sheafifySections`: sheafification followed by sections over
  the terminal object, a monoidal functor.
* `TauCeti.Stack.Prestackification.Fiber`: the fibre over `U` of the Hom-sheafification of `F`.
* `TauCeti.Stack.Prestackification.Fiber.homMk`: the morphism given by a local morphism, and
  `Fiber.homMk_comp`, `Fiber.homMk_id`, which compute composition and identities.
* `TauCeti.Stack.Prestackification.toFiber`: the comparison functor from the fibre of `F`, and
  `toFiberEquivalence`, the equivalence it gives for a prestack.

## References

* [Stacks Project, Section 02ZM](https://stacks.math.columbia.edu/tag/02ZM)
-/

public section

noncomputable section

universe v' u' v u

open CategoryTheory Limits Opposite MonoidalCategory Bicategory Pseudofunctor
  LocallyDiscreteOpToCat

namespace TauCeti.Stack.Prestackification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The fibre of `F` over `U`, as a type synonym carrying the enrichment in presheaves of types
on `Over U` given by the presheaves of morphisms `F.presheafHom`. -/
-- The body is exposed so that objects of `HomEnriched F U` are objects of `F` over `U`.
@[expose] def HomEnriched (U : C) : Type u' := F.obj (.mk (op U))

instance instEnrichedCategoryHomEnriched (U : C) :
    EnrichedCategory ((Over U)ᵒᵖ ⥤ Type v') (HomEnriched F U) where
  Hom M N := F.presheafHom (S := U) M N
  id M := presheafHomId M
  comp M N P := presheafHomComp M N P
  -- Objectwise, the tensor product of presheaves of types is the product, so each side is
  -- composition of local morphisms on a pair (`presheafHomComp_app_apply`), and the laws are those
  -- of the fibre of `F`. The arguments of `presheafHomComp_app_apply` and
  -- `presheafHomId_app_apply` are given explicitly: `simp` and `rw` cannot match them, because
  -- `(P ⊗ Q).obj T` is only definitionally `P.obj T × Q.obj T` and `HomEnriched F U` is a type
  -- synonym.
  id_comp M N := by
    ext T f
    calc _ = (presheafHomId M).app T PUnit.unit ≫ f := presheafHomComp_app_apply M M N T (_, f)
      _ = 𝟙 _ ≫ f := congrArg (· ≫ f) (presheafHomId_app_apply M T _)
      _ = f := Category.id_comp f
  comp_id M N := by
    ext T f
    calc _ = f ≫ (presheafHomId N).app T PUnit.unit := presheafHomComp_app_apply M N N T (f, _)
      _ = f ≫ 𝟙 _ := congrArg (f ≫ ·) (presheafHomId_app_apply N T _)
      _ = f := Category.comp_id f
  assoc M N P Q := by
    ext T ⟨f, g, h⟩
    calc _ = (presheafHomComp M N P).app T (f, g) ≫ h := presheafHomComp_app_apply M P Q T (_, h)
      _ = (f ≫ g) ≫ h := by rw [presheafHomComp_app_apply M N P T (f, g)]
      _ = f ≫ g ≫ h := Category.assoc f g h
      _ = f ≫ (presheafHomComp N P Q).app T (g, h) := by
        rw [presheafHomComp_app_apply N P Q T (g, h)]
      _ = _ := (presheafHomComp_app_apply M N Q T (f, _)).symm

section

variable (U : C) [HasSheafify (J.over U) (Type v')]

/-- The functor sending a presheaf of types on `Over U` to the sections of its sheafification
over the terminal object `Over.mk (𝟙 U)`. -/
-- The body is exposed so that its values are the sections of a sheafification.
@[expose] def sheafifySections : ((Over U)ᵒᵖ ⥤ Type v') ⥤ Type v' :=
  sheafification (J.over U) (Type v') ⋙ (evaluation _ _).obj (op (Over.mk (𝟙 U)))

instance preservesFiniteProducts_sheafifySections :
    PreservesFiniteProducts (sheafifySections J U) := by
  dsimp [sheafifySections]
  infer_instance

/-- The monoidal structure of `sheafifySections J U`, from its preservation of finite products. -/
instance monoidalSheafifySections : (sheafifySections J U).Monoidal := .ofChosenFiniteProducts _

/-- The value at the terminal object of the unit of sheafification. -/
def toSheafifySections : (evaluation _ _).obj (op (Over.mk (𝟙 U))) ⟶ sheafifySections J U :=
  Functor.whiskerRight (toSheafification (J.over U) (Type v'))
    ((evaluation _ _).obj (op (Over.mk (𝟙 U))))

@[simp]
lemma toSheafifySections_app (P : (Over U)ᵒᵖ ⥤ Type v') :
    (toSheafifySections J U).app P = (toSheafify (J.over U) P).app (op (Over.mk (𝟙 U))) := (rfl)

end

/-- The fibre over `U` of the Hom-sheafification of `F`: its objects are those of `F` over `U`,
and its morphisms from `M` to `N` are the sections over the terminal object of the
sheafification of `F.presheafHom M N`. -/
-- The body is exposed so that the enriched category structure of `TransportEnrichment` and the
-- objects of `F` over `U` can be used for it.
@[expose] def Fiber (U : C) [HasSheafify (J.over U) (Type v')] : Type u' :=
  TransportEnrichment (sheafifySections J U) (HomEnriched F U)

instance instEnrichedCategoryFiber (U : C) [HasSheafify (J.over U) (Type v')] :
    EnrichedCategory (Type v') (Fiber J F U) :=
  inferInstanceAs (EnrichedCategory (Type v')
    (TransportEnrichment (sheafifySections J U) (HomEnriched F U)))

instance instCategoryFiber (U : C) [HasSheafify (J.over U) (Type v')] :
    Category.{v'} (Fiber J F U) :=
  categoryOfEnrichedCategoryType _

variable {J F} {U : C} [HasSheafify (J.over U) (Type v')]

/-- An object of `F` over `U` as an object of the fibre of the Hom-sheafification. -/
-- This and `Fiber.obj` are exposed so that they are the identity by definition.
@[expose] def Fiber.mk (M : F.obj (.mk (op U))) : Fiber J F U := M

/-- The object of `F` underlying an object of the fibre of the Hom-sheafification. -/
@[expose] def Fiber.obj (M : Fiber J F U) : F.obj (.mk (op U)) := M

@[simp]
lemma Fiber.obj_mk (M : F.obj (.mk (op U))) : (Fiber.mk (J := J) M).obj = M := (rfl)

@[simp]
lemma Fiber.mk_obj (M : Fiber J F U) : Fiber.mk M.obj = M := (rfl)

open Functor.LaxMonoidal Functor.OplaxMonoidal

/-- The monoidal structure of `sheafifySections J U` is compatible with the unit of
sheafification: the pair of images of `x` and `y` corresponds to the image of `(x, y)`. -/
lemma μ_toSheafifySections {P Q : (Over U)ᵒᵖ ⥤ Type v'} (x : P.obj (op (Over.mk (𝟙 U))))
    (y : Q.obj (op (Over.mk (𝟙 U)))) :
    μ (sheafifySections J U) P Q ((toSheafifySections J U).app P x,
      (toSheafifySections J U).app Q y) =
      (toSheafifySections J U).app (P ⊗ Q) ((x, y) : (P ⊗ Q).obj (op (Over.mk (𝟙 U)))) := by
  -- Evaluation at the terminal object preserves finite products, so `toSheafifySections J U` is
  -- a monoidal natural transformation (`NatTrans.IsMonoidal.of_cartesianMonoidalCategory`), and
  -- the monoidal structure of evaluation is the identity on pairs.
  let _ : ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))).Monoidal := .ofChosenFiniteProducts _
  have hδ : δ ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))) P Q = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (Functor.OplaxMonoidal.δ_fst _ P Q).trans (Category.id_comp _).symm
    · exact (Functor.OplaxMonoidal.δ_snd _ P Q).trans (Category.id_comp _).symm
  have hμ : μ ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))) P Q = 𝟙 _ := by
    have h := Functor.Monoidal.μ_δ ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))) P Q
    rw [hδ] at h
    exact (Category.comp_id _).symm.trans h
  have := ConcreteCategory.congr_hom (NatTrans.IsMonoidal.tensor (τ := toSheafifySections J U) P Q)
    (show P.obj (op (Over.mk (𝟙 U))) × Q.obj (op (Over.mk (𝟙 U))) from (x, y))
  simp only [evaluation_obj_obj, Monoidal.tensorObj_obj, hμ, toSheafifySections_app,
    ConcreteCategory.comp_apply] at this
  exact this.symm

/-- The morphisms of the fibre of the Hom-sheafification are the sections over the terminal
object of the sheafified presheaves of morphisms of `F`. -/
def Fiber.homEquiv (M N : Fiber J F U) :
    (M ⟶ N) ≃ (sheafifySections J U).obj (F.presheafHom M.obj N.obj) :=
  Equiv.refl _

lemma Fiber.homEquiv_comp {M N P : Fiber J F U} (f : M ⟶ N) (g : N ⟶ P) :
    Fiber.homEquiv M P (f ≫ g) = (μ (sheafifySections J U) _ _ ≫ (sheafifySections J U).map
      (presheafHomComp M.obj N.obj P.obj)) ((Fiber.homEquiv M N f, Fiber.homEquiv N P g) :
        (_ ⊗ _)) := (rfl)

/-- The identity of `M` in the fibre of the Hom-sheafification is the image of `PUnit.unit` under
the unit morphism `ε` of the monoidal functor `sheafifySections J U` followed by the image of the
identities of local morphisms. -/
-- This holds by definition of the category obtained by transporting the enrichment
-- (`TransportEnrichment`) and of the category of a type-enriched category
-- (`categoryOfEnrichedCategoryType`).
lemma Fiber.homEquiv_id (M : Fiber J F U) :
    Fiber.homEquiv M M (𝟙 M) =
      (ε (sheafifySections J U) ≫ (sheafifySections J U).map (presheafHomId M.obj))
        PUnit.unit := (rfl)

@[ext]
lemma Fiber.hom_ext {M N : Fiber J F U} {f g : M ⟶ N}
    (h : Fiber.homEquiv M N f = Fiber.homEquiv M N g) : f = g :=
  (Fiber.homEquiv M N).injective h

/-- The morphism of the fibre of the Hom-sheafification given by a morphism `x` of `F` over `U`,
written as a section over the terminal object of `F.presheafHom M N`. -/
def Fiber.homMk {M N : Fiber J F U} (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U)))) :
    M ⟶ N :=
  (Fiber.homEquiv M N).symm ((toSheafifySections J U).app _ x)

@[simp]
lemma Fiber.homEquiv_homMk {M N : Fiber J F U}
    (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U)))) :
    Fiber.homEquiv M N (Fiber.homMk x) =
      (toSheafifySections J U).app (F.presheafHom M.obj N.obj) x :=
  Equiv.apply_symm_apply _ _

/-- The composite of the morphisms given by local morphisms `x` and `y` is the morphism given by
`x ≫ y`. -/
@[simp, reassoc]
lemma Fiber.homMk_comp {M N P : Fiber J F U}
    (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U))))
    (y : (F.presheafHom N.obj P.obj).obj (op (Over.mk (𝟙 U)))) :
    Fiber.homMk x ≫ Fiber.homMk y = Fiber.homMk (M := M) (N := P) (x ≫ y) := by
  ext
  rw [Fiber.homEquiv_comp, ConcreteCategory.comp_apply, Fiber.homEquiv_homMk,
    Fiber.homEquiv_homMk, Fiber.homEquiv_homMk, μ_toSheafifySections]
  refine (ConcreteCategory.congr_hom ((toSheafifySections J U).naturality
    (presheafHomComp M.obj N.obj P.obj))
    ((x, y) : (F.presheafHom M.obj N.obj ⊗ F.presheafHom N.obj P.obj).obj _)).symm.trans ?_
  exact congrArg ((toSheafifySections J U).app _)
    (presheafHomComp_app_apply M.obj N.obj P.obj _ (x, y))

/-- The morphism given by the identity local morphism is the identity. -/
lemma Fiber.homMk_id (M : Fiber J F U) : Fiber.homMk (𝟙 _) = 𝟙 M := by
  ext
  -- `toSheafifySections J U` is compatible with the units, as a monoidal natural transformation
  -- (`NatTrans.IsMonoidal.of_cartesianMonoidalCategory`).
  let _ : ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))).Monoidal := .ofChosenFiniteProducts _
  have hε : ε (sheafifySections J U) PUnit.unit =
      (toSheafifySections J U).app (𝟙_ ((Over U)ᵒᵖ ⥤ Type v')) PUnit.unit :=
    (ConcreteCategory.congr_hom (NatTrans.IsMonoidal.unit (τ := toSheafifySections J U))
      PUnit.unit).symm
  rw [Fiber.homEquiv_homMk, Fiber.homEquiv_id, ConcreteCategory.comp_apply, hε]
  exact (congrArg ((toSheafifySections J U).app _)
    (presheafHomId_app_apply M.obj _ PUnit.unit)).symm.trans
    (ConcreteCategory.congr_hom ((toSheafifySections J U).naturality (presheafHomId M.obj)) _)

variable (J F U) in
/-- The comparison functor from the fibre of `F` over `U` to the fibre of its
Hom-sheafification. It is the identity on objects. -/
-- The body is exposed so that the comparison functor is the identity on objects by definition.
@[expose] def toFiber : F.obj (.mk (op U)) ⥤ Fiber J F U where
  obj M := Fiber.mk M
  map φ := Fiber.homMk (F.presheafHomObjHomEquiv φ)
  map_id M := by
    rw [← Fiber.homMk_id]
    exact congrArg _ (presheafHomObjHomEquiv_id F M)
  map_comp φ ψ := by
    rw [Fiber.homMk_comp]
    exact congrArg _ (presheafHomObjHomEquiv_comp F φ ψ)

@[simp]
lemma toFiber_obj (M : F.obj (.mk (op U))) : (toFiber J F U).obj M = Fiber.mk M := (rfl)

@[simp]
lemma toFiber_map {M N : F.obj (.mk (op U))} (φ : M ⟶ N) :
    (toFiber J F U).map φ = Fiber.homMk (F.presheafHomObjHomEquiv φ) := (rfl)

instance essSurj_toFiber : (toFiber J F U).EssSurj where
  mem_essImage M := ⟨M.obj, ⟨Iso.refl _⟩⟩

/-- For a prestack, the comparison functor is bijective on morphisms. -/
lemma toFiber_map_bijective [F.IsPrestack J] (M N : F.obj (.mk (op U))) :
    Function.Bijective ((toFiber J F U).map : (M ⟶ N) → _) := by
  have := isIso_toSheafify (J.over U) (IsPrestack.isSheaf J M N)
  have hη : Function.Bijective ((toSheafifySections J U).app (F.presheafHom M N)) := by
    rw [toSheafifySections_app]
    exact (isIso_iff_bijective _).1 (NatIso.isIso_app_of_isIso _ _)
  exact (Fiber.homEquiv (Fiber.mk M) (Fiber.mk N)).symm.bijective.comp
    (hη.comp F.presheafHomObjHomEquiv.bijective)

instance full_toFiber [F.IsPrestack J] : (toFiber J F U).Full where
  map_surjective := (toFiber_map_bijective _ _).2

instance faithful_toFiber [F.IsPrestack J] : (toFiber J F U).Faithful where
  map_injective h := (toFiber_map_bijective _ _).1 h

variable (J F U) in
/-- For a prestack `F`, the comparison functor from the fibre of `F` over `U` to the fibre of
its Hom-sheafification is an equivalence. -/
def toFiberEquivalence [F.IsPrestack J] : F.obj (.mk (op U)) ≌ Fiber J F U :=
  have : (toFiber J F U).IsEquivalence := { }
  (toFiber J F U).asEquivalence

@[simp]
lemma toFiberEquivalence_functor [F.IsPrestack J] :
    (toFiberEquivalence J F U).functor = toFiber J F U := (rfl)

end TauCeti.Stack.Prestackification
end
