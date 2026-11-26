/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
public import TauCeti.CategoryTheory.Sites.CoverLifting
public import TauCeti.CategoryTheory.Sites.Descent.Stackification.HomSheafification

/-!
# The Hom-sheafification of a pseudofunctor

Let `F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat` be a pseudofunctor and `J` a Grothendieck topology on `C`.
The stackification of `F` is obtained by Hom-sheafification followed by adjoining descent data
(Stacks, Section 02ZM and Lemma 02ZN); the second step, for prestacks, is
`TauCeti.Stack.stackification`. This file makes the fibres `Fiber J F U` of
`TauCeti.CategoryTheory.Sites.Descent.Stackification.HomSheafification`, whose morphisms
`M ⟶ N` are the sections over the terminal object of the sheafification of `F.presheafHom M N`,
into a pseudofunctor `prestackification J F`, the Hom-sheafification of `F`, and proves that it
is a prestack whose presheaves of morphisms are the sheafifications of those of `F`.

The pullback of a morphism along `f : V ⟶ U` restricts the corresponding section to
`Over.mk f`, identifies the sections of the restriction of a sheafification along `Over.map f`
with those of the sheafification of the restriction
(`CategoryTheory.Functor.sheafPushforwardContinuousPresheafToSheafIso`, which needs that the
morphisms inverted by sheafification are the locally bijective ones, on every slice site), and
identifies the restricted presheaf of morphisms with that of the pullbacks (Mathlib's
`Pseudofunctor.overMapCompPresheafHomIso`). This pullback is functorial
(`Fiber.pullbackHom_comp`) because the restriction of sections is a natural transformation between
functors preserving finite products, hence monoidal. More generally, the sections over any
`T : Over U` of the sheafified presheaf of morphisms are the morphisms between the pullbacks to
`T.left` (`sheafifyPresheafHomEquiv`), compatibly with pullbacks and with the comparison
isomorphisms of `F` (`toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp`,
`sheafifyPresheafHomEquiv_mkId`). This gives the naturality of the unit and composition
isomorphisms, which are the images under `toFiber` of those of `F`, and the isomorphism of
presheaves of morphisms; the coherence conditions are the images of those of `F`.

The comparison functors `toFiber` form a strong transformation `toPrestackification` from `F`,
whose naturality isomorphisms are identities. For a prestack `F` it is an equivalence of
pseudofunctors (`toPrestackificationEquivalence`). The Hom-sheafification takes values in the
universes of `F`, so no universe lift is needed; this covers the big site `Over S` of
`S : Scheme.{u}` with `F` valued in `Cat.{u, u + 1}`, given sheafification of the presheaves of
morphisms. Both hypotheses on the slice sites hold automatically when the morphisms of `F` lie in
`Type (max u v)` for `C : Type u` with `Category.{v} C`.

## Main declarations

* `TauCeti.Stack.Prestackification.restrictSectionsOver`: the sections over `T` of a
  sheafification as sections over the terminal object of the sheafification of the restriction to
  `Over T.left`, with `restrictSectionsOver_comp` and `restrictSectionsOver_mkId`.
* `TauCeti.Stack.Prestackification.Fiber.pullback`: the pullback functors between the fibres.
* `TauCeti.Stack.Prestackification.sheafifyPresheafHomEquiv`: sections over `T` of the sheafified
  presheaf of morphisms as morphisms between pullbacks.
* `TauCeti.Stack.Prestackification.prestackification`: the Hom-sheafification of `F`.
* `TauCeti.Stack.Prestackification.prestackificationPresheafHomIso`: its presheaves of morphisms
  are the sheafifications of those of `F`, and `isPrestack_prestackification`.
* `TauCeti.Stack.Prestackification.toPrestackification`: the strong transformation from `F` with
  components `toFiber`, and `toPrestackificationEquivalence`, an equivalence for a prestack `F`.

## References

* [Stacks Project, Section 02ZM](https://stacks.math.columbia.edu/tag/02ZM)
* [Stacks Project, Lemma 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
-/

public section

noncomputable section

universe v' u' v u

open CategoryTheory Limits Opposite MonoidalCategory Bicategory Pseudofunctor
  LocallyDiscreteOpToCat

namespace TauCeti.Stack.Prestackification

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section restrictSections

variable [∀ U : C, HasSheafify (J.over U) (Type v')]
  [∀ U : C, (J.over U).WEqualsLocallyBijective (Type v')]

/-- The morphism `(Over.map T.hom).obj (Over.mk (𝟙 T.left)) ⟶ T` of `Over U` whose underlying
morphism is the identity of `T.left`. -/
abbrev overMapMkIdHom {U : C} (T : Over U) : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ⟶ T :=
  Over.homMk (𝟙 T.left)

/-- The sections over `T : Over U` of the sheafification of a presheaf `P` on `Over U`, as
sections over the terminal object of the sheafification of the restriction of `P` to
`Over T.left`. This is the restriction of sheafifications along `Over.map T.hom`
(`Functor.sheafPushforwardContinuousPresheafToSheafIso`), evaluated at the terminal object. -/
def restrictSectionsOver {U : C} (T : Over U) :
    sheafification (J.over U) (Type v') ⋙ (evaluation _ _).obj (op T) ⟶
      (Functor.whiskeringLeft _ _ (Type v')).obj (Over.map T.hom).op ⋙
        sheafifySections J T.left where
  app P := (sheafify (J.over U) P).map (overMapMkIdHom T).op ≫
    ((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso (J.over T.left) (J.over U)
      P).hom.hom.app (op (Over.mk (𝟙 T.left)))
  naturality P Q φ := by
    have h := congrArg (fun α ↦ α.hom.app (op (Over.mk (𝟙 T.left))))
      ((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso_hom_naturality
        (J.over T.left) (J.over U) φ)
    dsimp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
    -- Both sides are the naturality square of `sheafifyMap φ` along `overMapMkIdHom T` followed by
    -- `h`; the restriction of `sheafifyMap φ` is `sheafifyMap φ` only after unfolding, so the
    -- steps are combined by `exact`.
    exact ((sheafifyMap (J.over U) φ).naturality_assoc (overMapMkIdHom T).op _).symm.trans
      ((congrArg ((sheafify (J.over U) P).map (overMapMkIdHom T).op ≫ ·) h).trans
        (Category.assoc _ _ _).symm)

/-- `restrictSectionsOver` sends the image of a section of `P` over `T` to the image of its
restriction. -/
lemma restrictSectionsOver_app_toSheafify {U : C} (T : Over U) (P : (Over U)ᵒᵖ ⥤ Type v')
    (x : P.obj (op T)) :
    (restrictSectionsOver J T).app P ((toSheafify (J.over U) P).app (op T) x) =
      (toSheafifySections J T.left).app ((Over.map T.hom).op ⋙ P)
        (P.map (overMapMkIdHom T).op x) := by
  -- The restriction of `toSheafify P` followed by the comparison of sheafifications is
  -- `toSheafify` of the restriction of `P`.
  have h := congrArg (fun α ↦ α.app (op (Over.mk (𝟙 T.left))) (P.map (overMapMkIdHom T).op x))
    (Functor.whiskerLeft_toSheafify_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
      (Over.map T.hom) (J.over T.left) (J.over U) P)
  rw [toSheafifySections_app]
  exact (congrArg (((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso (J.over T.left)
    (J.over U) P).hom.hom.app (op (Over.mk (𝟙 T.left))))
      (ConcreteCategory.congr_hom ((toSheafify (J.over U) P).naturality
        (overMapMkIdHom T).op) x).symm).trans h

lemma bijective_restrictSectionsOver_app {U : C} (T : Over U) (P : (Over U)ᵒᵖ ⥤ Type v') :
    Function.Bijective ((restrictSectionsOver J T).app P) :=
  ((sheafify (J.over U) P).mapIso
      (Over.isoMk (Iso.refl T.left) : (Over.map T.hom).obj (Over.mk (𝟙 T.left)) ≅ T).op ≪≫
    ((sheafToPresheaf _ _).mapIso ((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso
      (J.over T.left) (J.over U) P)).app (op (Over.mk (𝟙 T.left)))).toEquiv.bijective

variable {U V : C} (f : V ⟶ U)

/-- Restricting the sections over the terminal object of the sheafification of a presheaf on
`Over U` along `f : V ⟶ U`: the sections over `Over.mk (𝟙 V)` of the sheafification of the
restriction of the presheaf to `Over V`. -/
def restrictSections :
    sheafifySections J U ⟶
      (Functor.whiskeringLeft _ _ (Type v')).obj (Over.map f).op ⋙ sheafifySections J V :=
  Functor.whiskerLeft (sheafification (J.over U) (Type v'))
      ((evaluation _ _).map (Over.mkIdTerminal.from (Over.mk f)).op) ≫
    restrictSectionsOver J (Over.mk f)

lemma restrictSections_app {P : (Over U)ᵒᵖ ⥤ Type v'} (s : (sheafifySections J U).obj P) :
    (restrictSections J f).app P s = (restrictSectionsOver J (Over.mk f)).app P
      ((sheafify (J.over U) P).map (Over.mkIdTerminal.from (Over.mk f)).op s) := (rfl)

/-- `restrictSections` sends the image of a section of `P` over the terminal object to the image
of its restriction. -/
lemma restrictSections_app_toSheafifySections (P : (Over U)ᵒᵖ ⥤ Type v')
    (x : P.obj (op (Over.mk (𝟙 U)))) :
    (restrictSections J f).app P ((toSheafifySections J U).app P x) =
      (toSheafifySections J V).app ((Over.map f).op ⋙ P)
        (P.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op x) := by
  have hP : P.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op =
      P.map (Over.mkIdTerminal.from (Over.mk f)).op ≫ P.map (overMapMkIdHom (Over.mk f)).op := by
    rw [← Functor.map_comp, ← op_comp]
    exact congrArg (fun g ↦ P.map g.op) (Over.mkIdTerminal.hom_ext _ _)
  rw [restrictSections_app, toSheafifySections_app]
  refine (congrArg ((restrictSectionsOver J (Over.mk f)).app P) (ConcreteCategory.congr_hom
    ((toSheafify (J.over U) P).naturality (Over.mkIdTerminal.from (Over.mk f)).op) x).symm).trans
      ((restrictSectionsOver_app_toSheafify J (Over.mk f) P _).trans ?_)
  exact congrArg _ (ConcreteCategory.congr_hom hP x).symm

/-- For `p : T' ⟶ T` in `Over U`, the identification of `Over.map T'.hom` with the composite of
`Over.map p.left` and `Over.map T.hom`. -/
abbrev overMapCompIso {U : C} {T T' : Over U} (p : T' ⟶ T) :
    Over.map T'.hom ≅ Over.map p.left ⋙ Over.map T.hom :=
  Over.mapCongr T'.hom (p.left ≫ T.hom) (Over.w p).symm ≪≫ Over.mapComp p.left T.hom

/-- Restricting sections over `T` to the terminal object and then along `p.left` is restricting
them along `p : T' ⟶ T` and then to the terminal object, up to the identification
`overMapCompIso p` of the restrictions of `P`. -/
lemma restrictSectionsOver_comp {U : C} {T T' : Over U} (p : T' ⟶ T) (P : (Over U)ᵒᵖ ⥤ Type v')
    (t : (sheafify (J.over U) P).obj (op T)) :
    (sheafifySections J T'.left).map (Functor.whiskerRight (NatTrans.op (overMapCompIso p).hom) P)
        ((restrictSections J p.left).app _ ((restrictSectionsOver J T).app P t)) =
      (restrictSectionsOver J T').app P ((sheafify (J.over U) P).map p.op t) := by
  have : (Over.map p.left ⋙ Over.map T.hom).IsContinuous (J.over T'.left) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over T.left) _
  have : (Over.map p.left ⋙ Over.map T.hom).IsCocontinuous (J.over T'.left) (J.over U) :=
    isCocontinuous_comp _ _ (J.over T'.left) (J.over T.left)
  have hB :=
    Functor.whiskerLeft_sheafPushforwardContinuousPresheafToSheafIso_hom_hom_comp_hom_hom
      (Over.map T.hom) (J.over T.left) (J.over U) (Over.map p.left) (J.over T'.left) P
  have hC := Functor.whiskerRight_op_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
    (Over.map T'.hom) (J.over T'.left) (J.over U) (overMapCompIso p).hom P
  -- the morphism of `Over U` along which the sections are restricted on the left
  let k : (Over.map T.hom).obj ((Over.map p.left).obj (Over.mk (𝟙 T'.left))) ⟶ T :=
    (Over.map T.hom).map (overMapMkIdHom (Over.mk p.left) ≫
      Over.mkIdTerminal.from (Over.mk p.left)) ≫ overMapMkIdHom T
  have hk : (overMapCompIso p).hom.app (Over.mk (𝟙 T'.left)) ≫ k = overMapMkIdHom T' ≫ p := by
    ext
    simp [k]
  -- restricting along `Over.mkIdTerminal.from` and then `overMapMkIdHom` commutes with the
  -- comparison of sheafifications for `Over.map T.hom`
  have S₁ : (sheafify (J.over T.left) ((Over.map T.hom).op ⋙ P)).map
      (overMapMkIdHom (Over.mk p.left)).op
        ((sheafify (J.over T.left) ((Over.map T.hom).op ⋙ P)).map
          (Over.mkIdTerminal.from (Over.mk p.left)).op
            ((restrictSectionsOver J T).app P t)) =
      ((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso (J.over T.left) (J.over U)
        P).hom.hom.app _ ((sheafify (J.over U) P).map k.op t) := by
    have n := ConcreteCategory.congr_hom
      (((Over.map T.hom).sheafPushforwardContinuousPresheafToSheafIso
        (J.over T.left) (J.over U) P).hom.hom.naturality (overMapMkIdHom (Over.mk p.left) ≫
        Over.mkIdTerminal.from (Over.mk p.left)).op)
          ((sheafify (J.over U) P).map (overMapMkIdHom T).op t)
    have m := ConcreteCategory.congr_hom
      ((sheafify (J.over T.left) ((Over.map T.hom).op ⋙ P)).map_comp
        (Over.mkIdTerminal.from (Over.mk p.left)).op (overMapMkIdHom (Over.mk p.left)).op)
        ((restrictSectionsOver J T).app P t)
    have l := ConcreteCategory.congr_hom ((sheafify (J.over U) P).map_comp (overMapMkIdHom T).op
      ((Over.map T.hom).map (overMapMkIdHom (Over.mk p.left) ≫
        Over.mkIdTerminal.from (Over.mk p.left))).op) t
    exact m.symm.trans (n.symm.trans (congrArg _ l.symm))
  -- Unfolding the restrictions on the left, the claim follows from `S₁`, `hB`, `hC` and `hk`.
  refine (congrArg (fun z ↦ (sheafifyMap (J.over T'.left)
    (Functor.whiskerRight (NatTrans.op (overMapCompIso p).hom) P)).app _
      (((Over.map p.left).sheafPushforwardContinuousPresheafToSheafIso (J.over T'.left)
        (J.over T.left) ((Over.map T.hom).op ⋙ P)).hom.hom.app _ z)) S₁).trans ?_
  refine (congrArg ((sheafifyMap (J.over T'.left)
    (Functor.whiskerRight (NatTrans.op (overMapCompIso p).hom) P)).app _)
      (ConcreteCategory.congr_hom (NatTrans.congr_app hB _) _)).trans ?_
  refine (ConcreteCategory.congr_hom (NatTrans.congr_app hC _) _).symm.trans ?_
  have h := congrArg (fun g ↦ (sheafify (J.over U) P).map g.op t) hk
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at h
  exact congrArg (((Over.map T'.hom).sheafPushforwardContinuousPresheafToSheafIso (J.over T'.left)
    (J.over U) P).hom.hom.app _) h

/-- Restricting sections over the terminal object of `Over U` to the terminal object gives them
back, up to the identification `Over.mapId U` of `Over.map (𝟙 U)` with the identity. -/
lemma restrictSectionsOver_mkId {U : C} (P : (Over U)ᵒᵖ ⥤ Type v')
    (s : (sheafifySections J U).obj P) :
    (sheafifySections J U).map (Functor.whiskerRight (NatTrans.op (Over.mapId U).inv) P)
        ((restrictSectionsOver J (Over.mk (𝟙 U))).app P s) = s := by
  have hC := Functor.whiskerRight_op_comp_sheafPushforwardContinuousPresheafToSheafIso_hom_hom
    (𝟭 (Over U)) (J.over U) (J.over U) (G' := Over.map (𝟙 U)) (Over.mapId U).inv P
  have hI := Functor.sheafPushforwardContinuousPresheafToSheafIso_id_hom_hom (J.over U) P
  refine (ConcreteCategory.congr_hom (NatTrans.congr_app hC _) _).symm.trans
    ((ConcreteCategory.congr_hom (NatTrans.congr_app hI _) _).trans ?_)
  have h := congrArg (fun g ↦ (sheafify (J.over U) P).map g.op s)
    (Over.mkIdTerminal.hom_ext ((Over.mapId U).inv.app (Over.mk (𝟙 U)) ≫
      overMapMkIdHom (Over.mk (𝟙 U))) (𝟙 _))
  simp only [op_comp, Functor.map_comp, op_id] at h
  exact h.trans (ConcreteCategory.congr_hom ((sheafify (J.over U) P).map_id _) s)

end restrictSections

section pullback

variable {J} [∀ U : C, HasSheafify (J.over U) (Type v')]
  [∀ U : C, (J.over U).WEqualsLocallyBijective (Type v')] {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}}
  {U V : C}

/-- The pullback along `f : V ⟶ U` of a morphism of the fibre over `U` of the Hom-sheafification
of `F`: the restriction of the corresponding section of the sheafified presheaf of morphisms
(`restrictSections`), transported along Mathlib's identification
`Pseudofunctor.overMapCompPresheafHomIso` of the restricted presheaf of morphisms with the
presheaf of morphisms between the pullbacks. -/
def Fiber.pullbackHom (f : V ⟶ U) {M N : Fiber J F U} (s : M ⟶ N) :
    Fiber.mk (J := J) ((F.map f.op.toLoc).toFunctor.obj M.obj) ⟶
      Fiber.mk ((F.map f.op.toLoc).toFunctor.obj N.obj) :=
  (Fiber.homEquiv _ _).symm ((sheafifySections J V).map
    (F.overMapCompPresheafHomIso M.obj N.obj f).hom
      ((restrictSections J f).app _ (Fiber.homEquiv M N s)))

lemma Fiber.homEquiv_pullbackHom (f : V ⟶ U) {M N : Fiber J F U} (s : M ⟶ N) :
    Fiber.homEquiv _ _ (Fiber.pullbackHom f s) = (sheafifySections J V).map
      (F.overMapCompPresheafHomIso M.obj N.obj f).hom
        ((restrictSections J f).app _ (Fiber.homEquiv M N s)) :=
  Equiv.apply_symm_apply _ _

/-- The pullback of the morphism given by a local morphism `x` is the morphism given by the
pullback of `x`. -/
lemma Fiber.pullbackHom_homMk (f : V ⟶ U) {M N : Fiber J F U}
    (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U)))) :
    Fiber.pullbackHom f (Fiber.homMk x) = Fiber.homMk
      ((F.overMapCompPresheafHomIso M.obj N.obj f).hom.app _
        ((F.presheafHom M.obj N.obj).map
          (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op x)) := by
  ext
  rw [Fiber.homEquiv_pullbackHom, Fiber.homEquiv_homMk, restrictSections_app_toSheafifySections]
  exact (ConcreteCategory.congr_hom ((toSheafifySections J V).naturality
    (F.overMapCompPresheafHomIso M.obj N.obj f).hom) _).symm.trans (Fiber.homEquiv_homMk _).symm

open Functor.LaxMonoidal Functor.OplaxMonoidal in
lemma Fiber.pullbackHom_comp (f : V ⟶ U) {M N P : Fiber J F U} (s : M ⟶ N) (t : N ⟶ P) :
    Fiber.pullbackHom f (s ≫ t) = Fiber.pullbackHom f s ≫ Fiber.pullbackHom f t := by
  let R := (Functor.whiskeringLeft (Over V)ᵒᵖ (Over U)ᵒᵖ (Type v')).obj (Over.map f).op
  let _ : R.Monoidal := .ofChosenFiniteProducts _
  -- The monoidal structure of the restriction `R` is the identity, as for evaluation in
  -- `μ_toSheafifySections`.
  have hδ : δ R (F.presheafHom M.obj N.obj) (F.presheafHom N.obj P.obj) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact (Functor.OplaxMonoidal.δ_fst _ _ _).trans (Category.id_comp _).symm
    · exact (Functor.OplaxMonoidal.δ_snd _ _ _).trans (Category.id_comp _).symm
  have hμ : μ R (F.presheafHom M.obj N.obj) (F.presheafHom N.obj P.obj) = 𝟙 _ := by
    have h := Functor.Monoidal.μ_δ R (F.presheafHom M.obj N.obj) (F.presheafHom N.obj P.obj)
    rw [hδ] at h
    exact (Category.comp_id _).symm.trans h
  -- Restricting presheaves of morphisms and then identifying them with the presheaves of
  -- morphisms between pullbacks is compatible with composition of local morphisms.
  have key : μ R _ _ ≫ R.map (presheafHomComp M.obj N.obj P.obj) ≫
      (F.overMapCompPresheafHomIso M.obj P.obj f).hom =
      ((F.overMapCompPresheafHomIso M.obj N.obj f).hom ⊗ₘ
        (F.overMapCompPresheafHomIso N.obj P.obj f).hom) ≫ presheafHomComp _ _ _ := by
    ext Z x
    have h : (μ R _ _).app Z x = x := ConcreteCategory.congr_hom (NatTrans.congr_app hμ Z) x
    refine (congrArg (fun y ↦ (F.overMapCompPresheafHomIso M.obj P.obj f).hom.app Z
      ((presheafHomComp M.obj N.obj P.obj).app _ y)) h).trans ?_
    exact (congrArg ((F.overMapCompPresheafHomIso M.obj P.obj f).hom.app Z)
      (presheafHomComp_app_apply _ _ _ _ x)).trans
        ((overMapCompPresheafHomIso_hom_app_comp f Z _ _).trans
          (presheafHomComp_app_apply _ _ _ Z
            (((F.overMapCompPresheafHomIso M.obj N.obj f).hom ⊗ₘ
              (F.overMapCompPresheafHomIso N.obj P.obj f).hom).app Z x)).symm)
  have key' := congrArg (sheafifySections J V).map key
  simp only [Functor.map_comp] at key'
  -- The same compatibility for the sheafified presheaves, from the monoidality of
  -- `restrictSections J f`.
  have H : μ (sheafifySections J U) _ _ ≫
      (sheafifySections J U).map (presheafHomComp M.obj N.obj P.obj) ≫
        (restrictSections J f).app _ ≫
          (sheafifySections J V).map (F.overMapCompPresheafHomIso M.obj P.obj f).hom =
      (((restrictSections J f).app _ ≫
          (sheafifySections J V).map (F.overMapCompPresheafHomIso M.obj N.obj f).hom) ⊗ₘ
        ((restrictSections J f).app _ ≫
          (sheafifySections J V).map (F.overMapCompPresheafHomIso N.obj P.obj f).hom)) ≫
        μ (sheafifySections J V) _ _ ≫ (sheafifySections J V).map (presheafHomComp _ _ _) := by
    rw [NatTrans.naturality_assoc, ← Category.assoc (μ _ _ _),
      NatTrans.IsMonoidal.tensor (τ := restrictSections J f), comp_μ, Category.assoc,
      Category.assoc, Functor.comp_map, key', ← μ_natural_assoc,
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  ext
  rw [Fiber.homEquiv_pullbackHom, Fiber.homEquiv_comp, Fiber.homEquiv_comp,
    Fiber.homEquiv_pullbackHom, Fiber.homEquiv_pullbackHom]
  exact ConcreteCategory.congr_hom H (show (sheafifySections J U).obj (F.presheafHom M.obj N.obj) ×
    (sheafifySections J U).obj (F.presheafHom N.obj P.obj) from
      (Fiber.homEquiv M N s, Fiber.homEquiv N P t))

open Functor.LaxMonoidal in
lemma Fiber.pullbackHom_id (f : V ⟶ U) (M : Fiber J F U) :
    Fiber.pullbackHom f (𝟙 M) = 𝟙 _ := by
  let R := (Functor.whiskeringLeft (Over V)ᵒᵖ (Over U)ᵒᵖ (Type v')).obj (Over.map f).op
  let _ : R.Monoidal := .ofChosenFiniteProducts _
  have key : ε R ≫ R.map (presheafHomId M.obj) ≫ (F.overMapCompPresheafHomIso M.obj M.obj f).hom =
      presheafHomId _ := by
    ext Z x
    exact (congrArg ((F.overMapCompPresheafHomIso M.obj M.obj f).hom.app Z)
      (presheafHomId_app_apply M.obj _ _)).trans
        ((overMapCompPresheafHomIso_hom_app_id M.obj f Z).trans
          (presheafHomId_app_apply _ Z x).symm)
  have key' := congrArg (sheafifySections J V).map key
  simp only [Functor.map_comp] at key'
  have H : ε (sheafifySections J U) ≫ (sheafifySections J U).map (presheafHomId M.obj) ≫
      (restrictSections J f).app _ ≫
        (sheafifySections J V).map (F.overMapCompPresheafHomIso M.obj M.obj f).hom =
      ε (sheafifySections J V) ≫ (sheafifySections J V).map (presheafHomId _) := by
    rw [NatTrans.naturality_assoc, ← Category.assoc (ε _),
      NatTrans.IsMonoidal.unit (τ := restrictSections J f), comp_ε, Category.assoc,
      Functor.comp_map, key']
  ext
  rw [Fiber.homEquiv_pullbackHom, Fiber.homEquiv_id, Fiber.homEquiv_id]
  exact ConcreteCategory.congr_hom H PUnit.unit

variable (J F) in
/-- The pullback functor along `f : V ⟶ U` between the fibres of the Hom-sheafification of `F`. On
objects it is the pullback functor of `F`, and on morphisms it is `Fiber.pullbackHom`. -/
-- The body is exposed so that the pullback functor is that of `F` on objects by definition.
@[expose] def Fiber.pullback (f : V ⟶ U) : Fiber J F U ⥤ Fiber J F V where
  obj M := Fiber.mk ((F.map f.op.toLoc).toFunctor.obj M.obj)
  map := Fiber.pullbackHom f
  map_id := Fiber.pullbackHom_id f
  map_comp := Fiber.pullbackHom_comp f

@[simp]
lemma Fiber.pullback_obj (f : V ⟶ U) (M : Fiber J F U) :
    (Fiber.pullback J F f).obj M = Fiber.mk ((F.map f.op.toLoc).toFunctor.obj M.obj) := (rfl)

@[simp]
lemma Fiber.pullback_map (f : V ⟶ U) {M N : Fiber J F U} (s : M ⟶ N) :
    (Fiber.pullback J F f).map s = Fiber.pullbackHom f s := (rfl)

/-- The coherence of the comparison isomorphisms of `F` behind
`toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp`: conjugating a local morphism `w`
over `y` by the comparison isomorphisms along `x`, `z ≫ q` and along `q`, `z`, and then by the
pullback along `z` of the comparison along `x`, `q`, is conjugating its pullback along `g = 𝟙`
by the comparison along `x'`, `z`. -/
private lemma mapComp'_conj_eq {X₀ X₁ X₂ Y : C} (x : X₁ ⟶ X₀) (q : X₂ ⟶ X₁) (x' : X₂ ⟶ X₀)
    (hx' : q ≫ x = x') (z : Y ⟶ X₂) (y₁ y₂ : Y ⟶ X₀) (h₁ : (z ≫ q) ≫ x = y₁)
    (h₂ : z ≫ x' = y₂) (g : Y ⟶ Y) (hg : g = 𝟙 Y) (hgy : g ≫ y₁ = y₂)
    (M N : F.obj (.mk (op X₀)))
    (w : (F.map y₁.op.toLoc).toFunctor.obj M ⟶ (F.map y₁.op.toLoc).toFunctor.obj N) :
    (F.map z.op.toLoc).toFunctor.map ((F.mapComp' x.op.toLoc q.op.toLoc x'.op.toLoc
        (by rw [← hx']; rfl)).hom.toNatTrans.app M) ≫
      ((F.mapComp' q.op.toLoc z.op.toLoc (z ≫ q).op.toLoc).inv.toNatTrans.app _ ≫
        ((F.mapComp' x.op.toLoc (z ≫ q).op.toLoc y₁.op.toLoc
          (by rw [← h₁]; rfl)).inv.toNatTrans.app M ≫ w ≫
            (F.mapComp' x.op.toLoc (z ≫ q).op.toLoc y₁.op.toLoc
              (by rw [← h₁]; rfl)).hom.toNatTrans.app N) ≫
        (F.mapComp' q.op.toLoc z.op.toLoc (z ≫ q).op.toLoc).hom.toNatTrans.app _) ≫
      (F.map z.op.toLoc).toFunctor.map ((F.mapComp' x.op.toLoc q.op.toLoc x'.op.toLoc
        (by rw [← hx']; rfl)).inv.toNatTrans.app N) =
    (F.mapComp' x'.op.toLoc z.op.toLoc y₂.op.toLoc (by rw [← h₂]; rfl)).inv.toNatTrans.app M ≫
      pullHom w g y₂ y₂ hgy hgy ≫
        (F.mapComp' x'.op.toLoc z.op.toLoc y₂.op.toLoc
          (by rw [← h₂]; rfl)).hom.toNatTrans.app N := by
  subst hg hx'
  obtain rfl : y₂ = y₁ := by rw [← hgy, Category.id_comp]
  rw [pullHom_id]
  have hM := mapComp'_hom_app_comp_map_mapComp'_hom_app F x.op.toLoc q.op.toLoc z.op.toLoc
    (q ≫ x).op.toLoc (z ≫ q).op.toLoc y₂.op.toLoc rfl rfl (by rw [← h₂]; rfl)
    (by rw [← h₁]; rfl) M
  have hN := mapComp'_hom_app_comp_map_mapComp'_hom_app F x.op.toLoc q.op.toLoc z.op.toLoc
    (q ≫ x).op.toLoc (z ≫ q).op.toLoc y₂.op.toLoc rfl rfl (by rw [← h₂]; rfl)
    (by rw [← h₁]; rfl) N
  have hM' : (F.map z.op.toLoc).toFunctor.map
      ((F.mapComp' x.op.toLoc q.op.toLoc (q ≫ x).op.toLoc).hom.toNatTrans.app M) ≫
      (F.mapComp' q.op.toLoc z.op.toLoc (z ≫ q).op.toLoc).inv.toNatTrans.app _ ≫
        (F.mapComp' x.op.toLoc (z ≫ q).op.toLoc y₂.op.toLoc
          (by rw [← h₁]; rfl)).inv.toNatTrans.app M =
      (F.mapComp' (q ≫ x).op.toLoc z.op.toLoc y₂.op.toLoc
        (by rw [← h₂]; rfl)).inv.toNatTrans.app M := by
    rw [← cancel_epi ((F.mapComp' (q ≫ x).op.toLoc z.op.toLoc y₂.op.toLoc
      (by rw [← h₂]; rfl)).hom.toNatTrans.app M), reassoc_of% hM]
    simp
  have hN' : (F.mapComp' x.op.toLoc (z ≫ q).op.toLoc y₂.op.toLoc
        (by rw [← h₁]; rfl)).hom.toNatTrans.app N ≫
      (F.mapComp' q.op.toLoc z.op.toLoc (z ≫ q).op.toLoc).hom.toNatTrans.app _ ≫
        (F.map z.op.toLoc).toFunctor.map
          ((F.mapComp' x.op.toLoc q.op.toLoc (q ≫ x).op.toLoc).inv.toNatTrans.app N) =
      (F.mapComp' (q ≫ x).op.toLoc z.op.toLoc y₂.op.toLoc
        (by rw [← h₂]; rfl)).hom.toNatTrans.app N := by
    rw [← reassoc_of% hN, ← Functor.map_comp, Cat.Hom.hom_inv_id_toNatTrans_app,
      CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  simp only [Category.assoc]
  rw [reassoc_of% hM', hN']

variable (J) in
/-- The sections over `T : Over U` of the sheafification of the presheaf of morphisms from `M` to
`N` are the morphisms between the pullbacks of `M` and `N` to `T.left` in the fibre of the
Hom-sheafification. -/
def sheafifyPresheafHomEquiv (M N : F.obj (.mk (op U))) (T : Over U) :
    (sheafify (J.over U) (F.presheafHom M N)).obj (op T) ≃
      (Fiber.mk (J := J) ((F.map T.hom.op.toLoc).toFunctor.obj M) ⟶
        Fiber.mk ((F.map T.hom.op.toLoc).toFunctor.obj N)) :=
  Equiv.ofBijective (fun t ↦ (Fiber.homEquiv _ _).symm ((sheafifySections J T.left).map
      (F.overMapCompPresheafHomIso M N T.hom).hom ((restrictSectionsOver J T).app _ t)))
    ((Fiber.homEquiv _ _).symm.bijective.comp
      ((((sheafifySections J T.left).mapIso
        (F.overMapCompPresheafHomIso M N T.hom)).toEquiv.bijective).comp
          (bijective_restrictSectionsOver_app J T _)))

lemma Fiber.homEquiv_sheafifyPresheafHomEquiv (M N : F.obj (.mk (op U))) (T : Over U)
    (t : (sheafify (J.over U) (F.presheafHom M N)).obj (op T)) :
    Fiber.homEquiv _ _ (sheafifyPresheafHomEquiv J M N T t) = (sheafifySections J T.left).map
      (F.overMapCompPresheafHomIso M N T.hom).hom ((restrictSectionsOver J T).app _ t) :=
  Equiv.apply_symm_apply _ _

/-- The morphism corresponding to the image of a local morphism `x` in the sheafification is the
image of `x` under the comparison functor `toFiber`. -/
lemma sheafifyPresheafHomEquiv_toSheafify (M N : F.obj (.mk (op U))) (T : Over U)
    (x : (F.presheafHom M N).obj (op T)) :
    sheafifyPresheafHomEquiv J M N T ((toSheafify (J.over U) (F.presheafHom M N)).app (op T) x) =
      (toFiber J F T.left).map x := by
  -- Restricting `x` to `(Over.map T.hom).obj (Over.mk (𝟙 T.left))` and conjugating it by the
  -- comparison isomorphisms of `F` gives its pullback along the identity.
  have h : (F.overMapCompPresheafHomIso M N T.hom).hom.app (op (Over.mk (𝟙 T.left)))
      ((F.presheafHom M N).map (overMapMkIdHom T).op x) = F.presheafHomObjHomEquiv x := by
    -- The restriction of `x` is its `pullHom` along the identity, which conjugates by the same
    -- comparison isomorphisms.
    have hx : (F.presheafHom M N).map (overMapMkIdHom T).op x = pullHom x (𝟙 T.left)
        ((Over.map T.hom).obj (Over.mk (𝟙 T.left))).hom
        ((Over.map T.hom).obj (Over.mk (𝟙 T.left))).hom (by simp) (by simp) := (rfl)
    rw [overMapCompPresheafHomIso_hom_app_apply, presheafHomObjHomEquiv_eq_map, hx]
    simp [pullHom]
  apply Fiber.hom_ext
  rw [Fiber.homEquiv_sheafifyPresheafHomEquiv, restrictSectionsOver_app_toSheafify]
  refine (ConcreteCategory.congr_hom ((toSheafifySections J T.left).naturality
    (F.overMapCompPresheafHomIso M N T.hom).hom) _).symm.trans ?_
  exact (congrArg ((toSheafifySections J T.left).app _) h).trans (Fiber.homEquiv_homMk _).symm

/-- The pullback along `f` of a morphism of the fibre over `U` corresponds to the restriction of
the corresponding section to `Over.mk f`. -/
lemma Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv (f : V ⟶ U) {M N : Fiber J F U}
    (s : M ⟶ N) :
    Fiber.pullbackHom f s = sheafifyPresheafHomEquiv J M.obj N.obj (Over.mk f)
      ((sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
        (Over.mkIdTerminal.from (Over.mk f)).op (Fiber.homEquiv M N s)) := (rfl)

/-- Pulling back the morphism of the fibre over `T.left` corresponding to a section over `T`
along `p.left`, for `p : T' ⟶ T` in `Over U`, gives the morphism corresponding to the restricted
section over `T'`, up to the comparison isomorphisms of `F`. -/
lemma toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp (M N : F.obj (.mk (op U)))
    {T T' : Over U} (p : T' ⟶ T) (t : (sheafify (J.over U) (F.presheafHom M N)).obj (op T)) :
    (toFiber J F T'.left).map ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
        (by rw [← Over.w p]; rfl)).hom.toNatTrans.app M) ≫
      Fiber.pullbackHom p.left (sheafifyPresheafHomEquiv J M N T t) ≫
        (toFiber J F T'.left).map ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
          (by rw [← Over.w p]; rfl)).inv.toNatTrans.app N) =
      sheafifyPresheafHomEquiv J M N T' ((sheafify (J.over U) (F.presheafHom M N)).map p.op t) := by
  -- The comparison isomorphisms of `F` relate the two identifications of local morphisms.
  have key : (Functor.whiskerLeft (Over.map p.left).op (F.overMapCompPresheafHomIso M N T.hom).hom ≫
      (F.overMapCompPresheafHomIso ((F.map T.hom.op.toLoc).toFunctor.obj M)
        ((F.map T.hom.op.toLoc).toFunctor.obj N) p.left).hom) ≫
      presheafHomPostcomp ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
        (by rw [← Over.w p]; rfl)).inv.toNatTrans.app N) ≫
      presheafHomPrecomp ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
        (by rw [← Over.w p]; rfl)).hom.toNatTrans.app M) =
      Functor.whiskerRight (NatTrans.op (overMapCompIso p).hom) (F.presheafHom M N) ≫
        (F.overMapCompPresheafHomIso M N T'.hom).hom := by
    refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    have h := mapComp'_conj_eq T.hom p.left T'.hom (Over.w p) Z.unop.hom _ _ rfl rfl
      ((overMapCompIso p).hom.app Z.unop).left (by simp) (Over.w _) M N w
    simp only [Category.assoc] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, presheafHomPostcomp_app_apply, presheafHomPrecomp_app_apply,
      overMapCompPresheafHomIso_hom_app_apply, Category.assoc]
    -- The remaining component of `overMapCompPresheafHomIso` is at an object of the form
    -- `(Over.map p.left).op.obj Z`, at which its argument `w` is typed only up to unfolding.
    erw [overMapCompPresheafHomIso_hom_app_apply]
    simp only [Category.assoc]
    exact h
  have key' := congrArg (sheafifySections J T'.left).map key
  simp only [Functor.map_comp] at key'
  have hθ := ConcreteCategory.congr_hom ((restrictSections J p.left).naturality
    (F.overMapCompPresheafHomIso M N T.hom).hom) ((restrictSectionsOver J T).app _ t)
  apply Fiber.hom_ext
  refine (Fiber.homEquiv_toFiber_map_comp _ _).trans ?_
  erw [Fiber.homEquiv_comp_toFiber_map, Fiber.homEquiv_pullbackHom,
    Fiber.homEquiv_sheafifyPresheafHomEquiv, Fiber.homEquiv_sheafifyPresheafHomEquiv,
    ← restrictSectionsOver_comp J p]
  simp only [ConcreteCategory.comp_apply] at hθ
  erw [hθ]
  exact ConcreteCategory.congr_hom key' _

/-- The coherence of the comparison isomorphisms of `F` behind
`sheafifyPresheafHomEquiv_mkId`. -/
private lemma mapComp'_conj_mapId'_eq {X₀ Y : C} (z : Y ⟶ X₀) (y₁ : Y ⟶ X₀) (h₁ : z ≫ 𝟙 X₀ = y₁)
    (g : Y ⟶ Y) (hg : g = 𝟙 Y) (hgy : g ≫ y₁ = z) (M N : F.obj (.mk (op X₀)))
    (w : (F.map y₁.op.toLoc).toFunctor.obj M ⟶ (F.map y₁.op.toLoc).toFunctor.obj N) :
    (F.mapComp' (𝟙 X₀).op.toLoc z.op.toLoc y₁.op.toLoc (by rw [← h₁]; rfl)).inv.toNatTrans.app M ≫
        w ≫ (F.mapComp' (𝟙 X₀).op.toLoc z.op.toLoc y₁.op.toLoc
          (by rw [← h₁]; rfl)).hom.toNatTrans.app N =
      (F.map z.op.toLoc).toFunctor.map
          ((F.mapId' (𝟙 X₀).op.toLoc (by simp)).hom.toNatTrans.app M) ≫
        pullHom w g z z hgy hgy ≫ (F.map z.op.toLoc).toFunctor.map
          ((F.mapId' (𝟙 X₀).op.toLoc (by simp)).inv.toNatTrans.app N) := by
  subst hg
  obtain rfl : y₁ = z := by rw [← hgy, Category.id_comp]
  rw [pullHom_id]
  have hM := mapComp'_hom_app_comp_map_mapId'_hom_app F (𝟙 X₀).op.toLoc (by simp) y₁.op.toLoc
    (by simp) M
  have hN := mapComp'_hom_app_comp_map_mapId'_hom_app F (𝟙 X₀).op.toLoc (by simp) y₁.op.toLoc
    (by simp) N
  have hM' : (F.mapComp' (𝟙 X₀).op.toLoc y₁.op.toLoc y₁.op.toLoc
      (by simp)).inv.toNatTrans.app M = (F.map y₁.op.toLoc).toFunctor.map
        ((F.mapId' (𝟙 X₀).op.toLoc (by simp)).hom.toNatTrans.app M) := by
    rw [← cancel_epi ((F.mapComp' (𝟙 X₀).op.toLoc y₁.op.toLoc y₁.op.toLoc
      (by simp)).hom.toNatTrans.app M), hM, Cat.Hom.hom_inv_id_toNatTrans_app]
  have hN' : (F.mapComp' (𝟙 X₀).op.toLoc y₁.op.toLoc y₁.op.toLoc
      (by simp)).hom.toNatTrans.app N = (F.map y₁.op.toLoc).toFunctor.map
        ((F.mapId' (𝟙 X₀).op.toLoc (by simp)).inv.toNatTrans.app N) := by
    rw [← cancel_mono ((F.map y₁.op.toLoc).toFunctor.map
      ((F.mapId' (𝟙 X₀).op.toLoc (by simp)).hom.toNatTrans.app N)), hN, ← Functor.map_comp,
      Cat.Hom.inv_hom_id_toNatTrans_app, CategoryTheory.Functor.map_id]
    rfl
  rw [hM', hN']

variable (J) in
/-- The morphism of the fibre over `U` corresponding to a section over the terminal object
`Over.mk (𝟙 U)` is the morphism given by that section, up to the unit isomorphisms of `F`. -/
lemma sheafifyPresheafHomEquiv_mkId (M N : F.obj (.mk (op U)))
    (s : (sheafify (J.over U) (F.presheafHom M N)).obj (op (Over.mk (𝟙 U)))) :
    sheafifyPresheafHomEquiv J M N (Over.mk (𝟙 U)) s =
      (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) ≫
        (Fiber.homEquiv (Fiber.mk M) (Fiber.mk N)).symm s ≫
          (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app N) := by
  have key : (F.overMapCompPresheafHomIso M N (𝟙 U)).hom =
      Functor.whiskerRight (NatTrans.op (Over.mapId U).inv) (F.presheafHom M N) ≫
        presheafHomPostcomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app N) ≫
          presheafHomPrecomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) := by
    refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    have h := mapComp'_conj_mapId'_eq Z.unop.hom _ rfl ((Over.mapId U).inv.app Z.unop).left
      (by simp) (Over.w _) M N w
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerRight_app,
      presheafHomPrecomp_app_apply, overMapCompPresheafHomIso_hom_app_apply]
    -- As in `toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp`, the remaining component
    -- is at an object at which its argument is typed only up to unfolding.
    erw [presheafHomPostcomp_app_apply]
    exact h
  apply Fiber.hom_ext
  refine Eq.trans ?_ (Fiber.homEquiv_toFiber_map_comp _ _).symm
  erw [Fiber.homEquiv_comp_toFiber_map, Equiv.apply_symm_apply]
  refine Eq.trans ?_ (congrArg (fun z ↦ (sheafifySections J U).map
    (presheafHomPrecomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M))
      ((sheafifySections J U).map
        (presheafHomPostcomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app N)) z))
          (Equiv.apply_symm_apply (Fiber.homEquiv (Fiber.mk M) (Fiber.mk N)) s).symm)
  conv_rhs => rw [← restrictSectionsOver_mkId J _ s]
  erw [key]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  rfl

/-- The pullback functors are compatible with the comparison functors `toFiber`. -/
lemma Fiber.pullbackHom_toFiber_map (f : V ⟶ U) {M N : F.obj (.mk (op U))} (φ : M ⟶ N) :
    Fiber.pullbackHom f ((toFiber J F U).map φ) =
      (toFiber J F V).map ((F.map f.op.toLoc).toFunctor.map φ) := by
  have h : (F.overMapCompPresheafHomIso M N f).hom.app _ ((F.presheafHom M N).map
      (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op
        (F.presheafHomObjHomEquiv φ)) = F.presheafHomObjHomEquiv
          ((F.map f.op.toLoc).toFunctor.map φ) := by
    rw [presheafHom_map_presheafHomObjHomEquiv, overMapCompPresheafHomIso_hom_app_apply]
    -- The object `Over.mk (𝟙 V)` appears both as it is and as `unop (op _)`.
    erw [mapComp'_naturality_1]
    exact (presheafHomObjHomEquiv_eq_map F _).symm
  exact (Fiber.pullbackHom_homMk (M := Fiber.mk M) (N := Fiber.mk N) f _).trans
    (congrArg Fiber.homMk h)

variable (J F) in
/-- The unit isomorphisms of the pullback functors of the Hom-sheafification, given by the unit
isomorphisms of `F`. -/
def Fiber.pullbackId (U : C) : Fiber.pullback J F (𝟙 U) ≅ 𝟭 (Fiber J F U) :=
  NatIso.ofComponents (fun M ↦ (toFiber J F U).mapIso
      ((Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc (by simp))).app M.obj)) fun {M N} s ↦ by
    -- The pullback of `s` along `𝟙 U` is `s` conjugated by the unit isomorphisms of `F`.
    have hs : (sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
        (Over.mkIdTerminal.from (Over.mk (𝟙 U))).op (Fiber.homEquiv M N s) =
          Fiber.homEquiv M N s := by
      rw [show Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 _ from Over.mkIdTerminal.hom_ext _ _]
      exact ConcreteCategory.congr_hom ((sheafify (J.over U) _).map_id _) _
    have h := (Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv (𝟙 U) s).trans
      ((congrArg _ hs).trans (sheafifyPresheafHomEquiv_mkId J M.obj N.obj _))
    erw [Equiv.symm_apply_apply] at h
    exact (congrArg (· ≫ _) h).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (s ≫ ·) ((toFiber J F U).mapIso
        ((Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc (by simp))).app N.obj)).inv_hom_id).trans
          (Category.comp_id s)))))

@[simp]
lemma Fiber.pullbackId_hom_app (U : C) (M : Fiber J F U) :
    (Fiber.pullbackId J F U).hom.app M =
      (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M.obj) := (rfl)

@[simp]
lemma Fiber.pullbackId_inv_app (U : C) (M : Fiber J F U) :
    (Fiber.pullbackId J F U).inv.app M =
      (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app M.obj) := (rfl)

variable (J F) in
/-- The composition isomorphisms of the pullback functors of the Hom-sheafification, given by the
composition isomorphisms of `F`. -/
def Fiber.pullbackComp {W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U) (h : g ≫ f = gf) :
    Fiber.pullback J F gf ≅ Fiber.pullback J F f ⋙ Fiber.pullback J F g :=
  NatIso.ofComponents (fun M ↦ (toFiber J F W).mapIso
      ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl))).app M.obj)) fun {M N} s ↦ by
    -- The pullback of `s` along `gf` is the pullback along `g` of its pullback along `f`,
    -- conjugated by the composition isomorphisms of `F`.
    have ht : (sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
        (Over.homMk g h : Over.mk gf ⟶ Over.mk f).op
          ((sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
            (Over.mkIdTerminal.from (Over.mk f)).op (Fiber.homEquiv M N s)) =
        (sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
          (Over.mkIdTerminal.from (Over.mk gf)).op (Fiber.homEquiv M N s) := by
      exact (ConcreteCategory.congr_hom ((sheafify (J.over U) (F.presheafHom M.obj N.obj)).map_comp
        (Over.mkIdTerminal.from (Over.mk f)).op (Over.homMk g h : Over.mk gf ⟶ Over.mk f).op)
          _).symm.trans (congrArg (fun k : Over.mk gf ⟶ Over.mk (𝟙 U) ↦
            (sheafify (J.over U) (F.presheafHom M.obj N.obj)).map k.op (Fiber.homEquiv M N s))
              (Over.mkIdTerminal.hom_ext _ _))
    have hK := toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp M.obj N.obj
      (Over.homMk g h : Over.mk gf ⟶ Over.mk f)
        ((sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
          (Over.mkIdTerminal.from (Over.mk f)).op (Fiber.homEquiv M N s))
    rw [ht, ← Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv,
      ← Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv] at hK
    exact (congrArg (· ≫ _) hK.symm).trans ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((toFiber J F W).mapIso
        ((Cat.Hom.toNatIso (F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
          (by rw [← h]; rfl))).app N.obj)).inv_hom_id).trans (Category.comp_id _)))))

@[simp]
lemma Fiber.pullbackComp_hom_app {W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U) (h : g ≫ f = gf)
    (M : Fiber J F U) :
    (Fiber.pullbackComp J F f g gf h).hom.app M =
      (toFiber J F W).map ((F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M.obj) := (rfl)

@[simp]
lemma Fiber.pullbackComp_inv_app {W : C} (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U) (h : g ≫ f = gf)
    (M : Fiber J F U) :
    (Fiber.pullbackComp J F f g gf h).inv.app M =
      (toFiber J F W).map ((F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).inv.toNatTrans.app M.obj) := (rfl)

end pullback

section pseudofunctor

variable [∀ U : C, HasSheafify (J.over U) (Type v')]
  [∀ U : C, (J.over U).WEqualsLocallyBijective (Type v')] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The Hom-sheafification of a pseudofunctor `F` for a Grothendieck topology `J`: its fibre over
`U` is `Fiber J F U`, whose morphisms are the sections over the terminal object of the
sheafifications of the presheaves of morphisms of `F`, and its pullback functors, unit and
composition isomorphisms are those of `F` (`Fiber.pullback`, `Fiber.pullbackId`,
`Fiber.pullbackComp`). It is a prestack (`isPrestack_prestackification`), and its presheaves of
morphisms are the sheafifications of those of `F` (`prestackificationPresheafHomIso`). -/
-- The body is exposed so that the fibres and pullback functors are definitionally `Fiber J F U`
-- and `Fiber.pullback`, as needed to state the component formulas below.
@[expose] def prestackification : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'} :=
  LocallyDiscrete.mkCatPseudofunctor (obj := fun U ↦ Cat.of (Fiber J F U.unop))
    (fun f ↦ Fiber.pullback J F f.unop) (fun U ↦ Fiber.pullbackId J F U.unop)
    (fun f g fg h ↦ Fiber.pullbackComp J F f.unop g.unop fg.unop (by rw [← h]; rfl))
    -- The coherence conditions are the images under `toFiber` of those of `F`, through
    -- `Fiber.pullbackHom_toFiber_map`.
    (fun f g h fg gh fgh hfg hgh hfgh hfgh' x ↦ by
      rw [Fiber.pullbackComp_hom_app, Fiber.pullbackComp_hom_app, Fiber.pullbackComp_hom_app,
        Fiber.pullbackComp_hom_app]
      exact ((congrArg (_ ≫ ·) (Fiber.pullbackHom_toFiber_map h.unop _)).trans
        ((toFiber J F _).map_comp _ _).symm).trans
          ((congrArg (toFiber J F _).map (mapComp'_hom_app_comp_map_mapComp'_hom_app F
            f.unop.op.toLoc g.unop.op.toLoc h.unop.op.toLoc fg.unop.op.toLoc gh.unop.op.toLoc
              fgh.unop.op.toLoc (by rw [← hfg]; rfl) (by rw [← hgh]; rfl) (by rw [← hfgh]; rfl)
                (by rw [← hfgh']; rfl) x.obj)).trans ((toFiber J F _).map_comp _ _)))
    (fun f hf x ↦ by
      rw [Fiber.pullbackComp_hom_app, Fiber.pullbackId_hom_app]
      exact ((congrArg (_ ≫ ·) (Fiber.pullbackHom_toFiber_map f.unop _)).trans
        ((toFiber J F _).map_comp _ _).symm).trans
          ((congrArg (toFiber J F _).map (mapComp'_hom_app_comp_map_mapId'_hom_app F
            (𝟙 _) rfl f.unop.op.toLoc (by simp) x.obj)).trans
              ((toFiber J F _).map_id _)))
    (fun f hf x ↦ by
      rw [Fiber.pullbackComp_hom_app, Fiber.pullbackId_hom_app]
      exact ((toFiber J F _).map_comp _ _).symm.trans
          ((congrArg (toFiber J F _).map (mapComp'_hom_app_comp_mapId'_hom_app F
            (𝟙 _) rfl f.unop.op.toLoc (by simp) x.obj)).trans
              ((toFiber J F _).map_id _)))

/-- The fibre of the Hom-sheafification over `U` is `Fiber J F U.as.unop`. -/
@[simp]
lemma prestackification_obj (U : LocallyDiscrete Cᵒᵖ) :
    (prestackification J F).obj U = Cat.of (Fiber J F U.as.unop) := (rfl)

/-- The pullback functors of the Hom-sheafification are the functors `Fiber.pullback`. -/
@[simp]
lemma prestackification_map_toFunctor {U V : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V) :
    ((prestackification J F).map f).toFunctor = Fiber.pullback J F f.as.unop := (rfl)

/-- The unit isomorphisms of the Hom-sheafification are the images of those of `F`. -/
@[simp]
lemma prestackification_mapId_hom_toNatTrans_app (U : LocallyDiscrete Cᵒᵖ)
    (M : Fiber J F U.as.unop) :
    ((prestackification J F).mapId U).hom.toNatTrans.app M =
      (toFiber J F U.as.unop).map
        ((F.mapId' (𝟙 U.as.unop).op.toLoc (by simp)).hom.toNatTrans.app M.obj) := (rfl)

/-- The inverse unit isomorphisms of the Hom-sheafification are the images of those of `F`. -/
@[simp]
lemma prestackification_mapId_inv_toNatTrans_app (U : LocallyDiscrete Cᵒᵖ)
    (M : Fiber J F U.as.unop) :
    ((prestackification J F).mapId U).inv.toNatTrans.app M =
      (toFiber J F U.as.unop).map
        ((F.mapId' (𝟙 U.as.unop).op.toLoc (by simp)).inv.toNatTrans.app M.obj) := (rfl)

/-- The comparison isomorphisms `mapComp'` of the Hom-sheafification are the images of those of
`F`. -/
@[simp]
lemma prestackification_mapComp'_hom_toNatTrans_app {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (g : V ⟶ W) (fg : U ⟶ W) (h : f ≫ g = fg) (M : Fiber J F U.as.unop) :
    ((prestackification J F).mapComp' f g fg h).hom.toNatTrans.app M =
      (toFiber J F W.as.unop).map ((F.mapComp' f g fg h).hom.toNatTrans.app M.obj) := by
  subst h
  rw [mapComp'_eq_mapComp]
  -- The morphisms `f.as.unop.op.toLoc` and `f` agree by definition.
  exact Fiber.pullbackComp_hom_app _ _ _ rfl M

/-- The inverse comparison isomorphisms `mapComp'` of the Hom-sheafification are the images of
those of `F`. -/
@[simp]
lemma prestackification_mapComp'_inv_toNatTrans_app {U V W : LocallyDiscrete Cᵒᵖ} (f : U ⟶ V)
    (g : V ⟶ W) (fg : U ⟶ W) (h : f ≫ g = fg) (M : Fiber J F U.as.unop) :
    ((prestackification J F).mapComp' f g fg h).inv.toNatTrans.app M =
      (toFiber J F W.as.unop).map ((F.mapComp' f g fg h).inv.toNatTrans.app M.obj) := by
  subst h
  rw [mapComp'_eq_mapComp]
  -- The morphisms `f.as.unop.op.toLoc` and `f` agree by definition.
  exact Fiber.pullbackComp_inv_app _ _ _ rfl M

/-- The pullback `pullHom` in the Hom-sheafification of a morphism `ψ : t^* M ⟶ s^* N` along `g`
is its pullback along `g`, composed with the images of the comparison isomorphisms of `F`. -/
lemma prestackification_pullHom {U U' T V : C} {M : F.obj (.mk (op U))}
    {N : F.obj (.mk (op U'))} {t : T ⟶ U} {s : T ⟶ U'}
    (ψ : Fiber.mk (J := J) ((F.map t.op.toLoc).toFunctor.obj M) ⟶
      Fiber.mk ((F.map s.op.toLoc).toFunctor.obj N))
    (g : V ⟶ T) (gt : V ⟶ U) (gs : V ⟶ U') (hgt : g ≫ t = gt) (hgs : g ≫ s = gs) :
    pullHom (F := prestackification J F) (M₁ := Fiber.mk (J := J) M) (M₂ := Fiber.mk (J := J) N)
      (f₁ := t)
      (f₂ := s) ψ g gt gs hgt hgs =
      (toFiber J F V).map ((F.mapComp' t.op.toLoc g.op.toLoc gt.op.toLoc
          (by rw [← hgt]; rfl)).hom.toNatTrans.app M) ≫ Fiber.pullbackHom g ψ ≫
        (toFiber J F V).map ((F.mapComp' s.op.toLoc g.op.toLoc gs.op.toLoc
          (by rw [← hgs]; rfl)).inv.toNatTrans.app N) := by
  simp only [pullHom]
  -- The objects `Fiber.mk M` of the Hom-sheafification are those of `F` only up to unfolding.
  erw [prestackification_mapComp'_hom_toNatTrans_app, prestackification_mapComp'_inv_toNatTrans_app]
  rfl

/-- The comparison functors `toFiber` commute with the pullback functors, through identity
isomorphisms. -/
def toFiberNatIso {U V : C} (f : V ⟶ U) :
    (F.map f.op.toLoc).toFunctor ⋙ toFiber J F V ≅ toFiber J F U ⋙ Fiber.pullback J F f :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun φ ↦
    (Category.comp_id _).trans ((Fiber.pullbackHom_toFiber_map f φ).symm.trans
      (Category.id_comp _).symm)

@[simp]
lemma toFiberNatIso_hom_app {U V : C} (f : V ⟶ U) (M : F.obj (.mk (op U))) :
    (toFiberNatIso J F f).hom.app M = 𝟙 _ := (rfl)

@[simp]
lemma toFiberNatIso_inv_app {U V : C} (f : V ⟶ U) (M : F.obj (.mk (op U))) :
    (toFiberNatIso J F f).inv.app M = 𝟙 _ := (rfl)

/-- The strong transformation from `F` to its Hom-sheafification, with components the comparison
functors `toFiber` and identity naturality isomorphisms. -/
-- The body is exposed so that the components are definitionally `toFiber` and the naturality
-- isomorphisms `toFiberNatIso`.
@[expose] def toPrestackification : StrongTrans F (prestackification J F) where
  app a := (toFiber J F a.as.unop).toCatHom
  naturality f := Cat.Hom.isoMk (toFiberNatIso J F f.as.unop)
  naturality_naturality η :=
    Pseudofunctor.naturality_naturality_of_locallyDiscrete F (prestackification J F)
      (fun a ↦ (toFiber J F a.as.unop).toCatHom)
      (fun f ↦ Cat.Hom.isoMk (toFiberNatIso J F f.as.unop)) η
  naturality_id a :=
    Cat.comp_whiskerLeft_eq_whiskerRight_comp_leftUnitor_hom_comp_rightUnitor_inv _ _ _
      fun M ↦ by
        -- The naturality isomorphism is the identity, and the unit isomorphism of the
        -- Hom-sheafification is the image of that of `F`.
        rw [show F.mapId a = F.mapId' (𝟙 a.as.unop).op.toLoc (by simp) from
          (F.mapId'_eq_mapId a).symm]
        exact Category.id_comp _
  naturality_comp f g :=
    Cat.comp_whiskerLeft_eq_whiskerRight_comp_associators _ _ _ _ _ fun M ↦ by
      have h := prestackification_mapComp'_hom_toNatTrans_app J F f g (f ≫ g) rfl
        ((toFiber J F _).obj M)
      rw [mapComp'_eq_mapComp, mapComp'_eq_mapComp] at h
      -- The naturality isomorphisms are identities, and the composition isomorphisms of the
      -- Hom-sheafification are the images of those of `F` (`h`); the identities are only
      -- definitionally the components of `Cat.Hom.isoMk`, so the steps are chained by `exact`.
      exact (Category.id_comp _).trans (h.trans ((Category.comp_id _).symm.trans
        (congrArg (_ ≫ ·) ((Category.id_comp _).trans
          (((prestackification J F).map g).toFunctor.map_id _)).symm)))

/-- The component of `toPrestackification` at `U` is the comparison functor `toFiber`. -/
@[simp]
lemma toPrestackification_app_toFunctor (a : LocallyDiscrete Cᵒᵖ) :
    ((toPrestackification J F).app a).toFunctor = toFiber J F a.as.unop := (rfl)

/-- The naturality isomorphisms of `toPrestackification` are identities. -/
@[simp]
lemma toPrestackification_naturality_hom_toNatTrans_app {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : F.obj a) : ((toPrestackification J F).naturality f).hom.toNatTrans.app M = 𝟙 _ := (rfl)

/-- The inverse naturality isomorphisms of `toPrestackification` are identities. -/
@[simp]
lemma toPrestackification_naturality_inv_toNatTrans_app {a b : LocallyDiscrete Cᵒᵖ} (f : a ⟶ b)
    (M : F.obj a) : ((toPrestackification J F).naturality f).inv.toNatTrans.app M = 𝟙 _ := (rfl)

/-- The presheaves of morphisms of the Hom-sheafification of `F` are the sheafifications of the
presheaves of morphisms of `F`. -/
def prestackificationPresheafHomIso {U : C} (M N : F.obj (.mk (op U))) :
    sheafify (J.over U) (F.presheafHom M N) ≅
      (prestackification J F).presheafHom (S := U) (Fiber.mk (J := J) M) (Fiber.mk (J := J) N) :=
  NatIso.ofComponents (fun T ↦ (sheafifyPresheafHomEquiv J M N T.unop).toIso) fun {T T'} p ↦ by
    refine ConcreteCategory.hom_ext _ _ fun t ↦
      (toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp M N p.unop t).symm.trans ?_
    exact (prestackification_pullHom J F _ _ _ _ (Over.w p.unop) (Over.w p.unop)).symm

/-- The components of `prestackificationPresheafHomIso` are the bijections
`sheafifyPresheafHomEquiv`. -/
@[simp]
lemma prestackificationPresheafHomIso_hom_app_apply {U : C} (M N : F.obj (.mk (op U)))
    (T : (Over U)ᵒᵖ) (t : (sheafify (J.over U) (F.presheafHom M N)).obj T) :
    (prestackificationPresheafHomIso J F M N).hom.app T t =
      sheafifyPresheafHomEquiv J M N T.unop t := (rfl)

/-- The components of the inverse of `prestackificationPresheafHomIso` are the inverses of the
bijections `sheafifyPresheafHomEquiv`. -/
@[simp]
lemma prestackificationPresheafHomIso_inv_app_apply {U : C} (M N : F.obj (.mk (op U)))
    (T : (Over U)ᵒᵖ)
    (φ : ((prestackification J F).presheafHom (S := U) (Fiber.mk (J := J) M)
      (Fiber.mk (J := J) N)).obj T) :
    (prestackificationPresheafHomIso J F M N).inv.app T φ =
      (sheafifyPresheafHomEquiv J M N T.unop).symm φ := (rfl)

/-- The Hom-sheafification of `F` is a prestack for `J`: its presheaves of morphisms are
sheafifications (`prestackificationPresheafHomIso`). -/
instance isPrestack_prestackification : (prestackification J F).IsPrestack J where
  isSheaf {U} M N := (Presheaf.isSheaf_of_iso_iff
    (prestackificationPresheafHomIso J F (Fiber.obj (J := J) M) (Fiber.obj (J := J) N))).1
      ((presheafToSheaf (J.over U) (Type v')).obj _).property

instance isEquivalence_toPrestackification_app [F.IsPrestack J] (a : LocallyDiscrete Cᵒᵖ) :
    ((toPrestackification J F).app a).toFunctor.IsEquivalence := by
  rw [toPrestackification_app_toFunctor, ← toFiberEquivalence_functor]
  exact (toFiberEquivalence J F a.as.unop).isEquivalence_functor

open scoped Pseudofunctor.StrongTrans in
/-- For a prestack `F`, the strong transformation from `F` to its Hom-sheafification is an
equivalence of pseudofunctors, with components the equivalences `toFiberEquivalence`. -/
def toPrestackificationEquivalence [F.IsPrestack J] :
    Bicategory.Equivalence F (prestackification J F) :=
  (toPrestackification J F).equivalenceOfIsEquivalence

open scoped Pseudofunctor.StrongTrans in
@[simp]
lemma toPrestackificationEquivalence_hom [F.IsPrestack J] :
    (toPrestackificationEquivalence J F).hom = toPrestackification J F := (rfl)

end pseudofunctor

end TauCeti.Stack.Prestackification
