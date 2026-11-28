/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import Mathlib.CategoryTheory.Sites.Over
public import TauCeti.CategoryTheory.Comma.Over
public import TauCeti.CategoryTheory.Sites.CoverLifting

/-!
# Sections of sheafifications on slice sites

Let `J` be a Grothendieck topology on `C` and `U` an object of `C`. This file studies the
sections of the sheafification, for the slice topology `J.over U`, of a presheaf of types `P` on
`Over U`.

The sections over the terminal object `Over.mk (𝟙 U)` form a functor `J.sheafifySections U`,
which preserves finite products and so is monoidal, and the unit of sheafification gives a
monoidal natural transformation `J.toSheafifySections U` from evaluation at the terminal object.

The sections over any `T : Over U` are the sections over the terminal object of the
sheafification of the restriction of `P` to `Over T.left`, along `Over.map T.hom`
(`J.restrictSectionsOver T`). This restricts along the isomorphism
`(Over.map T.hom).obj (Over.mk (𝟙 T.left)) ≅ T` and then identifies the restriction of a
sheafification with the sheafification of the restriction
(`CategoryTheory.Functor.opCompSheafifyIso`). That identification needs that the morphisms
inverted by sheafification are the locally bijective ones, on the slice sites involved
(`CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective`), which holds automatically when the
presheaves take values in `Type (max u v)` for `C : Type u` with `Category.{v} C`. In particular
the sections over the terminal object of `Over U` restrict along any `f : V ⟶ U` to sections over
the terminal object of `Over V` (`J.restrictSections f`). These restrictions are compatible with
morphisms of `Over U` and with the identity of `U` (`restrictSectionsOver_comp`,
`restrictSectionsOver_mkId`).

## Main declarations

* `CategoryTheory.GrothendieckTopology.sheafifySections`: sheafification followed by sections over
  the terminal object, a monoidal functor, with the unit `toSheafifySections`.
* `CategoryTheory.GrothendieckTopology.restrictSectionsOver`: the sections over `T` as sections
  over the terminal object of the sheafification of the restriction to `Over T.left`, with the
  computation rules `restrictSectionsOver_app_apply` and `restrictSectionsOver_app_toSheafify`.
* `CategoryTheory.GrothendieckTopology.restrictSections`: the restriction along `f : V ⟶ U` of
  sections over the terminal object, a monoidal natural transformation, with
  `restrictSections_app_apply` and `restrictSections_app_toSheafifySections`.
-/

public section

noncomputable section

universe v' v u

open CategoryTheory Limits Opposite MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

section sheafifySections

variable (U : C) [HasSheafify (J.over U) (Type v')]

/-- The functor sending a presheaf of types on `Over U` to the sections of its sheafification
over the terminal object `Over.mk (𝟙 U)`. -/
-- The body is exposed so that its values are the sections of a sheafification.
@[expose] def sheafifySections : ((Over U)ᵒᵖ ⥤ Type v') ⥤ Type v' :=
  CategoryTheory.sheafification (J.over U) (Type v') ⋙ (evaluation _ _).obj (op (Over.mk (𝟙 U)))

instance preservesFiniteProducts_sheafifySections :
    PreservesFiniteProducts (J.sheafifySections U) := by
  dsimp [sheafifySections]
  infer_instance

/-- The monoidal structure of `J.sheafifySections U`, from its preservation of finite products. -/
instance monoidalSheafifySections : (J.sheafifySections U).Monoidal := .ofChosenFiniteProducts _

/-- The value at the terminal object of the unit of sheafification. -/
def toSheafifySections : (evaluation _ _).obj (op (Over.mk (𝟙 U))) ⟶ J.sheafifySections U :=
  Functor.whiskerRight (CategoryTheory.toSheafification (J.over U) (Type v'))
    ((evaluation _ _).obj (op (Over.mk (𝟙 U))))

@[simp]
lemma toSheafifySections_app (P : (Over U)ᵒᵖ ⥤ Type v') :
    (J.toSheafifySections U).app P =
      (CategoryTheory.toSheafify (J.over U) P).app (op (Over.mk (𝟙 U))) := (rfl)

variable {J U}

/-- The monoidal structure of `J.sheafifySections U` is compatible with the unit of
sheafification: the pair of images of `x` and `y` corresponds to the image of `(x, y)`. -/
lemma μ_toSheafifySections {P Q : (Over U)ᵒᵖ ⥤ Type v'} (x : P.obj (op (Over.mk (𝟙 U))))
    (y : Q.obj (op (Over.mk (𝟙 U)))) :
    μ (J.sheafifySections U) P Q ((J.toSheafifySections U).app P x,
      (J.toSheafifySections U).app Q y) =
      (J.toSheafifySections U).app (P ⊗ Q) ((x, y) : (P ⊗ Q).obj (op (Over.mk (𝟙 U)))) := by
  -- Evaluation at the terminal object preserves finite products, so `J.toSheafifySections U` is
  -- a monoidal natural transformation (`NatTrans.IsMonoidal.of_cartesianMonoidalCategory`), and
  -- the monoidal structure of evaluation is the identity on pairs, as its components are the
  -- projections (`Functor.Monoidal.μ_fst`, `Functor.Monoidal.μ_snd`).
  let _ : ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))).Monoidal := .ofChosenFiniteProducts _
  have hμ : μ ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))) P Q = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext _ _
      ((Functor.Monoidal.μ_fst _ P Q).trans (Category.id_comp _).symm)
      ((Functor.Monoidal.μ_snd _ P Q).trans (Category.id_comp _).symm)
  -- The source of the tensor square is the tensor product `P.obj _ ⊗ Q.obj _` in `Type v'`, which
  -- is the product type only after unfolding, so the pair is ascribed the product type for the
  -- anonymous constructor.
  have := ConcreteCategory.congr_hom
    (NatTrans.IsMonoidal.tensor (τ := J.toSheafifySections U) P Q)
    (show P.obj (op (Over.mk (𝟙 U))) × Q.obj (op (Over.mk (𝟙 U))) from (x, y))
  simp only [evaluation_obj_obj, Monoidal.tensorObj_obj, hμ, toSheafifySections_app,
    ConcreteCategory.comp_apply] at this
  exact this.symm

/-- The monoidal structure of `J.sheafifySections U` is compatible with the unit of
sheafification: the unit `ε` is the image of the point of the terminal presheaf. -/
lemma ε_toSheafifySections :
    ε (J.sheafifySections U) PUnit.unit =
      (J.toSheafifySections U).app (𝟙_ ((Over U)ᵒᵖ ⥤ Type v')) PUnit.unit := by
  -- Evaluation at the terminal object preserves finite products, so `J.toSheafifySections U` is
  -- a monoidal natural transformation (`NatTrans.IsMonoidal.of_cartesianMonoidalCategory`), and
  -- so it is compatible with the units.
  let _ : ((evaluation _ (Type v')).obj (op (Over.mk (𝟙 U)))).Monoidal := .ofChosenFiniteProducts _
  exact (ConcreteCategory.congr_hom (NatTrans.IsMonoidal.unit (τ := J.toSheafifySections U))
    PUnit.unit).symm

/-- The image under `J.sheafifySections U` of a morphism `toUnit P ≫ y` that factors through the
terminal presheaf is constant, with value the image of the global section given by `y`. -/
lemma sheafifySections_map_toUnit_comp {P Q : (Over U)ᵒᵖ ⥤ Type v'}
    (y : 𝟙_ ((Over U)ᵒᵖ ⥤ Type v') ⟶ Q) (a : (J.sheafifySections U).obj P) :
    (J.sheafifySections U).map (CartesianMonoidalCategory.toUnit P ≫ y) a =
      (J.toSheafifySections U).app Q (y.app (op (Over.mk (𝟙 U))) PUnit.unit) := by
  rw [Functor.map_comp, ConcreteCategory.comp_apply, ← Functor.Monoidal.toUnit_ε]
  refine (congrArg ((J.sheafifySections U).map y) ε_toSheafifySections).trans ?_
  exact (ConcreteCategory.congr_hom ((J.toSheafifySections U).naturality y) _).symm

end sheafifySections

/-- Sheafification on the slice site over `(Over.mk f).left`, which is the slice site over the
source `Y` of `f`. -/
instance hasSheafify_over_mk_left {X Y : C} (f : Y ⟶ X) [HasSheafify (J.over Y) (Type v')] :
    HasSheafify (J.over (Over.mk f).left) (Type v') :=
  inferInstanceAs (HasSheafify (J.over Y) (Type v'))

/-- On the slice site over `(Over.mk f).left`, which is the slice site over the source `Y` of `f`,
the morphisms inverted by sheafification are the locally bijective ones. -/
instance wEqualsLocallyBijective_over_mk_left {X Y : C} (f : Y ⟶ X)
    [(J.over Y).WEqualsLocallyBijective (Type v')] :
    (J.over (Over.mk f).left).WEqualsLocallyBijective (Type v') :=
  inferInstanceAs ((J.over Y).WEqualsLocallyBijective (Type v'))

section restrictSections

variable {U : C} [HasSheafify (J.over U) (Type v')] [(J.over U).WEqualsLocallyBijective (Type v')]

/-- The sections over `T : Over U` of the sheafification of a presheaf `P` on `Over U`, as
sections over the terminal object of the sheafification of the restriction of `P` to
`Over T.left`. This is the restriction of sheafifications along `Over.map T.hom`
(`Functor.opCompSheafifyIso`), evaluated at the terminal object. -/
def restrictSectionsOver (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] :
    CategoryTheory.sheafification (J.over U) (Type v') ⋙ (evaluation _ _).obj (op T) ⟶
      (Functor.whiskeringLeft _ _ (Type v')).obj (Over.map T.hom).op ⋙
        J.sheafifySections T.left where
  app P := (CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom T).op ≫
    ((Over.map T.hom).opCompSheafifyIso (J.over T.left) (J.over U) P).hom.app
      (op (Over.mk (𝟙 T.left)))
  naturality P Q φ := by
    have h := NatTrans.congr_app
      ((Over.map T.hom).whiskerLeft_sheafifyMap_comp_opCompSheafifyIso_hom (J.over T.left)
        (J.over U) φ) (op (Over.mk (𝟙 T.left)))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h
    -- Both sides are the naturality square of `sheafifyMap φ` along `Over.mapObjMkIdHom T`
    -- followed by `h`. The goal writes `sheafifyMap φ` through `presheafToSheaf` and
    -- `sheafToPresheaf`, of which the abbreviation `sheafifyMap` is the composite, so the steps
    -- are combined by `exact`.
    exact ((CategoryTheory.sheafifyMap (J.over U) φ).naturality_assoc
      (Over.mapObjMkIdHom T).op _).symm.trans
        ((congrArg ((CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom T).op ≫ ·)
          h).trans (Category.assoc _ _ _).symm)

variable {J} in
/-- The computation rule for `restrictSectionsOver`: a section over `T` is restricted along
`Over.mapObjMkIdHom T`, and then the restriction of the sheafification is identified with the
sheafification of the restriction. -/
lemma restrictSectionsOver_app_apply (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] (P : (Over U)ᵒᵖ ⥤ Type v')
    (t : (CategoryTheory.sheafify (J.over U) P).obj (op T)) :
    (J.restrictSectionsOver T).app P t =
      ((Over.map T.hom).opCompSheafifyIso (J.over T.left) (J.over U) P).hom.app
        (op (Over.mk (𝟙 T.left)))
          ((CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom T).op t) :=
  (rfl)

variable {J} in
/-- `restrictSectionsOver` sends the image of a section of `P` over `T` to the image of its
restriction. -/
lemma restrictSectionsOver_app_toSheafify (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] (P : (Over U)ᵒᵖ ⥤ Type v')
    (x : P.obj (op T)) :
    (J.restrictSectionsOver T).app P ((CategoryTheory.toSheafify (J.over U) P).app (op T) x) =
      (J.toSheafifySections T.left).app ((Over.map T.hom).op ⋙ P)
        (P.map (Over.mapObjMkIdHom T).op x) := by
  have h := ConcreteCategory.congr_hom
    ((CategoryTheory.toSheafify (J.over U) P).naturality (Over.mapObjMkIdHom T).op) x
  simp only [ConcreteCategory.comp_apply] at h
  rw [restrictSectionsOver_app_apply, toSheafifySections_app, ← h]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    ((Over.map T.hom).whiskerLeft_toSheafify_comp_opCompSheafifyIso_hom (J.over T.left) (J.over U)
      P) (op (Over.mk (𝟙 T.left)))) _

/-- The component of `restrictSectionsOver` at `P` as an isomorphism: it restricts along the
isomorphism `Over.mapMkIso (𝟙 T.left) _` from `(Over.map T.hom).obj (Over.mk (𝟙 T.left))` to
`T`, and then applies the comparison isomorphism of sheafifications. -/
def restrictSectionsOverIso (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] (P : (Over U)ᵒᵖ ⥤ Type v') :
    (CategoryTheory.sheafify (J.over U) P).obj (op T) ≅
      (J.sheafifySections T.left).obj ((Over.map T.hom).op ⋙ P) :=
  (CategoryTheory.sheafify (J.over U) P).mapIso
      (Over.mapMkIso (𝟙 T.left) (Category.id_comp T.hom)).op ≪≫
    ((Over.map T.hom).opCompSheafifyIso (J.over T.left) (J.over U) P).app
      (op (Over.mk (𝟙 T.left)))

/-- The components of `restrictSectionsOver` are the isomorphisms `restrictSectionsOverIso`. -/
lemma restrictSectionsOver_app (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] (P : (Over U)ᵒᵖ ⥤ Type v') :
    (J.restrictSectionsOver T).app P = (J.restrictSectionsOverIso T P).hom := (rfl)

lemma restrictSectionsOver_app_bijective (T : Over U) [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] (P : (Over U)ᵒᵖ ⥤ Type v') :
    Function.Bijective ((J.restrictSectionsOver T).app P) := by
  rw [restrictSectionsOver_app]
  exact (J.restrictSectionsOverIso T P).toEquiv.bijective

variable {V : C} [HasSheafify (J.over V) (Type v')] [(J.over V).WEqualsLocallyBijective (Type v')]
  (f : V ⟶ U)

/-- Restricting the sections over the terminal object of the sheafification of a presheaf on
`Over U` along `f : V ⟶ U`: the sections over `Over.mk (𝟙 V)` of the sheafification of the
restriction of the presheaf to `Over V`. -/
def restrictSections :
    J.sheafifySections U ⟶
      (Functor.whiskeringLeft _ _ (Type v')).obj (Over.map f).op ⋙ J.sheafifySections V :=
  Functor.whiskerLeft (CategoryTheory.sheafification (J.over U) (Type v'))
      ((evaluation _ _).map (Over.mkIdTerminal.from (Over.mk f)).op) ≫
    J.restrictSectionsOver (Over.mk f)

lemma restrictSections_app {P : (Over U)ᵒᵖ ⥤ Type v'} (s : (J.sheafifySections U).obj P) :
    (J.restrictSections f).app P s = (J.restrictSectionsOver (Over.mk f)).app P
      ((CategoryTheory.sheafify (J.over U) P).map (Over.mkIdTerminal.from (Over.mk f)).op s) :=
  (rfl)

/-- The computation rule for `restrictSections`: a section over the terminal object is restricted
to `(Over.map f).obj (Over.mk (𝟙 V))`, and then the restriction of the sheafification is
identified with the sheafification of the restriction. -/
lemma restrictSections_app_apply {P : (Over U)ᵒᵖ ⥤ Type v'} (s : (J.sheafifySections U).obj P) :
    (J.restrictSections f).app P s =
      ((Over.map f).opCompSheafifyIso (J.over V) (J.over U) P).hom.app (op (Over.mk (𝟙 V)))
        ((CategoryTheory.sheafify (J.over U) P).map
          (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op s) := by
  have h (s : (CategoryTheory.sheafify (J.over U) P).obj (op (Over.mk (𝟙 U)))) :
      (CategoryTheory.sheafify (J.over U) P).map
        (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op s =
      (CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom (Over.mk f)).op
        ((CategoryTheory.sheafify (J.over U) P).map (Over.mkIdTerminal.from (Over.mk f)).op s) := by
    rw [Over.mkIdTerminal.hom_ext (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V))))
      (Over.mapObjMkIdHom (Over.mk f) ≫ Over.mkIdTerminal.from (Over.mk f)), op_comp,
      Functor.map_comp, ConcreteCategory.comp_apply]
  rw [restrictSections_app, restrictSectionsOver_app_apply]
  -- The two sides differ in writing the slice site and the restriction functor through
  -- `(Over.mk f).left = V` and `(Over.mk f).hom = f`, so `h` is applied by `exact`.
  exact congrArg _ (h s).symm

/-- `restrictSections` sends the image of a section of `P` over the terminal object to the image
of its restriction. -/
lemma restrictSections_app_toSheafifySections (P : (Over U)ᵒᵖ ⥤ Type v')
    (x : P.obj (op (Over.mk (𝟙 U)))) :
    (J.restrictSections f).app P ((J.toSheafifySections U).app P x) =
      (J.toSheafifySections V).app ((Over.map f).op ⋙ P)
        (P.map (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op x) := by
  have h := ConcreteCategory.congr_hom ((CategoryTheory.toSheafify (J.over U) P).naturality
    (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op) x
  simp only [ConcreteCategory.comp_apply] at h
  rw [restrictSections_app_apply, toSheafifySections_app, toSheafifySections_app]
  -- The sections of `J.sheafifySections U` are those of the sheafification only after unfolding,
  -- so `h` is applied by `exact`.
  exact (congrArg (((Over.map f).opCompSheafifyIso (J.over V) (J.over U) P).hom.app
    (op (Over.mk (𝟙 V))) ·) h.symm).trans (ConcreteCategory.congr_hom (NatTrans.congr_app
      ((Over.map f).whiskerLeft_toSheafify_comp_opCompSheafifyIso_hom (J.over V) (J.over U) P)
        (op (Over.mk (𝟙 V)))) _)

/-- Restricting sections over `T` to the terminal object and then along `p.left` is restricting
them along `p : T' ⟶ T` and then to the terminal object, up to the identification
`Over.mapCompOfHom p` of the restrictions of `P`. -/
lemma restrictSectionsOver_comp {T T' : Over U} [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] [HasSheafify (J.over T'.left) (Type v')]
    [(J.over T'.left).WEqualsLocallyBijective (Type v')] (p : T' ⟶ T) (P : (Over U)ᵒᵖ ⥤ Type v')
    (t : (CategoryTheory.sheafify (J.over U) P).obj (op T)) :
    (J.sheafifySections T'.left).map
        (Functor.whiskerRight (NatTrans.op (Over.mapCompOfHom p).hom) P)
        ((J.restrictSections p.left).app _ ((J.restrictSectionsOver T).app P t)) =
      (J.restrictSectionsOver T').app P ((CategoryTheory.sheafify (J.over U) P).map p.op t) := by
  -- `Over.mapCompOfHom p` ends at the composite functor, whose continuity `hC` needs.
  have : (Over.map p.left ⋙ Over.map T.hom).IsContinuous (J.over T'.left) (J.over U) :=
    Functor.isContinuous_comp _ _ _ (J.over T.left) _
  have : (Over.map p.left ⋙ Over.map T.hom).IsCocontinuous (J.over T'.left) (J.over U) :=
    CategoryTheory.isCocontinuous_comp _ _ (J.over T'.left) (J.over T.left)
  let g := Over.mkIdTerminal.from ((Over.map p.left).obj (Over.mk (𝟙 T'.left)))
  -- The comparison for `Over.map T.hom` is natural along `g`.
  have h₁ := ConcreteCategory.congr_hom
    (((Over.map T.hom).opCompSheafifyIso (J.over T.left) (J.over U) P).hom.naturality g.op)
    ((CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom T).op t)
  -- The comparisons for `Over.map T.hom` and `Over.map p.left` compose to that for the composite.
  have hB := NatTrans.congr_app
    ((Over.map T.hom).whiskerLeft_opCompSheafifyIso_hom_comp_opCompSheafifyIso_hom (J.over T.left)
      (J.over U) (Over.map p.left) (J.over T'.left) P) (op (Over.mk (𝟙 T'.left)))
  -- The comparison for the composite is that for `Over.map T'.hom`, along `Over.mapCompOfHom p`.
  have hC := NatTrans.congr_app
    ((Over.map T'.hom).whiskerRight_op_comp_opCompSheafifyIso_hom (J.over T'.left) (J.over U)
      (Over.mapCompOfHom p).hom P) (op (Over.mk (𝟙 T'.left)))
  have hk : ((Over.mapCompOfHom p).hom.app (Over.mk (𝟙 T'.left)) ≫ (Over.map T.hom).map g) ≫
      Over.mapObjMkIdHom T = Over.mapObjMkIdHom T' ≫ p := by
    ext
    simp [g]
  have h₂ := congrArg (fun q ↦ (CategoryTheory.sheafify (J.over U) P).map q.op t) hk
  simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] at h₂
  -- Unfolding the restrictions (`restrictSections_app_apply`, `restrictSectionsOver_app_apply`),
  -- the claim follows from `h₁`, `hB`, `hC` and `h₂`. The intermediate sections are typed by
  -- presheaves on slices written through composite and restricted functors, which agree only up
  -- to unfolding, so the steps are chained by `exact`.
  refine (congrArg ((J.sheafifySections T'.left).map
    (Functor.whiskerRight (NatTrans.op (Over.mapCompOfHom p).hom) P))
      (restrictSections_app_apply J p.left _)).trans ?_
  refine (congrArg (fun z ↦ (CategoryTheory.sheafifyMap (J.over T'.left)
    (Functor.whiskerRight (NatTrans.op (Over.mapCompOfHom p).hom) P)).app _
      (((Over.map p.left).opCompSheafifyIso (J.over T'.left) (J.over T.left)
        ((Over.map T.hom).op ⋙ P)).hom.app _ z)) h₁.symm).trans ?_
  refine (congrArg ((CategoryTheory.sheafifyMap (J.over T'.left)
    (Functor.whiskerRight (NatTrans.op (Over.mapCompOfHom p).hom) P)).app _)
      (ConcreteCategory.congr_hom hB _)).trans ?_
  refine (ConcreteCategory.congr_hom hC _).symm.trans ?_
  exact congrArg (((Over.map T'.hom).opCompSheafifyIso (J.over T'.left) (J.over U) P).hom.app _) h₂

/-- Restricting sections over the terminal object of `Over U` to the terminal object gives them
back, up to the identification `Over.mapId U` of `Over.map (𝟙 U)` with the identity. -/
lemma restrictSectionsOver_mkId (P : (Over U)ᵒᵖ ⥤ Type v')
    (s : (J.sheafifySections U).obj P) :
    (J.sheafifySections U).map (Functor.whiskerRight (NatTrans.op (Over.mapId U).inv) P)
        ((J.restrictSectionsOver (Over.mk (𝟙 U))).app P s) = s := by
  -- Restricting along `Over.map (𝟙 U)` is restricting along `𝟭 (Over U)` followed by the
  -- identification `Over.mapId U`, and the comparison for `𝟭 (Over U)` is the identity.
  have h := (𝟭 (Over U)).whiskerRight_op_comp_opCompSheafifyIso_hom (J.over U) (J.over U)
    (Over.mapId U).inv P
  rw [Functor.opCompSheafifyIso_id_hom, Category.comp_id] at h
  have h' := ConcreteCategory.congr_hom (NatTrans.congr_app h (op (Over.mk (𝟙 U))))
    ((CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom (Over.mk (𝟙 U))).op s)
  simp only [Functor.whiskerRight_app, NatTrans.op_app, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h'
  have hs (y : (CategoryTheory.sheafify (J.over U) P).obj (op (Over.mk (𝟙 U)))) :
      (CategoryTheory.sheafify (J.over U) P).map ((Over.mapId U).inv.app (Over.mk (𝟙 U))).op
        ((CategoryTheory.sheafify (J.over U) P).map (Over.mapObjMkIdHom (Over.mk (𝟙 U))).op y) =
          y := by
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      Over.mkIdTerminal.hom_ext (_ ≫ _) (𝟙 _)]
    simp
  -- The goal is `h'` read backwards followed by `hs`, up to `restrictSectionsOver_app_apply`,
  -- writing the slice site and the restriction functor through `(Over.mk (𝟙 U)).left = U` and
  -- `(Over.mk (𝟙 U)).hom = 𝟙 U`, and the sections of `J.sheafifySections U` as those of the
  -- sheafification; these agree only up to unfolding, so the steps are combined by `exact`.
  exact h'.symm.trans (hs s)

end restrictSections

end CategoryTheory.GrothendieckTopology
