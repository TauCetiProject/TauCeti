/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Cat
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
the terminal object of `Over V` (`CategoryTheory.GrothendieckTopology.restrictSections`, which
needs that the morphisms inverted by sheafification are the locally bijective ones, on the slice
sites involved: the pullback constructions assume this only on those slices, and the
pseudofunctor on every slice site), and
identifies the restricted presheaf of morphisms with that of the pullbacks (Mathlib's
`Pseudofunctor.overMapCompPresheafHomIso`). This pullback is functorial
(`Fiber.pullbackHom_comp`) because the restriction of sections is a natural transformation between
functors preserving finite products, hence monoidal. More generally, the sections over any
`T : Over U` of the sheafified presheaf of morphisms are the morphisms between the pullbacks to
`T.left` (`sheafifyPresheafHomEquiv`, through
`CategoryTheory.GrothendieckTopology.restrictSectionsOver`), compatibly with pullbacks and with
the comparison isomorphisms of `F` (`toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp`,
`sheafifyPresheafHomEquiv_mkId`). This gives the naturality of the unit and composition
isomorphisms, which are the images under `toFiber` of those of `F`, and the isomorphism of
presheaves of morphisms; the coherence conditions are the images of those of `F`.

The comparison functors `toFiber` form a strong transformation `toPrestackification` from `F`,
whose naturality isomorphisms are identities. For a prestack `F` it is an equivalence of
pseudofunctors (`toPrestackificationEquivalence`). The Hom-sheafification takes values in the
universes of `F`, so no universe lift is needed. The hypotheses `HasSheafify` and
`WEqualsLocallyBijective` on the slice sites hold automatically when the morphisms of `F` lie in
`Type (max u v)` for `C : Type u` with `Category.{v} C`.

## Main declarations

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

section pullback

variable {J} {F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'}} {U V : C} [HasSheafify (J.over U) (Type v')]
  [(J.over U).WEqualsLocallyBijective (Type v')] [HasSheafify (J.over V) (Type v')]
  [(J.over V).WEqualsLocallyBijective (Type v')]

/-- The pullback along `f : V ⟶ U` of a morphism of the fibre over `U` of the Hom-sheafification
of `F`: the restriction of the corresponding section of the sheafified presheaf of morphisms
(`restrictSections`), transported along Mathlib's identification
`Pseudofunctor.overMapCompPresheafHomIso` of the restricted presheaf of morphisms with the
presheaf of morphisms between the pullbacks. -/
def Fiber.pullbackHom (f : V ⟶ U) {M N : Fiber J F U} (s : M ⟶ N) :
    Fiber.mk (J := J) ((F.map f.op.toLoc).toFunctor.obj M.obj) ⟶
      Fiber.mk ((F.map f.op.toLoc).toFunctor.obj N.obj) :=
  (Fiber.homEquiv _ _).symm ((J.sheafifySections V).map
    (F.overMapCompPresheafHomIso M.obj N.obj f).hom
      ((J.restrictSections f).app _ (Fiber.homEquiv M N s)))

@[simp]
lemma Fiber.homEquiv_pullbackHom (f : V ⟶ U) {M N : Fiber J F U} (s : M ⟶ N) :
    Fiber.homEquiv _ _ (Fiber.pullbackHom f s) = (J.sheafifySections V).map
      (F.overMapCompPresheafHomIso M.obj N.obj f).hom
        ((J.restrictSections f).app _ (Fiber.homEquiv M N s)) :=
  Equiv.apply_symm_apply _ _

/-- The pullback of the morphism given by a local morphism `x` is the morphism given by the
pullback of `x`. -/
@[simp]
lemma Fiber.pullbackHom_homMk (f : V ⟶ U) {M N : Fiber J F U}
    (x : (F.presheafHom M.obj N.obj).obj (op (Over.mk (𝟙 U)))) :
    Fiber.pullbackHom f (Fiber.homMk x) = Fiber.homMk
      ((F.overMapCompPresheafHomIso M.obj N.obj f).hom.app _
        ((F.presheafHom M.obj N.obj).map
          (Over.mkIdTerminal.from ((Over.map f).obj (Over.mk (𝟙 V)))).op x)) := by
  ext
  rw [Fiber.homEquiv_pullbackHom, Fiber.homEquiv_homMk,
    GrothendieckTopology.restrictSections_app_toSheafifySections]
  exact (ConcreteCategory.congr_hom ((J.toSheafifySections V).naturality
    (F.overMapCompPresheafHomIso M.obj N.obj f).hom) _).symm.trans (Fiber.homEquiv_homMk _).symm

open Functor.LaxMonoidal in
@[simp, reassoc]
lemma Fiber.pullbackHom_comp (f : V ⟶ U) {M N P : Fiber J F U} (s : M ⟶ N) (t : N ⟶ P) :
    Fiber.pullbackHom f (s ≫ t) = Fiber.pullbackHom f s ≫ Fiber.pullbackHom f t := by
  let R := (Functor.whiskeringLeft (Over V)ᵒᵖ (Over U)ᵒᵖ (Type v')).obj (Over.map f).op
  let _ : R.Monoidal := .ofChosenFiniteProducts _
  -- The monoidal structure of the restriction `R` is the identity, as its components are the
  -- projections (`Functor.Monoidal.μ_fst`, `Functor.Monoidal.μ_snd`).
  have hμ : μ R (F.presheafHom M.obj N.obj) (F.presheafHom N.obj P.obj) = 𝟙 _ :=
    CartesianMonoidalCategory.hom_ext (X := R.obj (F.presheafHom M.obj N.obj))
      (Y := R.obj (F.presheafHom N.obj P.obj)) _ _
      ((Functor.Monoidal.μ_fst _ _ _).trans (Category.id_comp _).symm)
      ((Functor.Monoidal.μ_snd _ _ _).trans (Category.id_comp _).symm)
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
  have key' := congrArg (J.sheafifySections V).map key
  simp only [Functor.map_comp] at key'
  -- The same compatibility for the sheafified presheaves, from the monoidality of
  -- `J.restrictSections f`.
  have H : μ (J.sheafifySections U) _ _ ≫
      (J.sheafifySections U).map (presheafHomComp M.obj N.obj P.obj) ≫
        (J.restrictSections f).app _ ≫
          (J.sheafifySections V).map (F.overMapCompPresheafHomIso M.obj P.obj f).hom =
      (((J.restrictSections f).app _ ≫
          (J.sheafifySections V).map (F.overMapCompPresheafHomIso M.obj N.obj f).hom) ⊗ₘ
        ((J.restrictSections f).app _ ≫
          (J.sheafifySections V).map (F.overMapCompPresheafHomIso N.obj P.obj f).hom)) ≫
        μ (J.sheafifySections V) _ _ ≫ (J.sheafifySections V).map (presheafHomComp _ _ _) := by
    rw [NatTrans.naturality_assoc, ← Category.assoc (μ _ _ _),
      NatTrans.IsMonoidal.tensor (τ := J.restrictSections f), comp_μ, Category.assoc,
      Category.assoc, Functor.comp_map, key', ← μ_natural_assoc,
      ← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  ext
  rw [Fiber.homEquiv_pullbackHom, Fiber.homEquiv_comp, Fiber.homEquiv_comp,
    Fiber.homEquiv_pullbackHom, Fiber.homEquiv_pullbackHom]
  -- The source of `H` is a tensor product in `Type v'`, which is the product type only after
  -- unfolding, so the pair is ascribed the product type for the anonymous constructor.
  exact ConcreteCategory.congr_hom H (show (J.sheafifySections U).obj (F.presheafHom M.obj N.obj) ×
    (J.sheafifySections U).obj (F.presheafHom N.obj P.obj) from
      (Fiber.homEquiv M N s, Fiber.homEquiv N P t))

open Functor.LaxMonoidal in
@[simp]
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
  have key' := congrArg (J.sheafifySections V).map key
  simp only [Functor.map_comp] at key'
  have H : ε (J.sheafifySections U) ≫ (J.sheafifySections U).map (presheafHomId M.obj) ≫
      (J.restrictSections f).app _ ≫
        (J.sheafifySections V).map (F.overMapCompPresheafHomIso M.obj M.obj f).hom =
      ε (J.sheafifySections V) ≫ (J.sheafifySections V).map (presheafHomId _) := by
    rw [NatTrans.naturality_assoc, ← Category.assoc (ε _),
      NatTrans.IsMonoidal.unit (τ := J.restrictSections f), comp_ε, Category.assoc,
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

variable (J) in
/-- The sections over `T : Over U` of the sheafification of the presheaf of morphisms from `M` to
`N` are the morphisms between the pullbacks of `M` and `N` to `T.left` in the fibre of the
Hom-sheafification. -/
def sheafifyPresheafHomEquiv (M N : F.obj (.mk (op U))) (T : Over U)
    [HasSheafify (J.over T.left) (Type v')] [(J.over T.left).WEqualsLocallyBijective (Type v')] :
    (sheafify (J.over U) (F.presheafHom M N)).obj (op T) ≃
      (Fiber.mk (J := J) ((F.map T.hom.op.toLoc).toFunctor.obj M) ⟶
        Fiber.mk ((F.map T.hom.op.toLoc).toFunctor.obj N)) :=
  Equiv.ofBijective (fun t ↦ (Fiber.homEquiv _ _).symm ((J.sheafifySections T.left).map
      (F.overMapCompPresheafHomIso M N T.hom).hom ((J.restrictSectionsOver T).app _ t)))
    ((Fiber.homEquiv _ _).symm.bijective.comp
      ((((J.sheafifySections T.left).mapIso
        (F.overMapCompPresheafHomIso M N T.hom)).toEquiv.bijective).comp
          (GrothendieckTopology.restrictSectionsOver_app_bijective J T _)))

@[simp]
lemma Fiber.homEquiv_sheafifyPresheafHomEquiv (M N : F.obj (.mk (op U))) (T : Over U)
    [HasSheafify (J.over T.left) (Type v')] [(J.over T.left).WEqualsLocallyBijective (Type v')]
    (t : (sheafify (J.over U) (F.presheafHom M N)).obj (op T)) :
    Fiber.homEquiv _ _ (sheafifyPresheafHomEquiv J M N T t) = (J.sheafifySections T.left).map
      (F.overMapCompPresheafHomIso M N T.hom).hom ((J.restrictSectionsOver T).app _ t) :=
  Equiv.apply_symm_apply _ _

/-- The morphism corresponding to the image of a local morphism `x` in the sheafification is the
image of `x` under the comparison functor `toFiber`. -/
lemma sheafifyPresheafHomEquiv_toSheafify (M N : F.obj (.mk (op U))) (T : Over U)
    [HasSheafify (J.over T.left) (Type v')] [(J.over T.left).WEqualsLocallyBijective (Type v')]
    (x : (F.presheafHom M N).obj (op T)) :
    sheafifyPresheafHomEquiv J M N T ((toSheafify (J.over U) (F.presheafHom M N)).app (op T) x) =
      (toFiber J F T.left).map x := by
  -- Restricting `x` to `(Over.map T.hom).obj (Over.mk (𝟙 T.left))` and conjugating it by the
  -- comparison isomorphisms of `F` gives its pullback along the identity.
  have h : (F.overMapCompPresheafHomIso M N T.hom).hom.app (op (Over.mk (𝟙 T.left)))
      ((F.presheafHom M N).map (Over.mapObjMkIdHom T).op x) = F.presheafHomObjHomEquiv x := by
    -- The restriction of `x` is its `pullHom` along the identity, which conjugates by the same
    -- comparison isomorphisms.
    have hx : (F.presheafHom M N).map (Over.mapObjMkIdHom T).op x = pullHom x (𝟙 T.left)
        ((Over.map T.hom).obj (Over.mk (𝟙 T.left))).hom
        ((Over.map T.hom).obj (Over.mk (𝟙 T.left))).hom (by simp) (by simp) := by
      rw [Over.mapObjMkIdHom, Over.mapMkIso_hom]
      -- Restriction along `Over.homMk g` is `pullHom` along `g`, by definition of `presheafHom`.
      rfl
    rw [overMapCompPresheafHomIso_hom_app_apply, presheafHomObjHomEquiv_eq_map, hx]
    simp [pullHom]
  apply Fiber.hom_ext
  rw [Fiber.homEquiv_sheafifyPresheafHomEquiv,
    GrothendieckTopology.restrictSectionsOver_app_toSheafify]
  refine (ConcreteCategory.congr_hom ((J.toSheafifySections T.left).naturality
    (F.overMapCompPresheafHomIso M N T.hom).hom) _).symm.trans ?_
  exact (congrArg ((J.toSheafifySections T.left).app _) h).trans (Fiber.homEquiv_homMk _).symm

/-- The pullback along `f` of a morphism of the fibre over `U` corresponds to the restriction of
the corresponding section to `Over.mk f`. -/
lemma Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv (f : V ⟶ U) {M N : Fiber J F U}
    (s : M ⟶ N) :
    Fiber.pullbackHom f s = sheafifyPresheafHomEquiv J M.obj N.obj (Over.mk f)
      ((sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
        (Over.mkIdTerminal.from (Over.mk f)).op (Fiber.homEquiv M N s)) := by
  apply Fiber.hom_ext
  -- The morphisms on the right are typed by `Fiber.mk X` with `(Fiber.mk X).obj = X` only up to
  -- unfolding (`Fiber.obj_mk`), so the steps are chained by `exact`.
  exact (Fiber.homEquiv_pullbackHom f s).trans ((congrArg ((J.sheafifySections V).map
    (F.overMapCompPresheafHomIso M.obj N.obj f).hom)
      (GrothendieckTopology.restrictSections_app J f _)).trans
        (Fiber.homEquiv_sheafifyPresheafHomEquiv M.obj N.obj (Over.mk f) _).symm)

/-- Pulling back the morphism of the fibre over `T.left` corresponding to a section over `T`
along `p.left`, for `p : T' ⟶ T` in `Over U`, gives the morphism corresponding to the restricted
section over `T'`, up to the comparison isomorphisms of `F`. -/
lemma toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp (M N : F.obj (.mk (op U)))
    {T T' : Over U} [HasSheafify (J.over T.left) (Type v')]
    [(J.over T.left).WEqualsLocallyBijective (Type v')] [HasSheafify (J.over T'.left) (Type v')]
    [(J.over T'.left).WEqualsLocallyBijective (Type v')] (p : T' ⟶ T)
    (t : (sheafify (J.over U) (F.presheafHom M N)).obj (op T)) :
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
      F.presheafHomPostcomp _ ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
        (by rw [← Over.w p]; rfl)).inv.toNatTrans.app N) ≫
      presheafHomPrecomp ((F.mapComp' T.hom.op.toLoc p.left.op.toLoc T'.hom.op.toLoc
        (by rw [← Over.w p]; rfl)).hom.toNatTrans.app M) =
      Functor.whiskerRight (NatTrans.op (Over.mapCompOfHom p).hom) (F.presheafHom M N) ≫
        (F.overMapCompPresheafHomIso M N T'.hom).hom := by
    refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    have h := mapComp'_conj_eq_pullHom T.hom p.left T'.hom (Over.w p) Z.unop.hom _ _ rfl rfl
      ((Over.mapCompOfHom p).hom.app Z.unop).left (by simp) M N w
    simp only [Category.assoc] at h
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, presheafHomPostcomp_app_apply, presheafHomPrecomp_app_apply,
      overMapCompPresheafHomIso_hom_app_apply, Category.assoc]
    -- The remaining component of `overMapCompPresheafHomIso` is at an object of the form
    -- `(Over.map p.left).op.obj Z`, at which its argument `w` is typed only up to unfolding.
    erw [overMapCompPresheafHomIso_hom_app_apply]
    simp only [Category.assoc]
    exact h
  have key' := congrArg (J.sheafifySections T'.left).map key
  simp only [Functor.map_comp] at key'
  have hθ := ConcreteCategory.congr_hom ((J.restrictSections p.left).naturality
    (F.overMapCompPresheafHomIso M N T.hom).hom) ((J.restrictSectionsOver T).app _ t)
  apply Fiber.hom_ext
  refine (Fiber.homEquiv_toFiber_map_comp _ _).trans ?_
  -- The goal types its morphisms by the objects `(toFiber J F T'.left).obj X` and over the
  -- composite `F.map T.hom.op.toLoc ≫ F.map p.left.op.toLoc`, where these lemmas have `Fiber.mk X`
  -- and `F.map T'.hom.op.toLoc`; these agree only up to unfolding `toFiber_obj` and the
  -- composite, so the rewrites need `erw`.
  erw [Fiber.homEquiv_comp_toFiber_map, Fiber.homEquiv_pullbackHom,
    Fiber.homEquiv_sheafifyPresheafHomEquiv, Fiber.homEquiv_sheafifyPresheafHomEquiv,
    ← GrothendieckTopology.restrictSectionsOver_comp J p]
  simp only [ConcreteCategory.comp_apply] at hθ
  -- For the same reason, `hθ` matches the goal only up to unfolding.
  erw [hθ]
  exact ConcreteCategory.congr_hom key' _

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
        F.presheafHomPostcomp _ ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app N) ≫
          presheafHomPrecomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M) := by
    refine NatTrans.ext (funext fun Z ↦ ConcreteCategory.hom_ext _ _ fun w ↦ ?_)
    have h := mapComp'_conj_eq_mapId'_conj_pullHom Z.unop.hom _ rfl
      ((Over.mapId U).inv.app Z.unop).left (by simp) M N w
    simp only [NatTrans.comp_app, ConcreteCategory.comp_apply, Functor.whiskerRight_app,
      presheafHomPrecomp_app_apply, overMapCompPresheafHomIso_hom_app_apply]
    -- As in `toFiber_map_comp_pullbackHom_sheafifyPresheafHomEquiv_comp`, the remaining component
    -- is at an object at which its argument is typed only up to unfolding.
    erw [presheafHomPostcomp_app_apply]
    exact h
  apply Fiber.hom_ext
  refine Eq.trans ?_ (Fiber.homEquiv_toFiber_map_comp _ _).symm
  -- The morphisms of the goal are typed by `Fiber.mk ((F.map (Over.mk (𝟙 U)).hom.op.toLoc) ...)`
  -- and `Fiber.mk (𝟙 _ ...)`, which agree with the objects in these lemmas only up to unfolding
  -- `Fiber.obj` and `(Over.mk (𝟙 U)).hom = 𝟙 U`, so the rewrites need `erw`.
  erw [Fiber.homEquiv_comp_toFiber_map, Equiv.apply_symm_apply]
  refine Eq.trans ?_ (congrArg (fun z ↦ (J.sheafifySections U).map
    (presheafHomPrecomp ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M))
      ((J.sheafifySections U).map
        (F.presheafHomPostcomp _ ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app N)) z))
          (Equiv.apply_symm_apply (Fiber.homEquiv (Fiber.mk M) (Fiber.mk N)) s).symm)
  conv_rhs => rw [← GrothendieckTopology.restrictSectionsOver_mkId J _ s]
  -- The goal contains `F.overMapCompPresheafHomIso M N (Over.mk (𝟙 U)).hom`, which is `key`'s
  -- left side only after reducing `(Over.mk (𝟙 U)).hom` to `𝟙 U`.
  erw [key]
  simp only [Functor.map_comp, ConcreteCategory.comp_apply]
  -- The two sides differ only in writing the slice site as over `(Over.mk (𝟙 U)).left` or
  -- over `U`, which are the same object.
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
def Fiber.pullbackId (U : C) [HasSheafify (J.over U) (Type v')]
    [(J.over U).WEqualsLocallyBijective (Type v')] : Fiber.pullback J F (𝟙 U) ≅ 𝟭 (Fiber J F U) :=
  NatIso.ofComponents (fun M ↦ (toFiber J F U).mapIso
      ((Cat.Hom.toNatIso (F.mapId' (𝟙 U).op.toLoc (by simp))).app M.obj)) fun {M N} s ↦ by
    -- The pullback of `s` along `𝟙 U` is `s` conjugated by the unit isomorphisms of `F`.
    have hs : (sheafify (J.over U) (F.presheafHom M.obj N.obj)).map
        (Over.mkIdTerminal.from (Over.mk (𝟙 U))).op (Fiber.homEquiv M N s) =
          Fiber.homEquiv M N s := by
      have hterm : Over.mkIdTerminal.from (Over.mk (𝟙 U)) = 𝟙 _ := Over.mkIdTerminal.hom_ext _ _
      rw [hterm]
      exact ConcreteCategory.congr_hom ((sheafify (J.over U) _).map_id _) _
    have h := (Fiber.pullbackHom_eq_sheafifyPresheafHomEquiv (𝟙 U) s).trans
      ((congrArg _ hs).trans (sheafifyPresheafHomEquiv_mkId J M.obj N.obj _))
    -- `h` contains `(Fiber.homEquiv (Fiber.mk M.obj) (Fiber.mk N.obj)).symm` applied to
    -- `Fiber.homEquiv M N s`; the two equivalences agree only up to unfolding `Fiber.mk M.obj = M`
    -- (`Fiber.mk_obj`), so the cancellation needs `erw`.
    erw [Equiv.symm_apply_apply] at h
    exact (Iso.eq_comp_inv _).1 (h.trans (Category.assoc _ _ _).symm)

@[simp]
lemma Fiber.pullbackId_hom_app (U : C) [HasSheafify (J.over U) (Type v')]
    [(J.over U).WEqualsLocallyBijective (Type v')] (M : Fiber J F U) :
    (Fiber.pullbackId J F U).hom.app M =
      (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).hom.toNatTrans.app M.obj) := (rfl)

@[simp]
lemma Fiber.pullbackId_inv_app (U : C) [HasSheafify (J.over U) (Type v')]
    [(J.over U).WEqualsLocallyBijective (Type v')] (M : Fiber J F U) :
    (Fiber.pullbackId J F U).inv.app M =
      (toFiber J F U).map ((F.mapId' (𝟙 U).op.toLoc (by simp)).inv.toNatTrans.app M.obj) := (rfl)

variable (J F) in
/-- The composition isomorphisms of the pullback functors of the Hom-sheafification, given by the
composition isomorphisms of `F`. -/
def Fiber.pullbackComp {W : C} [HasSheafify (J.over W) (Type v')]
    [(J.over W).WEqualsLocallyBijective (Type v')] (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (h : g ≫ f = gf) :
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
    exact (Iso.eq_comp_inv _).1 (hK.symm.trans (Category.assoc _ _ _).symm)

@[simp]
lemma Fiber.pullbackComp_hom_app {W : C} [HasSheafify (J.over W) (Type v')]
    [(J.over W).WEqualsLocallyBijective (Type v')] (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (h : g ≫ f = gf) (M : Fiber J F U) :
    (Fiber.pullbackComp J F f g gf h).hom.app M =
      (toFiber J F W).map ((F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).hom.toNatTrans.app M.obj) := (rfl)

@[simp]
lemma Fiber.pullbackComp_inv_app {W : C} [HasSheafify (J.over W) (Type v')]
    [(J.over W).WEqualsLocallyBijective (Type v')] (f : V ⟶ U) (g : W ⟶ V) (gf : W ⟶ U)
    (h : g ≫ f = gf) (M : Fiber J F U) :
    (Fiber.pullbackComp J F f g gf h).inv.app M =
      (toFiber J F W).map ((F.mapComp' f.op.toLoc g.op.toLoc gf.op.toLoc
        (by rw [← h]; rfl)).inv.toNatTrans.app M.obj) := (rfl)

end pullback

section pseudofunctor

variable [∀ U : C, HasSheafify (J.over U) (Type v')]
  [∀ U : C, (J.over U).WEqualsLocallyBijective (Type v')] (F : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{v', u'})

/-- The Hom-sheafification of a pseudofunctor `F` for a Grothendieck topology `J`: its fibre over
`U` is `Fiber J F U`, whose morphisms are the sections over the terminal object of the
sheafifications of the presheaves of morphisms of `F`. Its pullback functors are those of `F`
on objects and restrict sheafified sections on morphisms (`Fiber.pullback`). The unit and
composition isomorphisms are the images under `toFiber` of those of `F` (`Fiber.pullbackId`,
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
        rw [← F.mapId'_eq_mapId a]
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
