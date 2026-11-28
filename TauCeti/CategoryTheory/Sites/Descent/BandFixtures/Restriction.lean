/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import TauCeti.CategoryTheory.Sites.Descent.BandCenter.Glue
public import TauCeti.CategoryTheory.Sites.Descent.BandFixtures.Component.Center
public import TauCeti.CategoryTheory.Sites.Descent.IsGerbe
public import TauCeti.CategoryTheory.Sites.Descent.IsStack

/-!
# Central sections of the one-object diagram of a presheaf of commutative groups

Let `P : Cᵒᵖ ⥤ CommGrpCat` be a presheaf of commutative groups on any category `C`, not
necessarily constant. Composing with `MonCat.toCat` gives the pseudofunctor
`RestrictionBandFixtures.groupDiagram P` whose fibre over `U` is the one-object category
`SingleObj P(U)` and whose pullback along `f : V ⟶ U` is `SingleObj.mapHom (P.map f.op)`.

A coefficient `g` of a commutative group `G` is a unit of the categorical centre of `SingleObj G`
(`BandFixtures.singleCenterUnit`), and a coefficient `g ∈ P(U)` is the compatible
central section with value `P(f)(g)` at `f : V ⟶ U` (`RestrictionBandFixtures.groupSection`). This
identifies `P(U)` with the intrinsic central sections over `U`
(`RestrictionBandFixtures.groupSectionsEquiv`), compatibly with restriction, with no topology and no
terminal object. Over a small category the additive presheaf of `P` is therefore isomorphic to the
presheaf of intrinsic central sections, and so are the corresponding sheaves for the bottom
topology (`RestrictionBandFixtures.groupBandSheafIso`). For the bottom topology `groupDiagram P` is
a stack (`Pseudofunctor.isStack_bot`) and a gerbe
(`RestrictionBandFixtures.groupDiagram_gerbe`), any two objects of a fibre being isomorphic by
every coefficient (`RestrictionBandFixtures.groupIso`).

These are the varying fixtures for the intrinsic band of the Stacks Project, Lemma 8.11.8 (0CJY).

## Main definitions

In the namespace `CategoryTheory.Pseudofunctor.RestrictionBandFixtures`:

* `groupDiagram P`: the one-object diagram of a presheaf of commutative groups.
* `groupIso P U x y g : x ≅ y`, with inverse coefficient `g⁻¹`.
* `groupSection P U : P(U) →* ZF(U)` and `groupSectionsEquiv P U : P(U) ≃* ZF(U)`.
* `groupSectionsPresheafIso P`, `groupBandSheaf P`, `groupBandSheafIso P`, for a small base.

## Main results

* `restrict_groupSection`: restriction along `f` sends the section of `g` to the section of
  `P(f)(g)`.
* `groupDiagram_gerbe`: `groupDiagram P` is a gerbe for the bottom topology, with no terminal
  object.

## References

* [The Stacks Project, Lemma 8.11.8 (0CJY)](https://stacks.math.columbia.edu/tag/0CJY)
-/

public section

universe w v u

open CategoryTheory Opposite Bicategory

namespace CategoryTheory.Pseudofunctor.RestrictionBandFixtures

open IntrinsicBandSections BandFixtures

variable {C : Type u} [Category.{v} C]

/-- The **one-object diagram** of a presheaf of commutative groups `P`: the pseudofunctor with
fibre `SingleObj P(U)` over `U` and pullback `SingleObj.mapHom (P.map f.op)` along `f`. -/
abbrev groupDiagram (P : Cᵒᵖ ⥤ CommGrpCat.{w}) : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat.{w, 0} :=
  (P ⋙ forget₂ CommGrpCat GrpCat ⋙ forget₂ GrpCat MonCat ⋙ MonCat.toCat).toPseudofunctor'

/-- Pulling back a morphism of `groupDiagram P` along `f` applies `P.map f.op`. -/
@[simp]
theorem groupDiagram_map_map (P : Cᵒᵖ ⥤ CommGrpCat.{w}) {U V : C} (f : V ⟶ U)
    {x y : (groupDiagram P).obj (.mk (op U))} (m : x ⟶ y) :
    ((groupDiagram P).map f.op.toLoc).toFunctor.map m = (P.map f.op (m : P.obj (op U)) :) :=
  (rfl)

/-- Any coefficient `g ∈ P(U)` is an isomorphism between any two objects of the one-object fibre
of `groupDiagram P` over `U`, with inverse coefficient `g⁻¹`. -/
def groupIso (P : Cᵒᵖ ⥤ CommGrpCat.{w}) (U : C) (x y : (groupDiagram P).obj (.mk (op U)))
    (g : P.obj (op U)) : x ≅ y where
  hom := (g : P.obj (op U))
  inv := (g⁻¹ : P.obj (op U))
  hom_inv_id := inv_mul_cancel g
  inv_hom_id := mul_inv_cancel g

@[simp]
theorem groupIso_hom (P : Cᵒᵖ ⥤ CommGrpCat.{w}) (U : C) (x y : (groupDiagram P).obj (.mk (op U)))
    (g : P.obj (op U)) : (groupIso P U x y g).hom = (g : P.obj (op U)) :=
  (rfl)

@[simp]
theorem groupIso_inv (P : Cᵒᵖ ⥤ CommGrpCat.{w}) (U : C) (x y : (groupDiagram P).obj (.mk (op U)))
    (g : P.obj (op U)) : (groupIso P U x y g).inv = (g⁻¹ : P.obj (op U)) :=
  (rfl)

/-! ### The central sections of `groupDiagram P` -/

variable (P : Cᵒᵖ ⥤ CommGrpCat.{w})

/-- The compatible central section of a coefficient `g ∈ P(U)`, as a function; see
`groupSection`. -/
private def groupSectionFun (U : C) (g : P.obj (op U)) :
    IntrinsicBandSections (groupDiagram P) U :=
  ofCompatible (fun V f ↦ singleCenterUnit (G := P.obj (op V)) (P.map f.op g))
    ((isPullbackCompatible_iff _).2 fun V W f h x ↦ by
      -- The fibre of `groupDiagram P` over `V` is `SingleObj P(V)` only after unfolding
      -- `MonCat.toCat`, so `singleCenter_app` and `groupDiagram_map_map` do not match
      -- syntactically; both sides are the coefficients they denote by definition.
      change P.map h.op (P.map f.op g) = P.map (h ≫ f).op g
      rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply])

private theorem val_groupSectionFun (U : C) (g : P.obj (op U)) {V : C} (f : V ⟶ U) :
    (groupSectionFun P U g).val V f = singleCenterUnit (G := P.obj (op V)) (P.map f.op g) :=
  val_ofCompatible _ _ V f

/-- The **compatible section of a coefficient** `g ∈ P(U)`: the intrinsic central section of
`groupDiagram P` whose centre coefficient at `f : V ⟶ U` is `P(f)(g)`, as a group homomorphism
`P(U) →* ZF(U)`. -/
def groupSection (U : C) : P.obj (op U) →* IntrinsicBandSections (groupDiagram P) U where
  toFun := groupSectionFun P U
  -- In both fields the two sides are units of the centres of `SingleObj P(V)` and of the fibre
  -- of `groupDiagram P` over `V`, which agree only after unfolding `MonCat.toCat`; after the
  -- rewrites they are syntactically equal up to that unfolding.
  map_one' := Subtype.ext (funext₂ fun V f ↦ by
    rw [val_groupSectionFun, map_one, singleCenterUnit_one, val_one]
    rfl)
  map_mul' g h := Subtype.ext (funext₂ fun V f ↦ by
    rw [val_groupSectionFun, map_mul, singleCenterUnit_mul, val_mul, val_groupSectionFun,
      val_groupSectionFun]
    rfl)

/-- The centre coefficient of `groupSection P U g` at `f : V ⟶ U` is `P(f)(g)`. -/
@[simp]
theorem val_groupSection (U : C) (g : P.obj (op U)) {V : C} (f : V ⟶ U) :
    (groupSection P U g).val V f = singleCenterUnit (G := P.obj (op V)) (P.map f.op g) :=
  val_groupSectionFun P U g f

/-- **Restriction of the section of a coefficient**: restricting `groupSection P U g` along
`f : V ⟶ U` gives the section of `P(f)(g)`. -/
@[simp]
theorem restrict_groupSection {U V : C} (f : V ⟶ U) (g : P.obj (op U)) :
    restrict f (groupSection P U g) = groupSection P V (P.map f.op g) :=
  IntrinsicBandSections.ext fun W a x ↦ by
    rw [val_restrict, val_groupSection, val_groupSection, op_comp, Functor.map_comp,
      ConcreteCategory.comp_apply]

/-- **The central sections of `groupDiagram P` are the coefficients**: the forward map is
`groupSection P U`, the inverse reads the centre coefficient at the identity of `U`. No topology
or terminal object is used. -/
def groupSectionsEquiv (U : C) : P.obj (op U) ≃* IntrinsicBandSections (groupDiagram P) U where
  toFun := groupSection P U
  invFun s := ((s.val U (𝟙 U)).val.app (SingleObj.star (P.obj (op U))) : P.obj (op U))
  left_inv g := by
    simp only [val_groupSection, op_id, Functor.map_id, CommGrpCat.id_apply,
      val_singleCenterUnit, singleCenter_app]
  right_inv s := IntrinsicBandSections.ext fun V f x ↦ by
    have h := IntrinsicBandSections.map_app s (𝟙 U) f (SingleObj.star (P.obj (op U)))
    rw [Category.comp_id] at h
    -- As in `groupSection`, the component of `groupSection P U g` at `f` is the pullback of `g`
    -- along `f` only after unfolding `MonCat.toCat`, so `h` closes the goal up to definition.
    exact (congrArg (fun z : (CatCenter _)ˣ ↦ z.val.app x) (val_groupSection P U _ f)).trans h
  map_mul' := (groupSection P U).map_mul

@[simp]
theorem groupSectionsEquiv_apply (U : C) (g : P.obj (op U)) :
    groupSectionsEquiv P U g = groupSection P U g :=
  (rfl)

@[simp]
theorem groupSectionsEquiv_symm_apply (U : C) (s : IntrinsicBandSections (groupDiagram P) U) :
    (groupSectionsEquiv P U).symm s =
      ((s.val U (𝟙 U)).val.app (SingleObj.star (P.obj (op U))) : P.obj (op U)) :=
  (rfl)

/-- Restriction along `f : V ⟶ U` corresponds to `P(f)` under `groupSectionsEquiv`. -/
theorem groupSectionsEquiv_restrict {U V : C} (f : V ⟶ U) (g : P.obj (op U)) :
    restrict f (groupSectionsEquiv P U g) = groupSectionsEquiv P V (P.map f.op g) :=
  restrict_groupSection P f g

/-! ### Stack and gerbe for the bottom topology -/

/-- **The one-object diagram is a gerbe for the bottom topology**, on any category and without a
terminal object: every pseudofunctor is a stack for `⊥`, the fibres are nonempty one-object
groupoids, and any two objects of a fibre are isomorphic. -/
instance groupDiagram_gerbe : (groupDiagram P).IsGerbe ⊥ where
  isGroupoid U := inferInstanceAs (IsGroupoid (SingleObj (P.obj (op U))))
  exists_covering_nonempty U :=
    ⟨⊤, (⊥ : GrothendieckTopology C).top_mem U, fun V _ _ ↦ ⟨SingleObj.star (P.obj (op V))⟩⟩
  exists_covering_iso {U} _ _ :=
    ⟨⊤, (⊥ : GrothendieckTopology C).top_mem U, fun V _ _ ↦ ⟨groupIso P V _ _ 1⟩⟩

/-! ### Presheaves and sheaves over a small base -/

section Small

variable {B : Type} [SmallCategory B] (P : Bᵒᵖ ⥤ CommGrpCat.{w})

/-- Over a small category, the **additive presheaf of `P` is the presheaf of intrinsic central
sections** of `groupDiagram P`, with components `groupSectionsEquiv`. -/
def groupSectionsPresheafIso :
    P ⋙ CommGrpCat.toAddCommGrp ≅ IntrinsicBandSections.presheaf (groupDiagram P) :=
  NatIso.ofComponents (fun U ↦ (MulEquiv.toAdditive (groupSectionsEquiv P U.unop)).toAddCommGrpIso)
    fun f ↦ AddCommGrpCat.ext fun g ↦
      congrArg Additive.ofMul (groupSectionsEquiv_restrict P f.unop g.toMul).symm

theorem groupSectionsPresheafIso_hom_app_apply (U : Bᵒᵖ)
    (g : (P ⋙ CommGrpCat.toAddCommGrp).obj U) :
    (groupSectionsPresheafIso P).hom.app U g =
      Additive.ofMul (groupSection P U.unop (Additive.toMul g)) :=
  (rfl)

theorem groupSectionsPresheafIso_inv_app_apply (U : Bᵒᵖ)
    (s : (IntrinsicBandSections.presheaf (groupDiagram P)).obj U) :
    (groupSectionsPresheafIso P).inv.app U s =
      Additive.ofMul ((s.toMul.val U.unop (𝟙 _)).val.app (SingleObj.star (P.obj U)) :
        P.obj U) :=
  (rfl)

/-- The **sheaf of intrinsic central sections** of `groupDiagram P` for the bottom topology, on a
small base. -/
@[expose]
def groupBandSheaf : Sheaf (⊥ : GrothendieckTopology B) AddCommGrpCat.{w} :=
  ⟨IntrinsicBandSections.presheaf (groupDiagram P), Presheaf.isSheaf_bot _⟩

/-- The underlying presheaf of `groupBandSheaf P` is the presheaf of intrinsic central sections. -/
@[simp]
theorem groupBandSheaf_obj :
    (groupBandSheaf P).obj = IntrinsicBandSections.presheaf (groupDiagram P) :=
  (rfl)

/-- Over a small category, the **coefficient sheaf of `P` for the bottom topology is the sheaf of
intrinsic central sections** of `groupDiagram P`. -/
def groupBandSheafIso :
    (⟨P ⋙ CommGrpCat.toAddCommGrp, Presheaf.isSheaf_bot _⟩ :
      Sheaf (⊥ : GrothendieckTopology B) AddCommGrpCat.{w}) ≅ groupBandSheaf P :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso (groupSectionsPresheafIso P)

@[simp]
theorem groupBandSheafIso_hom_hom :
    (groupBandSheafIso P).hom.hom = (groupSectionsPresheafIso P).hom :=
  (rfl)

@[simp]
theorem groupBandSheafIso_inv_hom :
    (groupBandSheafIso P).inv.hom = (groupSectionsPresheafIso P).inv :=
  (rfl)

end Small

end CategoryTheory.Pseudofunctor.RestrictionBandFixtures
