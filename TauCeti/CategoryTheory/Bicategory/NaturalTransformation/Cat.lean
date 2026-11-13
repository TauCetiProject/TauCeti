/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Cat
public import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo
public import TauCeti.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Equivalence

/-!
# Strong transformations into `Cat` and pointwise equivalences

A strong transformation between pseudofunctors into `Cat` that take the same values on objects
can have identity components. Its naturality isomorphism at `f` is then determined by a natural
isomorphism `e : T ≅ U` between the two functors `T` and `U` that the pseudofunctors assign to
`f`, as the composite `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U`.

This file reduces the conditions on such data to componentwise identities between the natural
isomorphisms `e`: the unit and composition conditions
(`Cat.rightUnitor_trans_leftUnitor_symm_naturality_id`,
`Cat.rightUnitor_trans_leftUnitor_symm_naturality_comp`), and the condition on an invertible
modification with unitor components from a composite of two such transformations to the identity
(`Cat.rightUnitor_trans_leftUnitor_symm_comp_modification`). The statements quantify over
arbitrary `1`-morphisms, so that they apply by unification to goals whose `1`-morphisms are values
of composite pseudofunctors, which `simp` and `rw` do not see through. The same reduction
handles identity and composite transport cells. The file also evaluates the naturality cell
of a composite strong transformation on objects, with the Cat endpoints made explicit.

A strong transformation into `Cat` is an equivalence whenever its component functors are
equivalences, for an arbitrary source bicategory. The equivalence
`StrongTrans.equivalenceOfIsEquivalence` uses the chosen component quasi-inverses, units, and
counits. Its inverse naturality satisfies compatibility with those counits; the
component equations allow callers to use the equivalence without unfolding its construction.
-/

public section

universe w v

namespace CategoryTheory

open Bicategory

namespace Cat

/-- The components of the isomorphism `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U` are those
of `e`. -/
lemma rightUnitor_trans_leftUnitor_symm_hom_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom.toNatTrans.app X = e.hom.toNatTrans.app X := by
  simp

/-- The components of the inverse of `ρ_ T ≪≫ e ≪≫ (λ_ U).symm : T ≫ 𝟙 _ ≅ 𝟙 _ ≫ U` are those
of the inverse of `e`. -/
lemma rightUnitor_trans_leftUnitor_symm_inv_app {D D' : Cat.{v, w}} {T U : D ⟶ D'} (e : T ≅ U)
    (X : D) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).inv.toNatTrans.app X = e.inv.toNatTrans.app X := by
  simp

/-- The unit condition for a strong transformation with identity component and naturality
isomorphism `ρ_ T ≪≫ e ≪≫ (λ_ U).symm`, reduced to a componentwise identity. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_id {D : Cat.{v, w}} {T U : D ⟶ D} (e : T ≅ U)
    (mT : T ≅ 𝟙 D) (mU : U ≅ 𝟙 D)
    (h : ∀ X, e.hom.toNatTrans.app X ≫ mU.hom.toNatTrans.app X = mT.hom.toNatTrans.app X) :
    (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom ≫ 𝟙 D ◁ mU.hom =
      mT.hom ▷ 𝟙 D ≫ (λ_ (𝟙 D)).hom ≫ (ρ_ (𝟙 D)).inv := by
  ext X
  simpa using h X

/-- The composition condition for a strong transformation with identity components and
naturality isomorphisms `ρ_ T ≪≫ e ≪≫ (λ_ U).symm`, reduced to a componentwise identity. -/
lemma rightUnitor_trans_leftUnitor_symm_naturality_comp {D₀ D₁ D₂ : Cat.{v, w}}
    {T₀₁ U₀₁ : D₀ ⟶ D₁} {T₁₂ U₁₂ : D₁ ⟶ D₂} {T₀₂ U₀₂ : D₀ ⟶ D₂} (e₀₁ : T₀₁ ≅ U₀₁)
    (e₁₂ : T₁₂ ≅ U₁₂) (e₀₂ : T₀₂ ≅ U₀₂) (mT : T₀₂ ≅ T₀₁ ≫ T₁₂) (mU : U₀₂ ≅ U₀₁ ≫ U₁₂)
    (h : ∀ X, e₀₂.hom.toNatTrans.app X ≫ mU.hom.toNatTrans.app X =
      mT.hom.toNatTrans.app X ≫ e₁₂.hom.toNatTrans.app (T₀₁.toFunctor.obj X) ≫
        U₁₂.toFunctor.map (e₀₁.hom.toNatTrans.app X)) :
    (ρ_ T₀₂ ≪≫ e₀₂ ≪≫ (λ_ U₀₂).symm).hom ≫ 𝟙 D₀ ◁ mU.hom =
      mT.hom ▷ 𝟙 D₂ ≫ (α_ _ _ _).hom ≫ T₀₁ ◁ (ρ_ T₁₂ ≪≫ e₁₂ ≪≫ (λ_ U₁₂).symm).hom ≫
        (α_ _ _ _).inv ≫ (ρ_ T₀₁ ≪≫ e₀₁ ≪≫ (λ_ U₀₁).symm).hom ▷ U₁₂ ≫ (α_ _ _ _).hom := by
  ext X
  simpa using h X

/-- The modification condition for an invertible modification with left unitor components from
the composite of two strong transformations into `Cat` with identity components to the identity,
when their naturality isomorphisms are given by mutually inverse isomorphisms `e` and `e'`. -/
lemma rightUnitor_trans_leftUnitor_symm_comp_modification {D D' : Cat.{v, w}} {T U : D ⟶ D'}
    (e : T ≅ U) (e' : U ≅ T)
    (h : ∀ X, e.hom.toNatTrans.app X ≫ e'.hom.toNatTrans.app X = 𝟙 _) :
    T ◁ (λ_ (𝟙 D')).hom ≫ (ρ_ T ≪≫ (λ_ T).symm).hom =
      ((α_ _ _ _).inv ≫ (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom ▷ 𝟙 D' ≫ (α_ _ _ _).hom ≫
        𝟙 D ◁ (ρ_ U ≪≫ e' ≪≫ (λ_ T).symm).hom ≫ (α_ _ _ _).inv) ≫ (λ_ (𝟙 D)).hom ▷ T := by
  ext X
  simpa using (h X).symm

/-- The identity transport cell gives a modification with identity components. -/
lemma rightUnitor_trans_leftUnitor_symm_id_modification {D D' : Cat.{v, w}}
    {T : D ⟶ D'} (e : T ≅ T) (h : ∀ X, e.hom.toNatTrans.app X = 𝟙 _) :
    T ◁ 𝟙 (𝟙 D') ≫ ((ρ_ T).hom ≫ (λ_ T).inv) =
      (ρ_ T ≪≫ e ≪≫ (λ_ T).symm).hom ≫ 𝟙 (𝟙 D) ▷ T := by
  ext X
  simpa using (h X).symm

/-- Composition of transport cells gives a modification with inverse left unitor
components. The component equation records the composite of the two natural isomorphisms. -/
lemma rightUnitor_trans_leftUnitor_symm_trans_modification {D D' : Cat.{v, w}}
    {T U V : D ⟶ D'} (e : T ≅ U) (e' : U ≅ V) (e'' : T ≅ V)
    (h : ∀ X, e.hom.toNatTrans.app X ≫ e'.hom.toNatTrans.app X = e''.hom.toNatTrans.app X) :
    T ◁ (λ_ (𝟙 D')).inv ≫
        ((α_ T (𝟙 D') (𝟙 D')).inv ≫
          (ρ_ T ≪≫ e ≪≫ (λ_ U).symm).hom ▷ 𝟙 D' ≫
          (α_ (𝟙 D) U (𝟙 D')).hom ≫
          𝟙 D ◁ (ρ_ U ≪≫ e' ≪≫ (λ_ V).symm).hom ≫
          (α_ (𝟙 D) (𝟙 D) V).inv) =
      (ρ_ T ≪≫ e'' ≪≫ (λ_ V).symm).hom ≫ (λ_ (𝟙 D)).inv ▷ V := by
  ext X
  simpa using h X

end Cat

namespace Pseudofunctor.StrongTrans

universe w₁ v₁ u₁

/-- The naturality cell of a composite strong transformation into `Cat`, on objects. -/
lemma comp_naturality_hom_app {B : Type u₁} [Bicategory.{w₁, v₁} B]
    {F G H : B ⥤ᵖ Cat.{v, w}} (η : F ⟶ G) (θ : G ⟶ H)
    {a b : B} (f : a ⟶ b) (X : F.obj a) :
    ((η ≫ θ).naturality f).hom.toNatTrans.app X =
      (θ.app b).toFunctor.map ((η.naturality f).hom.toNatTrans.app X) ≫
        (θ.naturality f).hom.toNatTrans.app ((η.app a).toFunctor.obj X) := by
  -- Fix the functor endpoints before simplifying the bicategorical component formula.
  let T : F.obj a ⟶ F.obj b := F.map f
  let U : G.obj a ⟶ G.obj b := G.map f
  let V : H.obj a ⟶ H.obj b := H.map f
  let ηa : F.obj a ⟶ G.obj a := η.app a
  let ηb : F.obj b ⟶ G.obj b := η.app b
  let θa : G.obj a ⟶ H.obj a := θ.app a
  let θb : G.obj b ⟶ H.obj b := θ.app b
  let m : T ≫ ηb ⟶ ηa ≫ U := (η.naturality f).hom
  let n : U ≫ θb ⟶ θa ≫ V := (θ.naturality f).hom
  have h : ((α_ T ηb θb).inv ≫ m ▷ θb ≫ (α_ ηa U θb).hom ≫
        ηa ◁ n ≫ (α_ ηa θa V).inv).toNatTrans.app X =
      θb.toFunctor.map (m.toNatTrans.app X) ≫ n.toNatTrans.app (ηa.toFunctor.obj X) := by
    simp
  exact (congrArg (fun m => m.toNatTrans.app X)
    (categoryStruct_comp_naturality_hom η θ f)).trans h

end Pseudofunctor.StrongTrans

end CategoryTheory

/-! ### Pointwise equivalences of strong transformations -/

universe w₁ v₁ u₁
namespace CategoryTheory.Pseudofunctor.StrongTrans

open Bicategory

variable {B : Type u₁} [Bicategory.{w₁, v₁} B] {F G : B ⥤ᵖ Cat.{v, w}}
variable (η : F ⟶ G) [∀ a, (η.app a).toFunctor.IsEquivalence]

/-- The inverse naturality isomorphism obtained by moving the component equivalences
across the naturality square. -/
private noncomputable def inverseNaturality {a b : B} (f : a ⟶ b) :
    (G.map f).toFunctor ⋙ (η.app b).toFunctor.inv ≅
      (η.app a).toFunctor.inv ⋙ (F.map f).toFunctor :=
  Iso.isoInverseComp (G := (η.app a).toFunctor.asEquivalence)
    (Iso.compInverseIso (H := (η.app b).toFunctor.asEquivalence)
      (Cat.Hom.toNatIso (η.naturality f)).symm)

private lemma map_inverseNaturality_hom_app {a b : B} (f : a ⟶ b) (X : G.obj a) :
    (η.app b).toFunctor.map ((η.inverseNaturality f).hom.app X) =
      (η.app b).toFunctor.asEquivalence.counit.app ((G.map f).toFunctor.obj X) ≫
        (G.map f).toFunctor.map ((η.app a).toFunctor.asEquivalence.counitInv.app X) ≫
        (η.naturality f).inv.toNatTrans.app ((η.app a).toFunctor.inv.obj X) := by
  simp only [Functor.comp_obj, inverseNaturality, Cat.Hom.comp_toFunctor,
    Iso.isoInverseComp_hom_app, Functor.asEquivalence_functor, Functor.comp_map,
    Iso.compInverseIso_hom_app, Iso.symm_hom, Cat.Hom.toNatIso_inv, Functor.map_comp,
    Functor.fun_inv_map, Functor.id_obj, Category.assoc, NatIso.cancel_natIso_hom_left]
  erw [← (η.app b).toFunctor.asEquivalence.counit_app_functor]
  erw [(η.app b).toFunctor.asEquivalence.counitInv_naturality_assoc]
  simp only [Functor.asEquivalence_functor, Iso.inv_hom_id_app, Functor.id_obj,
    Category.comp_id]
  rfl

@[reassoc]
private lemma map_inverseNaturality_hom_app_comp {a b : B} (f : a ⟶ b) (X : G.obj a) :
    (η.app b).toFunctor.map ((η.inverseNaturality f).hom.app X) ≫
      (η.naturality f).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) ≫
        (G.map f).toFunctor.map ((η.app a).toFunctor.asEquivalence.counit.app X) =
      (η.app b).toFunctor.asEquivalence.counit.app ((G.map f).toFunctor.obj X) := by
  rw [map_inverseNaturality_hom_app]
  simp [← Functor.map_comp]

private lemma inverseNaturality_naturality {a b : B} {f g : a ⟶ b} (ξ : f ⟶ g)
    (X : G.obj a) :
    (η.app b).toFunctor.inv.map ((G.map₂ ξ).toNatTrans.app X) ≫
      (η.inverseNaturality g).hom.app X =
    (η.inverseNaturality f).hom.app X ≫
      (F.map₂ ξ).toNatTrans.app ((η.app a).toFunctor.inv.obj X) := by
  apply (η.app b).toFunctor.map_injective
  apply (cancel_mono ((η.naturality g).hom.toNatTrans.app
    ((η.app a).toFunctor.inv.obj X) ≫
    (G.map g).toFunctor.map ((η.app a).toFunctor.asEquivalence.counit.app X))).mp
  simp only [Functor.map_comp, Category.assoc]
  erw [η.map_inverseNaturality_hom_app_comp]
  have hn := congrArg (fun t => t.toNatTrans.app ((η.app a).toFunctor.inv.obj X))
    (η.naturality_naturality ξ)
  simp only [Cat.Hom₂.comp_app, Cat.whiskerRight_app, Cat.whiskerLeft_app] at hn
  rw [reassoc_of% hn]
  erw [← (G.map₂ ξ).toNatTrans.naturality,
    η.map_inverseNaturality_hom_app_comp_assoc]
  exact ((η.app b).toFunctor.asEquivalence.counit_naturality
    ((G.map₂ ξ).toNatTrans.app X))

private lemma inverseNaturality_id (a : B) (X : G.obj a) :
    (η.inverseNaturality (𝟙 a)).hom.app X ≫
      (F.mapId a).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) =
      (η.app a).toFunctor.inv.map ((G.mapId a).hom.toNatTrans.app X) := by
  apply (η.app a).toFunctor.map_injective
  apply (cancel_mono ((η.app a).toFunctor.asEquivalence.counit.app X)).mp
  simp only [Functor.map_comp]
  have h : (η.naturality (𝟙 a)).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) ≫
      (G.mapId a).hom.toNatTrans.app ((η.app a).toFunctor.obj
        ((η.app a).toFunctor.inv.obj X)) =
      (η.app a).toFunctor.map ((F.mapId a).hom.toNatTrans.app
        ((η.app a).toFunctor.inv.obj X)) := by
    rw [naturality_id_hom_app]
    simp
  rw [← h]
  simp only [Category.assoc]
  erw [← (G.mapId a).hom.toNatTrans.naturality,
    η.map_inverseNaturality_hom_app_comp_assoc]
  exact ((η.app a).toFunctor.asEquivalence.counit_naturality
    ((G.mapId a).hom.toNatTrans.app X)).symm

private lemma inverseNaturality_comp {a b c : B} (f : a ⟶ b) (g : b ⟶ c) (X : G.obj a) :
    (η.inverseNaturality (f ≫ g)).hom.app X ≫
      (F.mapComp f g).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) =
      (η.app c).toFunctor.inv.map ((G.mapComp f g).hom.toNatTrans.app X) ≫
        (η.inverseNaturality g).hom.app ((G.map f).toFunctor.obj X) ≫
          (F.map g).toFunctor.map ((η.inverseNaturality f).hom.app X) := by
  apply (η.app c).toFunctor.map_injective
  apply (cancel_mono ((η.naturality g).hom.toNatTrans.app
    ((F.map f).toFunctor.obj ((η.app a).toFunctor.inv.obj X)) ≫
      (G.map g).toFunctor.map ((η.naturality f).hom.toNatTrans.app
        ((η.app a).toFunctor.inv.obj X)) ≫
      (G.map g).toFunctor.map ((G.map f).toFunctor.map
        ((η.app a).toFunctor.asEquivalence.counit.app X)))).mp
  simp only [Functor.map_comp, Category.assoc]
  have h : (η.app c).toFunctor.map ((F.mapComp f g).hom.toNatTrans.app
        ((η.app a).toFunctor.inv.obj X)) ≫
      (η.naturality g).hom.toNatTrans.app
        ((F.map f).toFunctor.obj ((η.app a).toFunctor.inv.obj X)) ≫
      (G.map g).toFunctor.map ((η.naturality f).hom.toNatTrans.app
        ((η.app a).toFunctor.inv.obj X)) =
      (η.naturality (f ≫ g)).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) ≫
        (G.mapComp f g).hom.toNatTrans.app
          ((η.app a).toFunctor.obj ((η.app a).toFunctor.inv.obj X)) := by
    rw [naturality_comp_hom_app]
    simp
  rw [reassoc_of% h]
  erw [← (G.mapComp f g).hom.toNatTrans.naturality,
    η.map_inverseNaturality_hom_app_comp_assoc]
  have hn : (η.app c).toFunctor.map
        ((F.map g).toFunctor.map ((η.inverseNaturality f).hom.app X)) ≫
      (η.naturality g).hom.toNatTrans.app
        ((F.map f).toFunctor.obj ((η.app a).toFunctor.inv.obj X)) =
      (η.naturality g).hom.toNatTrans.app
        ((η.app b).toFunctor.inv.obj ((G.map f).toFunctor.obj X)) ≫
      (G.map g).toFunctor.map
        ((η.app b).toFunctor.map ((η.inverseNaturality f).hom.app X)) :=
    (η.naturality g).hom.toNatTrans.naturality ((η.inverseNaturality f).hom.app X)
  rw [reassoc_of% hn]
  have hf := congrArg (G.map g).toFunctor.map
    (η.map_inverseNaturality_hom_app_comp f X)
  simp only [Functor.map_comp] at hf
  rw [hf, η.map_inverseNaturality_hom_app_comp]
  exact ((η.app c).toFunctor.asEquivalence.counit_naturality
    ((G.mapComp f g).hom.toNatTrans.app X)).symm

private lemma inverse_unit_naturality {a b : B} (f : a ⟶ b) (X : F.obj a) :
    (η.app b).toFunctor.asEquivalence.unit.app ((F.map f).toFunctor.obj X) ≫
      (η.app b).toFunctor.inv.map ((η.naturality f).hom.toNatTrans.app X) ≫
        (η.inverseNaturality f).hom.app ((η.app a).toFunctor.obj X) =
      (F.map f).toFunctor.map ((η.app a).toFunctor.asEquivalence.unit.app X) := by
  apply (η.app b).toFunctor.map_injective
  apply (cancel_mono ((η.naturality f).hom.toNatTrans.app
    ((η.app a).toFunctor.inv.obj ((η.app a).toFunctor.obj X)) ≫
      (G.map f).toFunctor.map ((η.app a).toFunctor.asEquivalence.counit.app
        ((η.app a).toFunctor.obj X)))).mp
  simp only [Functor.map_comp, Category.assoc]
  rw [η.map_inverseNaturality_hom_app_comp]
  erw [(η.app b).toFunctor.asEquivalence.counit_naturality]
  rw [← Category.assoc]
  have ht (a : B) (Y : F.obj a) : (η.app a).toFunctor.map
      ((η.app a).toFunctor.asEquivalence.unit.app Y) ≫
      (η.app a).toFunctor.asEquivalence.counit.app ((η.app a).toFunctor.obj Y) = 𝟙 _ :=
    (η.app a).toFunctor.asEquivalence.functor_unit_comp Y
  erw [ht, Category.id_comp]
  have hn : (η.app b).toFunctor.map ((F.map f).toFunctor.map
        ((η.app a).toFunctor.asEquivalence.unit.app X)) ≫
      (η.naturality f).hom.toNatTrans.app
        ((η.app a).toFunctor.inv.obj ((η.app a).toFunctor.obj X)) =
      (η.naturality f).hom.toNatTrans.app X ≫
        (G.map f).toFunctor.map ((η.app a).toFunctor.map
          ((η.app a).toFunctor.asEquivalence.unit.app X)) :=
    (η.naturality f).hom.toNatTrans.naturality _
  rw [reassoc_of% hn]
  have ht' := congrArg (G.map f).toFunctor.map (ht a X)
  simp only [Functor.map_comp, Functor.map_id] at ht'
  rw [ht']
  exact (Category.comp_id _).symm

/-- A strong transformation into `Cat` is an equivalence when each component functor is an
equivalence. Its inverse has the chosen quasi-inverse component functors; its unit and counit
are their chosen unit and counit isomorphisms. -/
-- Expose the record projections so its dependent unit/counit component equations can be stated;
-- its inverse naturality satisfies compatibility with the component counits.
@[expose] noncomputable def equivalenceOfIsEquivalence :
    Bicategory.Equivalence F G where
  hom := η
  -- Keep the inverse data inline so exposing the record does not export proof-only helpers.
  inv := {
    app a := (η.app a).toFunctor.inv.toCatHom
    naturality {a b} f := Cat.Hom.isoMk
      (Iso.isoInverseComp (G := (η.app a).toFunctor.asEquivalence)
        (Iso.compInverseIso (H := (η.app b).toFunctor.asEquivalence)
          (Cat.Hom.toNatIso (η.naturality f)).symm))
    naturality_naturality ξ := by
      ext X
      simpa [inverseNaturality] using! η.inverseNaturality_naturality ξ X
    naturality_id a := by
      ext X
      simpa [inverseNaturality] using! η.inverseNaturality_id a X
    naturality_comp f g := by
      ext X
      simpa [inverseNaturality] using! η.inverseNaturality_comp f g X }
  unit := isoMk (fun a => Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.unitIso)
    (fun {a b} f => by
      exact Cat.unit_modification _ _ _ _
        (fun X => η.inverse_unit_naturality f X))
  counit := isoMk (fun a => Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.counitIso)
    (fun {a b} f => by
      exact Cat.counit_modification _ _ _ _
        (fun X => η.map_inverseNaturality_hom_app_comp f X))
  left_triangle := by
    apply Iso.ext
    simp only [leftZigzagIso_hom, Iso.trans_hom, Iso.symm_hom]
    have reduce {a b : B ⥤ᵖ Cat.{v, w}}
        (f : a ⟶ b) (g : b ⟶ a) (ι : 𝟙 a ⟶ f ≫ g) (ε : g ≫ f ⟶ 𝟙 b) :
        leftZigzag ι ε = ι ▷ f ≫ (α_ f g f).hom ≫ f ◁ ε := by
      simp [leftZigzag, bicategoricalComp]
    refine (reduce η _ _ _).trans ?_
    apply homCategory.ext
    intro a
    simp only [homCategory_comp_as_app, whiskerRight_as_app, whiskerLeft_as_app,
      associator_hom_as_app, leftUnitor_hom_as_app, rightUnitor_inv_as_app]
    dsimp only [isoMk]
    have key {C D : Cat.{v, w}} (P : C ⟶ D) [P.toFunctor.IsEquivalence] :
        (Cat.Hom.isoMk P.toFunctor.asEquivalence.unitIso).hom ▷ P ≫
          (α_ P P.toFunctor.inv.toCatHom P).hom ≫
          P ◁ (Cat.Hom.isoMk P.toFunctor.asEquivalence.counitIso).hom =
            (λ_ P).hom ≫ (ρ_ P).inv := by
      obtain ⟨P⟩ := P
      simpa [leftZigzag, bicategoricalComp] using!
        P.asEquivalence.toAdjunction.toCat.left_triangle
    exact key (η.app a)

/-- The forward strong transformation is the original one. -/
@[simp]
lemma equivalenceOfIsEquivalence_hom :
    η.equivalenceOfIsEquivalence.hom = η := (rfl)

/-- The inverse component is the chosen quasi-inverse of the original component. -/
@[simp]
lemma equivalenceOfIsEquivalence_inv_app (a : B) :
    η.equivalenceOfIsEquivalence.inv.app a = (η.app a).toFunctor.inv.toCatHom := (rfl)

-- Keep the unit/counit component equations named: their dependent carriers do not have a
-- robust common simp normal form in importing modules.
/-- The forward unit component is the chosen component unit. -/
lemma equivalenceOfIsEquivalence_unit_hom_as_app (a : B) :
    η.equivalenceOfIsEquivalence.unit.hom.as.app a =
      (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.unitIso).hom := (rfl)

/-- The inverse unit component is the inverse of the chosen component unit. -/
lemma equivalenceOfIsEquivalence_unit_inv_as_app (a : B) :
    η.equivalenceOfIsEquivalence.unit.inv.as.app a =
      (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.unitIso).inv := (rfl)

/-- The forward counit component is the chosen component counit. -/
lemma equivalenceOfIsEquivalence_counit_hom_as_app (a : B) :
    η.equivalenceOfIsEquivalence.counit.hom.as.app a =
      (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.counitIso).hom := (rfl)

/-- The inverse counit component is the inverse of the chosen component counit. -/
lemma equivalenceOfIsEquivalence_counit_inv_as_app (a : B) :
    η.equivalenceOfIsEquivalence.counit.inv.as.app a =
      (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.counitIso).inv := (rfl)

/-- Mapping the inverse naturality cell by the target component gives a square compatible
with the original naturality cell and the component counits. -/
@[reassoc]
lemma map_equivalenceOfIsEquivalence_inv_naturality_hom_app_comp
    {a b : B} (f : a ⟶ b) (X : G.obj a) :
    (η.app b).toFunctor.map
        ((η.equivalenceOfIsEquivalence.inv.naturality f).hom.toNatTrans.app X) ≫
      (η.naturality f).hom.toNatTrans.app ((η.app a).toFunctor.inv.obj X) ≫
        (G.map f).toFunctor.map ((η.app a).toFunctor.asEquivalence.counit.app X) =
      (η.app b).toFunctor.asEquivalence.counit.app ((G.map f).toFunctor.obj X) :=
  η.map_inverseNaturality_hom_app_comp f X

end CategoryTheory.Pseudofunctor.StrongTrans
