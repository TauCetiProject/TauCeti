/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Bicategory.NaturalTransformation.Equivalence
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
equivalences, for an arbitrary source bicategory. Specializing `StrongTrans.equivalenceMk` to
the chosen component quasi-inverses, units, and counits gives
`StrongTrans.equivalenceOfIsEquivalence`. Its inverse naturality satisfies compatibility with
those counits; the component equations allow callers to use the equivalence without unfolding
its construction.
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

/-- A strong transformation into `Cat` is an equivalence when each component functor is an
equivalence. Its inverse has the chosen quasi-inverse component functors; its unit and counit
are their chosen unit and counit isomorphisms. -/
-- Expose the record projections so its dependent unit/counit component equations can be stated;
-- its inverse naturality satisfies compatibility with the component counits.
@[expose] noncomputable def equivalenceOfIsEquivalence :
    Bicategory.Equivalence F G :=
  η.equivalenceMk
    (fun a => (η.app a).toFunctor.inv.toCatHom)
    (fun a => Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.unitIso)
    (fun a => Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.counitIso)
    (fun a => by
      apply Iso.ext
      ext X
      simpa [leftZigzagIso, leftZigzag, bicategoricalComp] using
        (η.app a).toFunctor.asEquivalence.functor_unit_comp X)

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
      (η.app b).toFunctor.asEquivalence.counit.app ((G.map f).toFunctor.obj X) := by
  have h (c : B) : leftZigzagIso
      (Cat.Hom.isoMk (η.app c).toFunctor.asEquivalence.unitIso)
      (Cat.Hom.isoMk (η.app c).toFunctor.asEquivalence.counitIso) =
      λ_ (η.app c) ≪≫ (ρ_ (η.app c)).symm := by
    apply Iso.ext
    ext Y
    simpa [leftZigzagIso, leftZigzag, bicategoricalComp] using
      (η.app c).toFunctor.asEquivalence.functor_unit_comp Y
  have hc := congrArg (fun m => m.toNatTrans.app X)
    ((Bicategory.Equivalence.mk (η.app a) (η.app a).toFunctor.inv.toCatHom
        (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.unitIso)
        (Cat.Hom.isoMk (η.app a).toFunctor.asEquivalence.counitIso) (h a)).mateIsoEquiv_inv_counit
      (Bicategory.Equivalence.mk (η.app b) (η.app b).toFunctor.inv.toCatHom
        (Cat.Hom.isoMk (η.app b).toFunctor.asEquivalence.unitIso)
        (Cat.Hom.isoMk (η.app b).toFunctor.asEquivalence.counitIso) (h b))
      (η.naturality f))
  simpa [equivalenceOfIsEquivalence] using! hc

end CategoryTheory.Pseudofunctor.StrongTrans
