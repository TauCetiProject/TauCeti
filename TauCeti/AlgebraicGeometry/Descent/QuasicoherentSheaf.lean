/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.CategoryTheory.Bicategory.Adjunction.Adj
public import Mathlib.CategoryTheory.Bicategory.Functor.Cat.ObjectProperty
public import TauCeti.AlgebraicGeometry.Modules.Quasicoherent.Basic
public import TauCeti.AlgebraicGeometry.Stack.Basic

/-!
# The pseudofunctor of quasi-coherent modules

Descent theory for schemes is phrased in terms of `Cat`-valued pseudofunctors on
`LocallyDiscrete Scheme.{u}ᵒᵖ`: Mathlib's `Pseudofunctor.IsPrestack` and `Pseudofunctor.IsStack`
express that morphisms and objects descend along the coverings of a Grothendieck topology on
schemes, such as `Scheme.fpqcTopology`. This file packages the categories of quasi-coherent
modules as such a pseudofunctor, so that fpqc descent of quasi-coherent modules can be stated
as `Descent.qcohPseudofunctor.IsStack Scheme.fpqcTopology`.

The pseudofunctor `T ↦ T.Modules` with pullback of modules, together with its coherence
isomorphisms, is the left-adjoint part of Mathlib's `Scheme.Modules.pseudofunctor` (which also
records pushforward). Quasi-coherence is stable under pullback, so it is a property of objects
closed under the functoriality in the sense of Mathlib's `Pseudofunctor.ObjectProperty`, and the
quasi-coherent modules form the corresponding full sub-pseudofunctor. Its value at `T` is
`QuasicoherentSheaf T`, its value on a morphism is `QuasicoherentSheaf.pullback`, and its
coherence isomorphisms are those of pullback of modules, so they agree with
`QuasicoherentSheaf.pullbackId` and `QuasicoherentSheaf.pullbackComp`.

## Main declarations

* `TauCeti.AlgebraicGeometry.Descent.modulesPseudofunctor`: `T ↦ T.Modules` with pullback.
* `TauCeti.AlgebraicGeometry.Descent.isQuasicoherent`: quasi-coherence, as a property of objects
  of `modulesPseudofunctor` closed under pullback and isomorphisms.
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor`: `T ↦ QuasicoherentSheaf T` with pullback.
* `TauCeti.AlgebraicGeometry.Descent.qcohPseudofunctor_not_isGroupoid`: on a nonempty scheme the
  category of quasi-coherent modules is not a groupoid (the zero endomorphism of the structure
  sheaf is not invertible), so `qcohPseudofunctor` is not a pseudofunctor to groupoids.

## References

* The Stacks Project, Lemma 17.10.4 (01BG): pullback of modules is a pseudofunctor.
* The Stacks Project, Section 35.5 (023T): descent of quasi-coherent modules.
-/

public section

open CategoryTheory Limits Opposite Bicategory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

namespace Descent

/-- The pseudofunctor sending a scheme `T` to the category `T.Modules` of `𝒪_T`-modules and a
morphism to pullback of modules. It is the left-adjoint part of Mathlib's
`Scheme.Modules.pseudofunctor`. -/
-- Exposed so that the categories `modulesPseudofunctor.obj T` unfold to `T.Modules` for
-- consumers, as the objects and morphisms of descent data live in these categories.
@[expose] noncomputable def modulesPseudofunctor : SchPseudofunctor.{u} :=
  Scheme.Modules.pseudofunctor.comp Adj.forget₁

@[simp]
lemma modulesPseudofunctor_obj (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    modulesPseudofunctor.obj T = Cat.of T.as.unop.Modules :=
  (rfl)

@[simp]
lemma modulesPseudofunctor_map_toFunctor {T T' : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : T ⟶ T') :
    (modulesPseudofunctor.map f).toFunctor = Scheme.Modules.pullback f.as.unop :=
  (rfl)

/-- The unit isomorphisms of `modulesPseudofunctor` are those of pullback of modules. -/
@[simp]
lemma modulesPseudofunctor_mapId_hom_toNatTrans (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (modulesPseudofunctor.mapId T).hom.toNatTrans = (Scheme.Modules.pullbackId T.as.unop).hom := by
  ext M
  -- The coherence isomorphisms of `Adj.forget₁` are identities, which `simp` cannot remove
  -- because their source and target are only definitionally those of `Adj.forget₁.map₂Iso _`.
  exact Category.comp_id _

@[simp]
lemma modulesPseudofunctor_mapId_inv_toNatTrans (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    (modulesPseudofunctor.mapId T).inv.toNatTrans = (Scheme.Modules.pullbackId T.as.unop).inv := by
  ext M
  exact Category.id_comp _

/-- The composition isomorphisms of `modulesPseudofunctor` are those of pullback of modules. -/
@[simp]
lemma modulesPseudofunctor_mapComp_hom_toNatTrans {T T' T'' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    (modulesPseudofunctor.mapComp f g).hom.toNatTrans =
      (Scheme.Modules.pullbackComp g.as.unop f.as.unop).inv := by
  ext M
  exact Category.comp_id _

@[simp]
lemma modulesPseudofunctor_mapComp_inv_toNatTrans {T T' T'' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') :
    (modulesPseudofunctor.mapComp f g).inv.toNatTrans =
      (Scheme.Modules.pullbackComp g.as.unop f.as.unop).hom := by
  ext M
  exact Category.id_comp _

/-- Quasi-coherence of modules, as a property of the objects of `modulesPseudofunctor`. -/
-- Exposed so that `isQuasicoherent.prop T M` unfolds to `M.IsQuasicoherent` for consumers.
@[expose] def isQuasicoherent : modulesPseudofunctor.{u}.ObjectProperty where
  prop T := SheafOfModules.isQuasicoherent T.as.unop.ringCatSheaf

@[simp]
lemma isQuasicoherent_prop_iff (T : LocallyDiscrete Scheme.{u}ᵒᵖ) (M : T.as.unop.Modules) :
    isQuasicoherent.prop T M ↔ M.IsQuasicoherent :=
  Iff.rfl

/-- Quasi-coherence is stable under pullback. -/
instance : isQuasicoherent.{u}.IsClosedUnderMapObj where
  map_obj {_ _} M hM f := by
    have : M.IsQuasicoherent := (isQuasicoherent_prop_iff _ M).1 hM
    exact Scheme.Modules.isQuasicoherent_pullback f.as.unop M

instance : isQuasicoherent.{u}.IsClosedUnderIsomorphisms where
  isClosedUnderIsomorphisms T :=
    inferInstanceAs
      (SheafOfModules.isQuasicoherent T.as.unop.ringCatSheaf).IsClosedUnderIsomorphisms

/-- The pseudofunctor sending a scheme `T` to the category `QuasicoherentSheaf T` of
quasi-coherent `𝒪_T`-modules and a morphism to pullback of quasi-coherent modules
(`QuasicoherentSheaf.pullback`, see `qcohPseudofunctor_map_toFunctor`). It is the full
sub-pseudofunctor of `modulesPseudofunctor` on the quasi-coherent modules; Mathlib's
`Pseudofunctor.ObjectProperty.ι isQuasicoherent` is the inclusion. -/
-- Exposed so that the categories `qcohPseudofunctor.obj T` unfold to `QuasicoherentSheaf T` for
-- consumers, as the objects and morphisms of descent data live in these categories.
@[expose] noncomputable def qcohPseudofunctor : SchPseudofunctor.{u} :=
  isQuasicoherent.fullsubcategory

@[simp]
lemma qcohPseudofunctor_obj (T : LocallyDiscrete Scheme.{u}ᵒᵖ) :
    qcohPseudofunctor.obj T = Cat.of (QuasicoherentSheaf T.as.unop) :=
  (rfl)

/-- The underlying module of the pullback of a quasi-coherent module along `f` is its pullback
as a module. -/
@[simp]
lemma qcohPseudofunctor_map_toFunctor_obj_obj {T T' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') (E : QuasicoherentSheaf T.as.unop) :
    ((qcohPseudofunctor.map f).toFunctor.obj E).obj =
      (Scheme.Modules.pullback f.as.unop).obj E.obj :=
  (rfl)

@[simp]
lemma qcohPseudofunctor_map_toFunctor_map_hom {T T' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') {E F : QuasicoherentSheaf T.as.unop} (φ : E ⟶ F) :
    ((qcohPseudofunctor.map f).toFunctor.map φ).hom =
      (Scheme.Modules.pullback f.as.unop).map φ.hom :=
  (rfl)

/-- The functors of `qcohPseudofunctor` are the pullback functors of quasi-coherent modules. -/
lemma qcohPseudofunctor_map_toFunctor {T T' : LocallyDiscrete Scheme.{u}ᵒᵖ} (f : T ⟶ T') :
    (qcohPseudofunctor.map f).toFunctor = QuasicoherentSheaf.pullback f.as.unop :=
  (QuasicoherentSheaf.pullback_def f.as.unop).symm

/-- The unit isomorphisms of `qcohPseudofunctor` are those of pullback of modules. -/
@[simp]
lemma qcohPseudofunctor_mapId_hom_toNatTrans_app_hom (T : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (E : QuasicoherentSheaf T.as.unop) :
    ((qcohPseudofunctor.mapId T).hom.toNatTrans.app E).hom =
      (Scheme.Modules.pullbackId T.as.unop).hom.app E.obj :=
  NatTrans.congr_app (modulesPseudofunctor_mapId_hom_toNatTrans T) E.obj

@[simp]
lemma qcohPseudofunctor_mapId_inv_toNatTrans_app_hom (T : LocallyDiscrete Scheme.{u}ᵒᵖ)
    (E : QuasicoherentSheaf T.as.unop) :
    ((qcohPseudofunctor.mapId T).inv.toNatTrans.app E).hom =
      (Scheme.Modules.pullbackId T.as.unop).inv.app E.obj :=
  NatTrans.congr_app (modulesPseudofunctor_mapId_inv_toNatTrans T) E.obj

/-- The composition isomorphisms of `qcohPseudofunctor` are those of pullback of modules. -/
@[simp]
lemma qcohPseudofunctor_mapComp_hom_toNatTrans_app_hom {T T' T'' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') (E : QuasicoherentSheaf T.as.unop) :
    ((qcohPseudofunctor.mapComp f g).hom.toNatTrans.app E).hom =
      (Scheme.Modules.pullbackComp g.as.unop f.as.unop).inv.app E.obj :=
  NatTrans.congr_app (modulesPseudofunctor_mapComp_hom_toNatTrans f g) E.obj

@[simp]
lemma qcohPseudofunctor_mapComp_inv_toNatTrans_app_hom {T T' T'' : LocallyDiscrete Scheme.{u}ᵒᵖ}
    (f : T ⟶ T') (g : T' ⟶ T'') (E : QuasicoherentSheaf T.as.unop) :
    ((qcohPseudofunctor.mapComp f g).inv.toNatTrans.app E).hom =
      (Scheme.Modules.pullbackComp g.as.unop f.as.unop).hom.app E.obj :=
  NatTrans.congr_app (modulesPseudofunctor_mapComp_inv_toNatTrans f g) E.obj

/-- On a nonempty scheme the quasi-coherent modules do not form a groupoid: the zero
endomorphism of the structure sheaf is not an isomorphism, since `Γ(T, ⊤)` is a nonzero ring.
So `qcohPseudofunctor` is not a pseudofunctor to groupoids, and its descent is not that of a
stack in groupoids. (On the empty scheme every module is zero, and the category is a groupoid.) -/
theorem qcohPseudofunctor_not_isGroupoid (T : Scheme.{u}) [Nonempty T] :
    ¬ IsGroupoid (qcohPseudofunctor.obj ⟨op T⟩) := by
  intro h
  let O : QuasicoherentSheaf T := ⟨SheafOfModules.unit T.ringCatSheaf, inferInstance⟩
  have h₀ : IsIso (ObjectProperty.homMk (P := SheafOfModules.isQuasicoherent T.ringCatSheaf)
      (0 : O.obj ⟶ O.obj)) := IsGroupoid.all_isIso (C := qcohPseudofunctor.obj ⟨op T⟩) _
  have h₁ : IsIso (0 : O.obj ⟶ O.obj) := by
    simpa only [ObjectProperty.ι_map, ObjectProperty.homMk_hom] using
      (ObjectProperty.ι (SheafOfModules.isQuasicoherent T.ringCatSheaf)).map_isIso
        (ObjectProperty.homMk (0 : O.obj ⟶ O.obj))
  -- If `0 : 𝒪_T ⟶ 𝒪_T` is invertible, then `𝟙 = 0`, so `1 = 0` in the ring `Γ(T, ⊤)`.
  have h₂ := congr($((isIsoZeroSelfEquiv O.obj) h₁).val.app (op ⊤) (1 : Γ(T, ⊤)))
  have : Nonempty (⊤ : T.Opens) := ⟨⟨Classical.arbitrary T, trivial⟩⟩
  -- The zero morphism of sheaves of modules is the zero morphism of the underlying presheaves.
  have h₃ : (0 : O.obj ⟶ O.obj).val = 0 := rfl
  simp only [SheafOfModules.id_val, h₃, PresheafOfModules.zero_app] at h₂
  exact one_ne_zero (α := Γ(T, ⊤)) h₂

end Descent

namespace QuasicoherentSheaf

open Descent

/-- `QuasicoherentSheaf.pullbackId` is the unit isomorphism of `qcohPseudofunctor`, up to the
identification `pullback_obj_obj` of the underlying modules. -/
theorem pullbackId_hom_app_hom_eq_qcohPseudofunctor (X : Scheme.{u}) (E : QuasicoherentSheaf X) :
    ((pullbackId X).hom.app E).hom =
      eqToHom (pullback_obj_obj (𝟙 X) E) ≫
        ((qcohPseudofunctor.mapId ⟨op X⟩).hom.toNatTrans.app E).hom := by
  rw [pullbackId_hom_app_hom, qcohPseudofunctor_mapId_hom_toNatTrans_app_hom]

theorem pullbackId_inv_app_hom_eq_qcohPseudofunctor (X : Scheme.{u}) (E : QuasicoherentSheaf X) :
    ((pullbackId X).inv.app E).hom =
      ((qcohPseudofunctor.mapId ⟨op X⟩).inv.toNatTrans.app E).hom ≫
        eqToHom (pullback_obj_obj (𝟙 X) E).symm := by
  rw [pullbackId_inv_app_hom, qcohPseudofunctor_mapId_inv_toNatTrans_app_hom]
  -- The two sides now differ only in whether the composite is formed in `X.Modules` or in
  -- `SheafOfModules X.ringCatSheaf`, which are the same category by definition.
  rfl

/-- `QuasicoherentSheaf.pullbackComp` is the composition isomorphism of `qcohPseudofunctor`, up to
the identifications `pullback_obj_obj` and `pullbackComp_obj_obj` of the underlying modules. -/
theorem pullbackComp_hom_app_hom_eq_qcohPseudofunctor {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (E : QuasicoherentSheaf Z) :
    ((pullbackComp f g).hom.app E).hom =
      eqToHom (pullbackComp_obj_obj f g E) ≫
        ((qcohPseudofunctor.mapComp g.op.toLoc f.op.toLoc).inv.toNatTrans.app E).hom ≫
        eqToHom (pullback_obj_obj (f ≫ g) E).symm := by
  rw [pullbackComp_hom_app_hom, qcohPseudofunctor_mapComp_inv_toNatTrans_app_hom]
  -- As above, the composites differ only in being formed in `X.Modules` or in sheaves of modules.
  rfl

theorem pullbackComp_inv_app_hom_eq_qcohPseudofunctor {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (g : Y ⟶ Z) (E : QuasicoherentSheaf Z) :
    ((pullbackComp f g).inv.app E).hom =
      eqToHom (pullback_obj_obj (f ≫ g) E) ≫
        ((qcohPseudofunctor.mapComp g.op.toLoc f.op.toLoc).hom.toNatTrans.app E).hom ≫
        eqToHom (pullbackComp_obj_obj f g E).symm := by
  rw [pullbackComp_inv_app_hom, qcohPseudofunctor_mapComp_hom_toNatTrans_app_hom]
  rfl

end QuasicoherentSheaf

end TauCeti.AlgebraicGeometry
