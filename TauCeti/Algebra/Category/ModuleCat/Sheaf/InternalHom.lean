/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Presheaf.InternalHom
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Hom
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Closed
import TauCeti.CategoryTheory.Monoidal.Closed.Basic
import TauCeti.CategoryTheory.Monoidal.Closed.Functor

/-!
# Sections of the internal Hom of sheaves of modules

Let `R` be a sheaf of commutative rings on a small site, and let `M` and `N` be sheaves of
`R`-modules. The internal Hom `𝓗om(M, N)` of sheaves of modules is defined as the sheafification
of the internal Hom of the underlying presheaves of modules
(`SheafOfModules.ihom_obj`). This file shows that the sheafification does nothing: the presheaf
internal Hom of two sheaves is already a sheaf. Its sections over `U` are the morphisms
`M|_U ⟶ N|_U` of restrictions to the slice over `U`
(`TauCeti.PresheafOfModules.ihomObjEquiv`), and since `N` is a sheaf, compatible local morphisms
of restrictions glue uniquely: under this identification the presheaf internal Hom has the sheaf
of local linear morphisms `SheafOfModules.linearHom M N` as its underlying presheaf of sets.

Consequently the sections of the sheaf internal Hom are computed exactly as for sheaves of
morphisms: a section of `𝓗om(M, N)` over `U` is a morphism of sheaves of modules
`M.over U ⟶ N.over U`, compatibly with restriction and naturally in both `M` and `N`. This is
the sectionwise description on which the comparison of `𝓗om(M, N)` with restriction to a slice
rests, for sources `M` that are only locally free.

## Main declarations

* `SheafOfModules.isSheaf_ihom_val`: the presheaf internal Hom from any presheaf of modules into
  a sheaf of modules is a sheaf;
* `SheafOfModules.ihomCompForgetIso`: the underlying presheaf of the sheaf internal Hom is the
  presheaf internal Hom, naturally in the source and target;
* `SheafOfModules.ihomObjEquiv`: the sections of `𝓗om(M, N)` over `U` are the morphisms
  `M.over U ⟶ N.over U`; `SheafOfModules.ihomObjEquiv_apply` reads the morphism attached to a
  section off the presheaf internal Hom, and the equivalence is compatible with restriction by
  `SheafOfModules.ihomObjEquiv_map_app`, natural in the target by
  `SheafOfModules.ihomObjEquiv_ihom_map_app`, and natural in the source by
  `SheafOfModules.ihomObjEquiv_pre_app_app`.

## References

* [R. Hartshorne, *Algebraic Geometry*][hartshorne1977], Chapter II, Exercise 1.15 (the sheaf
  `𝓗om(M, N)` and its sections).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}} (M N : _root_.SheafOfModules.{u} (ringCatSheaf R))

/-- The sections over `U` of the internal Hom of the underlying presheaves of two sheaves of
modules are the morphisms of their restrictions to the slice over `U`. -/
private def ihomValObjEquiv (U : C) :
    ((ihom M.val).obj N.val).obj (op U) ≃ (M.over U ⟶ N.over U) :=
  (PresheafOfModules.ihomObjEquiv (R := R.obj) U M.val N.val).trans
    ((fullyFaithfulForget _).homEquiv (X := M.over U) (Y := N.over U)).symm

/-- The morphism of restrictions attached by `ihomValObjEquiv` to a section of the presheaf
internal Hom is the one given by `TauCeti.PresheafOfModules.ihomObjEquiv`. -/
private theorem ihomValObjEquiv_val (U : C) (s : ((ihom M.val).obj N.val).obj (op U)) :
    (ihomValObjEquiv M N U s).val = PresheafOfModules.ihomObjEquiv (R := R.obj) U M.val N.val s :=
  (fullyFaithfulForget _).map_preimage (X := M.over U) (Y := N.over U) _

/-- Componentwise form of `ihomValObjEquiv_val`. -/
private theorem ihomValObjEquiv_val_app (U : C) (s : ((ihom M.val).obj N.val).obj (op U))
    {W : C} (h : W ⟶ U) (m : M.val.obj (op W)) :
    ((ihomValObjEquiv M N U s).val.app (op (Over.mk h))) m =
      (PresheafOfModules.ihomObjEquiv (R := R.obj) U M.val N.val s).app' (op (Over.mk h)) m :=
  congrArg (fun φ ↦ (φ.app (op (Over.mk h))) m) (ihomValObjEquiv_val M N U s)

/-- Restricting a section of the presheaf internal Hom agrees, under `ihomValObjEquiv`, with
restricting the corresponding local linear morphism. -/
private theorem ihomValObjEquiv_map {U V : C} (g : V ⟶ U)
    (s : ((ihom M.val).obj N.val).obj (op U)) :
    ihomValObjEquiv M N V (((ihom M.val).obj N.val).map g.op s) =
      linearHomObjEquiv M N V ((linearHom M N).obj.map g.op
        ((linearHomObjEquiv M N U).symm (ihomValObjEquiv M N U s))) := by
  ext ⟨W⟩ m
  -- An object of the slice over `V` is `Over.mk h` for its structure morphism `h`.
  obtain ⟨W, ⟨⟨⟩⟩, h⟩ := W
  refine (ihomValObjEquiv_val_app M N V _ h m).trans ?_
  refine (PresheafOfModules.ihomObjEquiv_map_app (R := R.obj) U M.val N.val s g h m).trans ?_
  refine Eq.symm ((linearHomObjEquiv_map_app M N g h _ m).trans ?_)
  rw [Equiv.apply_symm_apply]
  exact ihomValObjEquiv_val_app M N U s (h ≫ g) m

/-- The underlying presheaf of sets of the presheaf internal Hom of two sheaves of modules is the
sheaf of local linear morphisms between them. -/
private def ihomValPresheafIsoLinearHom :
    ((ihom M.val).obj N.val).presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{u} ≅
      (linearHom M N).obj :=
  NatIso.ofComponents
    (fun U ↦ ((ihomValObjEquiv M N U.unop).trans (linearHomObjEquiv M N U.unop).symm).toIso)
    (fun {_ V} g ↦ by
      ext s
      apply (linearHomObjEquiv M N V.unop).injective
      exact (Equiv.apply_symm_apply _ _).trans (ihomValObjEquiv_map M N g.unop s))

/-- The internal Hom of the underlying presheaves of two sheaves of modules is a sheaf: its
underlying presheaf of sets is the sheaf of local linear morphisms. -/
private theorem isSheaf_ihom_val_of_sheaf_source :
    Presheaf.IsSheaf J ((ihom M.val).obj N.val).presheaf :=
  (Presheaf.isSheaf_iff_isSheaf_forget J _ (CategoryTheory.forget AddCommGrpCat.{u})).2
    ((Presheaf.isSheaf_of_iso_iff (ihomValPresheafIsoLinearHom M N)).2 (linearHom M N).property)

variable [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The presheaf internal Hom into a sheaf of modules is a sheaf. No sheaf condition is needed
on the source presheaf. -/
theorem _root_.SheafOfModules.isSheaf_ihom_val
    (M : PresheafOfModules.{u} (ringCatSheaf R).obj)
    (N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    Presheaf.IsSheaf J ((ihom M).obj N.val).presheaf := by
  let L := PresheafOfModules.sheafification (R := ringCatSheaf R)
    (J := J) (𝟙 (ringCatSheaf R).obj)
  let adj := PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
    (J := J) (𝟙 (ringCatSheaf R).obj)
  have hpre : IsIso ((pre (adj.unit.app M)).app N.val) := by
    have h := ((Monoidal.Reflective.isIso_tfae adj).out 4 2).mp (by
      intro d d'
      infer_instance)
    exact h ⟨N.val, N.isSheaf⟩ M
  let e : ((ihom (L.obj M).val).obj N.val).presheaf ≅
      ((ihom M).obj N.val).presheaf :=
    (PresheafOfModules.toPresheaf _).mapIso
      (@asIso _ _ _ _ ((pre (adj.unit.app M)).app N.val) hpre)
  exact (Presheaf.isSheaf_of_iso_iff e).1
    (isSheaf_ihom_val_of_sheaf_source (L.obj M) N)

private def restrictScalarsIdApp (P : PresheafOfModules.{u} (ringCatSheaf R).obj) :
    (PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)).obj P ≅ P where
  hom :=
    { app := fun X ↦
        (ModuleCat.restrictScalarsId ((ringCatSheaf R).obj.obj X)).hom.app (P.obj X)
      naturality := fun {X Y} f ↦ by
        ext x
        rfl }
  inv :=
    { app := fun X ↦
        (ModuleCat.restrictScalarsId ((ringCatSheaf R).obj.obj X)).inv.app (P.obj X)
      naturality := fun {X Y} f ↦ by
        ext x
        rfl }
  hom_inv_id := by
    apply PresheafOfModules.hom_ext
    intro X
    exact (ModuleCat.restrictScalarsId ((ringCatSheaf R).obj.obj X)).hom_inv_id_app (P.obj X)
  inv_hom_id := by
    apply PresheafOfModules.hom_ext
    intro X
    exact (ModuleCat.restrictScalarsId ((ringCatSheaf R).obj.obj X)).inv_hom_id_app (P.obj X)

private def forgetRestrictScalarsIdIso :
    forget (ringCatSheaf R) ⋙ PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj) ≅
      forget (ringCatSheaf R) :=
  NatIso.ofComponents (fun P ↦ restrictScalarsIdApp P.val) (fun f ↦ by
    apply PresheafOfModules.hom_ext
    intro X
    exact (ModuleCat.restrictScalarsId ((ringCatSheaf R).obj.obj X)).hom.naturality
      (f.val.app X))

private def ihomForgetRestrictScalarsIdIso (M N : _root_.SheafOfModules.{u}
    (ringCatSheaf R)) :
    (ihom ((forget (ringCatSheaf R) ⋙
      PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)).obj M)).obj
      ((forget (ringCatSheaf R) ⋙
        PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)).obj N) ≅
        (ihom ((forget (ringCatSheaf R)).obj M)).obj
          ((forget (ringCatSheaf R)).obj N) :=
  (ihom ((forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)).obj M)).mapIso
      (forgetRestrictScalarsIdIso.app N) ≪≫
    @asIso _ _ _ _ ((pre (forgetRestrictScalarsIdIso.inv.app M)).app
      ((forget (ringCatSheaf R)).obj N))
      ((NatTrans.isIso_iff_isIso_app (pre (forgetRestrictScalarsIdIso.inv.app M))).1
        (MonoidalClosed.pre_isIso (forgetRestrictScalarsIdIso.app M).symm)
          ((forget (ringCatSheaf R)).obj N))

private def ihomCompForgetIsoApp (M N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    ((ihom M).obj N).val ≅ (ihom M.val).obj N.val := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
    (J := J) (𝟙 (ringCatSheaf R).obj)
  exact (forgetRestrictScalarsIdIso.app ((ihom M).obj N)).symm ≪≫
    (Monoidal.Reflective.ihomComparisonUnitIso adj M).symm.app N ≪≫
      ihomForgetRestrictScalarsIdIso M N

private theorem ihomCompForgetIsoApp_naturality (M : _root_.SheafOfModules.{u}
    (ringCatSheaf R)) {N N' : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : N ⟶ N') :
    (ihomCompForgetIsoApp M N).hom ≫ (ihom M.val).map f.val =
      ((ihom M).map f).val ≫ (ihomCompForgetIsoApp M N').hom := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
    (J := J) (𝟙 (ringCatSheaf R).obj)
  let iC := forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)
  let _ : iC.LaxMonoidal := adj.rightAdjointLaxMonoidal
  let r := forgetRestrictScalarsIdIso (R := R)
  let e := Monoidal.Reflective.ihomComparisonUnitIso adj M
  change r.inv.app ((ihom M).obj N) ≫ e.inv.app N ≫
      (ihom (iC.obj M)).map (r.hom.app N) ≫
        (pre (r.inv.app M)).app ((forget (ringCatSheaf R)).obj N) ≫
          (ihom ((forget (ringCatSheaf R)).obj M)).map
            ((forget (ringCatSheaf R)).map f) =
    (forget (ringCatSheaf R)).map ((ihom M).map f) ≫
      r.inv.app ((ihom M).obj N') ≫ e.inv.app N' ≫
        (ihom (iC.obj M)).map (r.hom.app N') ≫
          (pre (r.inv.app M)).app ((forget (ringCatSheaf R)).obj N')
  rw [r.inv.naturality_assoc]
  slice_rhs 2 3 =>
    change (ihom M ⋙ iC).map f ≫ e.inv.app N'
    rw [e.inv.naturality]
  simp only [Category.assoc]
  slice_lhs 4 5 => rw [pre_comm_ihom_map]
  slice_lhs 3 4 => rw [← Functor.map_comp]
  slice_rhs 3 4 =>
    change (ihom (iC.obj M)).map (iC.map f) ≫
      (ihom (iC.obj M)).map (r.hom.app N')
    rw [← Functor.map_comp]
  rw [r.hom.naturality f]

/-- The underlying presheaf of the internal Hom of sheaves of modules is the internal Hom of the
underlying presheaves: the sheafification defining the former is an isomorphism, since the latter
is already a sheaf (`SheafOfModules.isSheaf_ihom_val`). -/
def _root_.SheafOfModules.ihomCompForgetIso :
    ihom M ⋙ forget (ringCatSheaf R) ≅ forget (ringCatSheaf R) ⋙ ihom M.val :=
  NatIso.ofComponents (ihomCompForgetIsoApp M)
    (fun f ↦ (ihomCompForgetIsoApp_naturality M f).symm)

/-- The comparison between sheaf and presheaf internal Homs is natural in the source. -/
theorem _root_.SheafOfModules.ihomCompForgetIso_pre_app
    {M' : _root_.SheafOfModules.{u} (ringCatSheaf R)} (f : M' ⟶ M) :
    ((pre f).app N).val ≫ (ihomCompForgetIso M').hom.app N =
      (ihomCompForgetIso M).hom.app N ≫ (pre f.val).app N.val := by
  let adj := PresheafOfModules.sheafificationAdjunction (R := ringCatSheaf R)
    (J := J) (𝟙 (ringCatSheaf R).obj)
  let iC := forget (ringCatSheaf R) ⋙
    PresheafOfModules.restrictScalars (𝟙 (ringCatSheaf R).obj)
  let _ : iC.LaxMonoidal := adj.rightAdjointLaxMonoidal
  have hnat := congrArg (fun S ↦ S.natTrans.app N)
    (Functor.ihomComparison_whiskerLeft (F := iC) f)
  dsimp only [TwoSquare.whiskerBottom, TwoSquare.whiskerTop,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at hnat
  have hM := Monoidal.Reflective.ihomComparison_app_eq_ihomComparisonUnitIso_inv adj M N
  have hM' := Monoidal.Reflective.ihomComparison_app_eq_ihomComparisonUnitIso_inv adj M' N
  rw [hM, hM'] at hnat
  dsimp only [iC] at hnat
  let r := forgetRestrictScalarsIdIso (R := R)
  let e := Monoidal.Reflective.ihomComparisonUnitIso adj M
  let e' := Monoidal.Reflective.ihomComparisonUnitIso adj M'
  dsimp only [ihomCompForgetIso, NatIso.ofComponents]
  change (forget (ringCatSheaf R)).map ((pre f).app N) ≫
      r.inv.app ((ihom M').obj N) ≫ e'.inv.app N ≫
      (ihom (iC.obj M')).map (r.hom.app N) ≫
        (pre (r.inv.app M')).app ((forget (ringCatSheaf R)).obj N) =
    r.inv.app ((ihom M).obj N) ≫ e.inv.app N ≫
      (ihom (iC.obj M)).map (r.hom.app N) ≫
        (pre (r.inv.app M)).app ((forget (ringCatSheaf R)).obj N) ≫
          (pre ((forget (ringCatSheaf R)).map f)).app ((forget (ringCatSheaf R)).obj N)
  dsimp only [e, e', iC]
  rw [r.inv.naturality_assoc]
  slice_lhs 2 3 => rw [← hnat]
  simp only [Category.assoc]
  slice_lhs 3 4 => rw [pre_comm_ihom_map]
  simp only [Category.assoc]
  rw [← NatTrans.comp_app, ← pre_map, ← NatTrans.comp_app, ← pre_map,
    r.inv.naturality f]

/-- The sections over `U` of the internal Hom `𝓗om(M, N)` of sheaves of modules are the morphisms
`M.over U ⟶ N.over U` of restrictions to the slice over `U`. -/
def _root_.SheafOfModules.ihomObjEquiv (U : C) :
    ((ihom M).obj N).val.obj (op U) ≃ (M.over U ⟶ N.over U) :=
  ((PresheafOfModules.evaluation _ (op U)).mapIso
    ((ihomCompForgetIso M).app N)).toLinearEquiv.toEquiv.trans (ihomValObjEquiv M N U)

/-- The morphism of restrictions attached to a section of `𝓗om(M, N)` is the one attached to its
image in the presheaf internal Hom (`TauCeti.PresheafOfModules.ihomObjEquiv`). -/
theorem _root_.SheafOfModules.ihomObjEquiv_apply (U : C) (s : ((ihom M).obj N).val.obj (op U)) :
    M.ihomObjEquiv N U s =
      ⟨PresheafOfModules.ihomObjEquiv (R := R.obj) U M.val N.val
        (((ihomCompForgetIso M).hom.app N).app (op U) s)⟩ :=
  (Equiv.trans_apply _ _ _).trans (Hom.ext ((ihomValObjEquiv_val M N U _).trans
    (congrArg (PresheafOfModules.ihomObjEquiv (R := R.obj) U M.val N.val)
      (Iso.toLinearEquiv_apply
        ((PresheafOfModules.evaluation _ (op U)).mapIso ((ihomCompForgetIso M).app N)) s))))

/-- Restricting a section of `𝓗om(M, N)` along `g : V ⟶ U` restricts the corresponding morphism
of restrictions to the slice over `V`.

This is not a simp lemma: `SheafOfModules.ihom_obj` rewrites the internal Hom in its left-hand
side. -/
theorem _root_.SheafOfModules.ihomObjEquiv_map_app {U : C} (s : ((ihom M).obj N).val.obj (op U))
    {V : C} (g : V ⟶ U) {W : C} (h : W ⟶ V) (m : M.val.obj (op W)) :
    ((M.ihomObjEquiv N V (((ihom M).obj N).val.map g.op s)).val.app (op (Over.mk h))) m =
      ((M.ihomObjEquiv N U s).val.app (op (Over.mk (h ≫ g)))) m := by
  refine Eq.trans ?_ (PresheafOfModules.ihomObjEquiv_map_app (R := R.obj) U M.val N.val
    (((ihomCompForgetIso M).hom.app N).app (op U) s) g h m)
  -- The comparison with the presheaf internal Hom commutes with restriction.
  have hnat : ((ihomCompForgetIso M).hom.app N).app (op V) (((ihom M).obj N).val.map g.op s) =
      ((ihom M.val).obj N.val).map g.op (((ihomCompForgetIso M).hom.app N).app (op U) s) :=
    PresheafOfModules.naturality_apply _ g.op s
  exact congrArg (fun x ↦ (PresheafOfModules.ihomObjEquiv (R := R.obj) V M.val N.val x).app'
    (op (Over.mk h)) m) hnat

/-- The sections equivalence is natural in the target: applying `𝓗om(M, α)` to a section
corresponds to postcomposing the morphism of restrictions with the restriction of `α`. -/
theorem _root_.SheafOfModules.ihomObjEquiv_ihom_map_app {N' : _root_.SheafOfModules.{u}
    (ringCatSheaf R)} (α : N ⟶ N') (U : C) (s : ((ihom M).obj N).val.obj (op U)) :
    M.ihomObjEquiv N' U (((ihom M).map α).val.app (op U) s) =
      M.ihomObjEquiv N U s ≫ α.over U := by
  -- The comparison with the presheaf internal Hom is natural in the target.
  have hnat : ((ihomCompForgetIso M).hom.app N').app (op U) (((ihom M).map α).val.app (op U) s) =
      ((ihom M.val).map α.val).app (op U) (((ihomCompForgetIso M).hom.app N).app (op U) s) :=
    congrArg (fun f ↦ f.app (op U) s) ((ihomCompForgetIso M).hom.naturality α)
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, hnat]
  exact congrArg Hom.mk (PresheafOfModules.ihomObjEquiv_ihom_map_app (R := R.obj) U M.val N.val
    α.val _)

/-- The sections equivalence is natural in the source: applying `Hom(β, N)` to a section
corresponds to precomposing the morphism of restrictions with the restriction of `β`. -/
theorem _root_.SheafOfModules.ihomObjEquiv_pre_app_app
    {M' : _root_.SheafOfModules.{u} (ringCatSheaf R)} (β : M' ⟶ M) (U : C)
    (s : ((ihom M).obj N).val.obj (op U)) :
    M'.ihomObjEquiv N U (((pre β).app N).val.app (op U) s) =
      β.over U ≫ M.ihomObjEquiv N U s := by
  have hnat : ((ihomCompForgetIso M').hom.app N).app (op U)
      (((pre β).app N).val.app (op U) s) =
      ((pre β.val).app N.val).app (op U)
        (((ihomCompForgetIso M).hom.app N).app (op U) s) :=
    congrArg (fun f ↦ f.app (op U) s) (ihomCompForgetIso_pre_app M N β)
  rw [ihomObjEquiv_apply, ihomObjEquiv_apply, hnat]
  apply Hom.ext
  exact PresheafOfModules.ihomObjEquiv_pre_app_app (R := R.obj) U M.val N.val β.val _

end SheafOfModules

end

end TauCeti
