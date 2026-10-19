/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.InternalHom.Basic
public import TauCeti.Algebra.Category.ModuleCat.Presheaf.Stalk
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Stalk

/-!
# The stalk comparison for internal Hom

A germ of a local morphism of sheaves of modules acts on germs of sections. This gives the
canonical linear comparison from the stalk of the internal Hom to the module of linear maps
between the two stalks, naturally in both sheaves. No finiteness hypothesis is imposed on the
source, and the comparison is not asserted to be invertible.

The construction uses Mathlib's module structure on stalks and its filtered-colimit universal
property, together with the sectionwise description of internal Hom in `InternalHom.Basic`.

## Main declarations

* `SheafOfModules.ihomStalkComparison`: the comparison as a linear map over the ring stalk;
* `SheafOfModules.ihomStalkComparison_germ_apply`: evaluation on representatives in a neighborhood;
* `SheafOfModules.ihomStalkComparison_naturality` and `SheafOfModules.ihomStalkComparison_pre`:
  compatibility with morphisms in the target and source.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed Opposite TopologicalSpace

universe u

noncomputable section

namespace SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  (M N : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R))

variable (x : X)

private def ihomSectionStalkMap (U : Opens X) (hx : x ∈ U)
    (s : ((ihom M).obj N).val.obj (op U)) :
    ↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      ↑(TopCat.Presheaf.stalk N.val.presheaf x) := by
  -- Forgetting commutativity gives a different chosen scalar colimit; rebundle its additive
  -- map over the original commutative-ring stalk using the characteristic germ equation.
  let f := M.val.stalkMapOver (R := (TauCeti.SheafOfModules.ringCatSheaf R).obj)
    x U (M.ihomObjEquiv N U s).val hx
  refine { toFun := f, map_add' := map_add f, map_smul' := ?_ }
  intro r m
  obtain ⟨V, hxV, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  obtain ⟨W, hW, hxW, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m (V := V ⊓ U) ⟨hxV, hx⟩
  let m : M.val.obj (op W) := m
  let i : W ⟶ U := homOfLE (hW.trans inf_le_right)
  let j : W ⟶ V := homOfLE (hW.trans inf_le_left)
  rw [← TopCat.Presheaf.germ_res_apply R.obj j x hxW r]
  erw [← M.val.germ_smul (R := R.obj) x W hxW (R.obj.map j.op r) m]
  erw [M.val.stalkMapOver_germ x U _ hx W i hxW (R.obj.map j.op r • m),
    M.val.stalkMapOver_germ x U _ hx W i hxW m,
    ((M.ihomObjEquiv N U s).val.app (op (Over.mk i))).hom.map_smul]
  exact N.val.germ_smul (R := R.obj) x W hxW _ _

private theorem ihomSectionStalkMap_germ (U : Opens X) (hx : x ∈ U)
    (s : ((ihom M).obj N).val.obj (op U)) (V : Opens X) (i : V ⟶ U)
    (hxV : x ∈ V) (m : M.val.obj (op V)) :
    ihomSectionStalkMap M N x U hx s (TopCat.Presheaf.germ M.val.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.val.presheaf V x hxV
        ((M.ihomObjEquiv N U s).val.app (op (Over.mk i)) m) :=
  M.val.stalkMapOver_germ (R := (TauCeti.SheafOfModules.ringCatSheaf R).obj)
    x U (M.ihomObjEquiv N U s).val hx V i hxV m

private theorem ihomSectionStalkMap_add (U : Opens X) (hx : x ∈ U)
    (s t : ((ihom M).obj N).val.obj (op U)) :
    ihomSectionStalkMap M N x U hx (s + t) =
      ihomSectionStalkMap M N x U hx s + ihomSectionStalkMap M N x U hx t := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hx
  simp only [LinearMap.add_apply]
  erw [ihomSectionStalkMap_germ M N x U hx (s + t) V (homOfLE hVU) hxV m,
    ihomSectionStalkMap_germ M N x U hx s V (homOfLE hVU) hxV m,
    ihomSectionStalkMap_germ M N x U hx t V (homOfLE hVU) hxV m]
  exact (congrArg (TopCat.Presheaf.germ N.val.presheaf V x hxV)
    (M.ihomObjEquiv_add_app N U s t (homOfLE hVU) m)).trans
      ((TopCat.Presheaf.germ N.val.presheaf V x hxV).hom.map_add _ _)

private theorem ihomSectionStalkMap_res {U V : Opens X} (i : V ⟶ U)
    (hx : x ∈ V) (s : ((ihom M).obj N).val.obj (op U)) :
    ihomSectionStalkMap M N x V hx (((ihom M).obj N).val.map i.op s) =
      ihomSectionStalkMap M N x U (i.le hx) s := by
  apply LinearMap.ext
  intro m
  obtain ⟨W, hWV, hxW, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hx
  erw [ihomSectionStalkMap_germ M N x V hx _ W (homOfLE hWV) hxW m,
    ihomSectionStalkMap_germ M N x U (i.le hx) s W (homOfLE hWV ≫ i) hxW m]
  exact congrArg (TopCat.Presheaf.germ N.val.presheaf W x hxW)
    (M.ihomObjEquiv_map_app N s i (homOfLE hWV) m)

private theorem ihomSectionStalkMap_smul (U : Opens X) (hx : x ∈ U)
    (r : R.obj.obj (op U)) (s : ((ihom M).obj N).val.obj (op U)) :
    ihomSectionStalkMap M N x U hx (r • s) =
      TopCat.Presheaf.germ R.obj U x hx r • ihomSectionStalkMap M N x U hx s := by
  apply LinearMap.ext
  intro m
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hx
  simp only [LinearMap.smul_apply]
  erw [ihomSectionStalkMap_germ M N x U hx (r • s) V (homOfLE hVU) hxV m,
    ihomSectionStalkMap_germ M N x U hx s V (homOfLE hVU) hxV m]
  refine (congrArg (TopCat.Presheaf.germ N.val.presheaf V x hxV)
    (M.ihomObjEquiv_smul_app N U r s (homOfLE hVU) m)).trans ?_
  exact (N.val.germ_smul (R := R.obj) x V hxV _ _).trans
    (congrArg (fun a ↦ a • TopCat.Presheaf.germ N.val.presheaf V x hxV
      ((M.ihomObjEquiv N U s).val.app (op (Over.mk (homOfLE hVU))) m))
      (TopCat.Presheaf.germ_res_apply R.obj (homOfLE hVU) x hxV r))

/-- The canonical linear comparison from the stalk of the internal Hom to linear maps between
stalks, obtained by letting germs of local morphisms act on germs of sections. -/
def ihomStalkComparison :
    ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x)) := by
  -- Pin the coefficient presheaf so section scalar inference avoids repeatedly unfolding
  -- the sheaf forgetful construction and its chosen stalk module structures.
  let P : PresheafOfModulesOfCommRing.{u} R.obj := ((ihom M).obj N).val
  let f : ∀ (U : Opens X), x ∈ U → P.obj (op U) →+
      (↑(TopCat.Presheaf.stalk M.val.presheaf x) →ₗ[↑(TopCat.Presheaf.stalk R.obj x)]
        ↑(TopCat.Presheaf.stalk N.val.presheaf x)) := fun U hx ↦
    AddMonoidHom.mk' (ihomSectionStalkMap M N x U hx)
    (ihomSectionStalkMap_add M N x U hx)
  let l := TopCat.Presheaf.stalkLiftAddHom P.presheaf x f
    (ihomSectionStalkMap_res M N x)
  refine { toFun := l, map_add' := map_add l, map_smul' := ?_ }
  intro r s
  obtain ⟨U, hxU, r, rfl⟩ := TopCat.Presheaf.exists_germ_eq R.obj r
  obtain ⟨V, hVU, hxV, s, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq P.presheaf s hxU
  let s : P.obj (op V) := s
  rw [← TopCat.Presheaf.germ_res_apply R.obj (homOfLE hVU) x hxV r]
  erw [← P.germ_smul (R := R.obj)
    x V hxV (R.obj.map (homOfLE hVU).op r) s]
  erw [TopCat.Presheaf.stalkLiftAddHom_germ P.presheaf x f
    (ihomSectionStalkMap_res M N x) V hxV (R.obj.map (homOfLE hVU).op r •
      s),
    TopCat.Presheaf.stalkLiftAddHom_germ P.presheaf x f
      (ihomSectionStalkMap_res M N x) V hxV s]
  exact ihomSectionStalkMap_smul M N x V hxV (R.obj.map (homOfLE hVU).op r) s

/-- On a germ of a local internal-Hom section, the comparison has the underlying additive
map of the stalk map of its local morphism. The two linear maps use respectively the original
commutative-ring stalk and the stalk after forgetting commutativity as their scalar rings. -/
theorem ihomStalkComparison_germ (U : Opens X) (hx : x ∈ U)
    (s : ((ihom M).obj N).val.obj (op U)) :
    (M.ihomStalkComparison N x
        (TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf U x hx s)).toAddHom =
      (M.val.stalkMapOver (R := (TauCeti.SheafOfModules.ringCatSheaf R).obj)
        x U (M.ihomObjEquiv N U s).val hx).toAddHom := by
  apply AddHom.ext
  intro m
  exact congrArg (fun φ ↦ φ m)
    (TopCat.Presheaf.stalkLiftAddHom_germ ((ihom M).obj N).val.presheaf x
      (fun U hx ↦ AddMonoidHom.mk' (ihomSectionStalkMap M N x U hx)
        (ihomSectionStalkMap_add M N x U hx))
      (ihomSectionStalkMap_res M N x) U hx s)

/-- The comparison evaluates two germs by applying the local morphism to a representative
section in its domain. -/
theorem ihomStalkComparison_germ_apply (U : Opens X) (hx : x ∈ U)
    (s : ((ihom M).obj N).val.obj (op U)) (V : Opens X) (i : V ⟶ U)
    (hxV : x ∈ V) (m : M.val.obj (op V)) :
    M.ihomStalkComparison N x (TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf U x hx s)
        (TopCat.Presheaf.germ M.val.presheaf V x hxV m) =
      TopCat.Presheaf.germ N.val.presheaf V x hxV
        ((M.ihomObjEquiv N U s).val.app (op (Over.mk i)) m) := by
  exact (congrArg (fun f : _ →ₙ+ _ ↦
    f (TopCat.Presheaf.germ M.val.presheaf V x hxV m))
      (ihomStalkComparison_germ M N x U hx s)).trans
        (M.val.stalkMapOver_germ (R := (TauCeti.SheafOfModules.ringCatSheaf R).obj)
          x U (M.ihomObjEquiv N U s).val hx V i hxV m)

/-- The stalk comparison is covariant in the target: a morphism of target sheaves acts by
postcomposition with its stalk map. -/
theorem ihomStalkComparison_naturality
    {N' : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)} (α : N ⟶ N')
    (s : ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf x))
    (m : ↑(TopCat.Presheaf.stalk M.val.presheaf x)) :
    M.ihomStalkComparison N' x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf _).map ((ihom M).map α).val) s) m =
      (TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
        ((PresheafOfModules.toPresheaf _).map α.val) (M.ihomStalkComparison N x s m) := by
  obtain ⟨U, hx, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((ihom M).obj N).val.presheaf s
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M.val.presheaf m hx
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply,
    ihomStalkComparison_germ_apply M N' x U hx
      (((ihom M).map α).val.app (op U) s) V (homOfLE hVU) hxV m,
    ihomStalkComparison_germ_apply M N x U hx s V (homOfLE hVU) hxV m,
    TopCat.Presheaf.stalkFunctor_map_germ_apply]
  -- Restricting a morphism of sheaves retains its component on the underlying open.
  exact congrArg (fun φ : M.over U ⟶ N'.over U ↦
    TopCat.Presheaf.germ N'.val.presheaf V x hxV (φ.val.app (op (Over.mk (homOfLE hVU))) m))
      (M.ihomObjEquiv_ihom_map_app N α U s)

/-- The stalk comparison is contravariant in the source: a morphism of source sheaves acts by
precomposition with its stalk map. -/
theorem ihomStalkComparison_pre
    {M' : SheafOfModules.{u} (TauCeti.SheafOfModules.ringCatSheaf R)} (β : M' ⟶ M)
    (s : ↑(TopCat.Presheaf.stalk ((ihom M).obj N).val.presheaf x))
    (m : ↑(TopCat.Presheaf.stalk M'.val.presheaf x)) :
    M'.ihomStalkComparison N x
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf _).map ((pre β).app N).val) s) m =
      M.ihomStalkComparison N x s
        ((TopCat.Presheaf.stalkFunctor AddCommGrpCat x).map
          ((PresheafOfModules.toPresheaf _).map β.val) m) := by
  obtain ⟨U, hx, s, rfl⟩ :=
    TopCat.Presheaf.exists_germ_eq ((ihom M).obj N).val.presheaf s
  obtain ⟨V, hVU, hxV, m, rfl⟩ :=
    TopCat.Presheaf.exists_le_germ_eq M'.val.presheaf m hx
  have hs := TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx
    ((PresheafOfModules.toPresheaf _).map ((pre β).app N).val) s
  have hm := TopCat.Presheaf.stalkFunctor_map_germ_apply V x hxV
    ((PresheafOfModules.toPresheaf _).map β.val) m
  have hl := congrArg (fun t ↦ M'.ihomStalkComparison N x t
    (TopCat.Presheaf.germ M'.val.presheaf V x hxV m)) hs
  have he := M'.ihomStalkComparison_germ_apply N x U hx
    (((pre β).app N).val.app (op U) s) V (homOfLE hVU) hxV m
  -- The source restriction has the same component on this representative open.
  have hn := congrArg (fun φ : M'.over U ⟶ N.over U ↦
    TopCat.Presheaf.germ N.val.presheaf V x hxV (φ.val.app (op (Over.mk (homOfLE hVU))) m))
      (M.ihomObjEquiv_pre_app_app N β U s)
  have hr := M.ihomStalkComparison_germ_apply N x U hx s V (homOfLE hVU) hxV
    (β.val.app (op V) m)
  have ht := congrArg (M.ihomStalkComparison N x
    (TopCat.Presheaf.germ ((ihom M).obj N).val.presheaf U x hx s)) hm
  exact hl.trans (he.trans (hn.trans (hr.symm.trans ht.symm)))

end SheafOfModules
