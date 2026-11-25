/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Pro.Basic
public import Mathlib.CategoryTheory.Limits.Types.Filtered
import TauCeti.CategoryTheory.Presentable.Ind

/-!
# Morphisms of pro-objects

For small cofiltered diagrams `Y : I ⥤ C` and `Z : J ⥤ C`, morphisms between the presented
pro-objects are computed by the double-limit formula
`Hom(mk Y, mk Z) ≃ lim_j colim_i Hom(Y_i, Z_j)`.

The colimit half says that morphisms to a constant pro-object are determined at a stage: every
morphism `mk Y ⟶ const.obj A` factors as `π Y i ≫ const.map g`
(`TauCeti.Pro.exists_π_comp_const_map_eq`), and two stage representatives give the same
morphism exactly when they agree at a common earlier stage
(`TauCeti.Pro.π_comp_const_map_eq_iff`). Dually to `Ind`, this is finite presentability of
representable ind-objects. The limit half is the universal property of `mk Z`
(`TauCeti.Pro.mkConeIsLimit`).

The formula is stated on the chosen stage maps: a coordinate of `homEquiv Y Z f` is the class
of a stage map `g` exactly when `f ≫ π Z j = π Y i ≫ const.map g`, and precomposition and
postcomposition with the pro-morphisms induced by natural transformations become the stagewise
maps `h ↦ a.app i ≫ h ≫ b.app j`.

## Main definitions

* `TauCeti.Pro.homConstEquiv Y A`: `Hom(mk Y, const A) ≃ colim_i Hom(Y_i, A)`.
* `TauCeti.Pro.homStage Y Z`: the diagram `j ↦ (i ↦ Hom(Y_i, Z_j))` of the double-limit formula.
* `TauCeti.Pro.homEquiv Y Z`: `Hom(mk Y, mk Z) ≃ lim_j colim_i Hom(Y_i, Z_j)`.

## Main results

* `TauCeti.Pro.homEquiv_π_apply_eq_ι_iff`: the coordinates of `homEquiv` on stage
  representatives.
* `TauCeti.Pro.homEquiv_naturality`: naturality in both diagrams.

## References

* M. Kashiwara and P. Schapira, *Categories and Sheaves*, §6.1, by duality.
* P. Scholze, *Étale cohomology of diamonds*, §7, Proposition 7.10.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace TauCeti

universe v u

namespace Pro

variable {C : Type u} [Category.{v} C] {I : Type v} [SmallCategory I] {J : Type v}
  [SmallCategory J]

section Stage

variable (Y : I ⥤ C) (Z : J ⥤ C)

/-- The stages of the double-limit formula for morphisms `mk Y ⟶ mk Z`: the functor sending
`j` to the diagram `i ↦ (Y.obj i ⟶ Z.obj j)`. -/
@[expose]
def homStage : J ⥤ Iᵒᵖ ⥤ Type v :=
  Z ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj Y.op

@[simp]
theorem homStage_obj (j : J) : (homStage Y Z).obj j = Y.op ⋙ yoneda.obj (Z.obj j) := (rfl)

@[simp]
theorem homStage_map {j j' : J} (b : j ⟶ j') :
    (homStage Y Z).map b = Functor.whiskerLeft Y.op (yoneda.map (Z.map b)) := (rfl)

variable {Y Z} {Y' : I ⥤ C} {Z' : J ⥤ C}

/-- Precomposition with `a : Y' ⟶ Y` and postcomposition with `b : Z ⟶ Z'` on the stages of the
double-limit formula: `h ↦ a.app i ≫ h ≫ b.app j`. -/
def homStageMap (a : Y' ⟶ Y) (b : Z ⟶ Z') : homStage Y Z ⟶ homStage Y' Z' :=
  Functor.whiskerRight b (yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj Y.op) ≫
    Functor.whiskerLeft (Z' ⋙ yoneda) ((Functor.whiskeringLeft _ _ _).map (NatTrans.op a))

@[simp]
theorem homStageMap_app_app_apply (a : Y' ⟶ Y) (b : Z ⟶ Z') (j : J) (i : Iᵒᵖ)
    (h : Y.obj i.unop ⟶ Z.obj j) :
    ((homStageMap a b).app j).app i h = a.app i.unop ≫ h ≫ b.app j := (rfl)

end Stage

variable [IsCofiltered I] [IsCofiltered J]

attribute [local instance] IsCofiltered.isConnected

section Const

variable (Y : I ⥤ C) {A : C}

/-- A stage representative, read in the ind-category of `Cᵒᵖ` that defines `Pro C`. -/
private theorem π_comp_const_map_eq_op {i : I} (g : Y.obj i ⟶ A) :
    π Y i ≫ const.map g = (Ind.yoneda.map g.op ≫ colimit.ι (Y.op ⋙ Ind.yoneda) (op i)).op := by
  rw [π_def, const_map]
  -- Both sides are now the same composite: `op_comp` holds definitionally.
  rfl

/-- Every morphism from a presented pro-object to a constant pro-object factors through one of
its stages. -/
theorem exists_π_comp_const_map_eq (f : mk Y ⟶ const.obj A) :
    ∃ (i : I) (g : Y.obj i ⟶ A), π Y i ≫ const.map g = f := by
  -- By `const_obj` and `mk_def`, `f.unop` is a map from a representable ind-object to the
  -- filtered colimit presenting `mk Y`.
  obtain ⟨⟨i⟩, p, hp⟩ := IsFinitelyPresentable.exists_hom_of_isColimit
    (colimit.isColimit (Y.op ⋙ Ind.yoneda)) (X := Ind.yoneda.obj (op A))
    (f.unop : Ind.yoneda.obj (op A) ⟶ colimit (Y.op ⋙ Ind.yoneda))
  refine ⟨i, (Ind.yoneda.preimage p).unop, ?_⟩
  rw [π_comp_const_map_eq_op, Quiver.Hom.op_unop, Functor.map_preimage]
  exact congrArg Quiver.Hom.op hp

/-- Two stage representatives give the same morphism to a constant pro-object exactly when they
agree at a common earlier stage. -/
theorem π_comp_const_map_eq_iff {i i' : I} (g : Y.obj i ⟶ A) (g' : Y.obj i' ⟶ A) :
    π Y i ≫ const.map g = π Y i' ≫ const.map g' ↔
      ∃ (k : I) (a : k ⟶ i) (b : k ⟶ i'), Y.map a ≫ g = Y.map b ≫ g' := by
  constructor
  · intro h
    rw [π_comp_const_map_eq_op, π_comp_const_map_eq_op] at h
    obtain ⟨k, a, b, hab⟩ := IsFinitelyPresentable.exists_eq_of_isColimit
      (colimit.isColimit (Y.op ⋙ Ind.yoneda)) (Ind.yoneda.map g.op) (Ind.yoneda.map g'.op)
      (Quiver.Hom.op_inj h)
    refine ⟨k.unop, a.unop, b.unop, Quiver.Hom.op_inj (Ind.yoneda.map_injective ?_)⟩
    simpa using hab
  · rintro ⟨k, a, b, hab⟩
    rw [← π_naturality Y a, ← π_naturality Y b, Category.assoc, Category.assoc, ← const.map_comp,
      ← const.map_comp, hab]

/-- The stage representatives of morphisms from `mk Y` to `const.obj A`, as a cocone over the
diagram `i ↦ (Y.obj i ⟶ A)`. -/
private def homConstCocone : Cocone (Y.op ⋙ yoneda.obj A) where
  pt := mk Y ⟶ const.obj A
  ι :=
    { app i := TypeCat.ofHom fun g ↦ π Y i.unop ≫ const.map g
      naturality i i' a := by
        ext g
        simp }

private theorem bijective_colimitDesc_homConstCocone :
    Function.Bijective (colimit.desc _ (homConstCocone Y (A := A))) := by
  constructor
  · intro x x' h
    obtain ⟨i, g, rfl⟩ := Types.jointly_surjective' x
    obtain ⟨i', g', rfl⟩ := Types.jointly_surjective' x'
    rw [colimit.ι_desc_apply, colimit.ι_desc_apply] at h
    obtain ⟨k, a, b, hab⟩ := (π_comp_const_map_eq_iff Y g g').1 h
    exact (Types.FilteredColimit.colimit_eq_iff _).2 ⟨op k, a.op, b.op, hab⟩
  · intro f
    obtain ⟨i, g, rfl⟩ := exists_π_comp_const_map_eq Y f
    exact ⟨colimit.ι (Y.op ⋙ yoneda.obj A) (op i) g, colimit.ι_desc_apply _ _ _⟩

/-- Morphisms from a presented pro-object to a constant pro-object are the filtered colimit of
the morphisms from its stages: `Hom(mk Y, const A) ≃ colim_i Hom(Y_i, A)`. -/
def homConstEquiv (A : C) : (mk Y ⟶ const.obj A) ≃ colimit (Y.op ⋙ yoneda.obj A) :=
  (Equiv.ofBijective _ (bijective_colimitDesc_homConstCocone Y)).symm

/-- The morphism represented by a stage map `g : Y.obj i ⟶ A` is `π Y i ≫ const.map g`. -/
@[simp]
theorem homConstEquiv_symm_ι {i : I} (g : Y.obj i ⟶ A) :
    dsimp% (homConstEquiv Y A).symm (colimit.ι (Y.op ⋙ yoneda.obj A) (op i) g) =
      π Y i ≫ const.map g :=
  -- The inverse of `homConstEquiv` is `colimit.desc` of `homConstCocone`, whose legs are these
  -- composites by definition.
  colimit.ι_desc_apply (homConstCocone Y) (op i) g

/-- The class of a stage representative of a morphism to a constant pro-object. -/
@[simp]
theorem homConstEquiv_π_comp_const_map {i : I} (g : Y.obj i ⟶ A) :
    homConstEquiv Y A (π Y i ≫ const.map g) = colimit.ι (Y.op ⋙ yoneda.obj A) (op i) g := by
  rw [← Equiv.eq_symm_apply, homConstEquiv_symm_ι]

/-- Postcomposition with a constant morphism acts on stage representatives by postcomposition. -/
theorem homConstEquiv_comp_const_map {B : C} (f : mk Y ⟶ const.obj A) (h : A ⟶ B) :
    homConstEquiv Y B (f ≫ const.map h) =
      colimMap (Functor.whiskerLeft Y.op (yoneda.map h)) (homConstEquiv Y A f) := by
  obtain ⟨i, g, rfl⟩ := exists_π_comp_const_map_eq Y f
  simp [← Functor.map_comp]

/-- Precomposition with the pro-morphism induced by `a : Y' ⟶ Y` acts on stage representatives
by precomposition with the components of `a`. -/
theorem homConstEquiv_lim_map_comp {Y' : I ⥤ C} (a : Y' ⟶ Y) (f : mk Y ⟶ const.obj A) :
    homConstEquiv Y' A (lim.map a ≫ f) =
      colimMap (Functor.whiskerRight (NatTrans.op a) (yoneda.obj A)) (homConstEquiv Y A f) := by
  obtain ⟨i, g, rfl⟩ := exists_π_comp_const_map_eq Y f
  simp [← Functor.map_comp]

end Const

section Hom

variable (Y : I ⥤ C) (Z : J ⥤ C)

/-- Morphisms from `mk Y` to the constant pro-objects `const.obj (Z.obj j)`, computed
stagewise by `homConstEquiv`. -/
private def homConstNatIso : (Z ⋙ const) ⋙ coyoneda.obj (op (mk Y)) ≅ homStage Y Z ⋙ colim :=
  NatIso.ofComponents (fun j ↦ (homConstEquiv Y (Z.obj j)).toIso) (fun b ↦ by
    ext f
    exact homConstEquiv_comp_const_map Y f (Z.map b))

/-- Maps into `mk Z` are the compatible families of maps into its stages. -/
private def homLimitIso : (mk Y ⟶ mk Z) ≅ limit ((Z ⋙ const) ⋙ coyoneda.obj (op (mk Y))) :=
  (isLimitOfPreserves (coyoneda.obj (op (mk Y))) (mkConeIsLimit Z)).conePointUniqueUpToIso
    (limit.isLimit _)

@[reassoc]
private theorem homLimitIso_hom_π (j : J) :
    (homLimitIso Y Z).hom ≫ limit.π _ j = (coyoneda.obj (op (mk Y))).map (π Z j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ j

/-- The double-limit formula as an isomorphism of types. -/
private def homIso : (mk Y ⟶ mk Z) ≅ limit (homStage Y Z ⋙ colim) :=
  homLimitIso Y Z ≪≫ Limits.lim.mapIso (homConstNatIso Y Z)

private theorem homIso_hom_π (j : J) :
    (homIso Y Z).hom ≫ limit.π (homStage Y Z ⋙ colim) j =
      (coyoneda.obj (op (mk Y))).map (π Z j) ≫ (homConstNatIso Y Z).hom.app j := by
  simp only [homIso, Iso.trans_hom, Functor.mapIso_hom, Category.assoc, lim_map, limMap_π]
  exact homLimitIso_hom_π_assoc Y Z j _

/-- Morphisms of pro-objects are given by the double-limit formula
`Hom(mk Y, mk Z) ≃ lim_j colim_i Hom(Y_i, Z_j)`. -/
def homEquiv : (mk Y ⟶ mk Z) ≃ limit (homStage Y Z ⋙ colim) :=
  (homIso Y Z).toEquiv

/-- The `j`-th coordinate of `homEquiv Y Z f` is the class of `f ≫ π Z j`. -/
@[simp]
theorem homEquiv_π_apply (f : mk Y ⟶ mk Z) (j : J) :
    dsimp% limit.π (homStage Y Z ⋙ colim) j (homEquiv Y Z f) =
      homConstEquiv Y (Z.obj j) (f ≫ π Z j) :=
  ConcreteCategory.congr_hom (homIso_hom_π Y Z j) f

/-- The `j`-th coordinate of `homEquiv Y Z f` is represented by a stage map `g : Y.obj i ⟶ Z.obj j`
exactly when `g` represents `f` at the stage `j` of `mk Z`. -/
theorem homEquiv_π_apply_eq_ι_iff (f : mk Y ⟶ mk Z) {i : I} {j : J} (g : Y.obj i ⟶ Z.obj j) :
    limit.π (homStage Y Z ⋙ colim) j (homEquiv Y Z f) =
        colimit.ι (Y.op ⋙ yoneda.obj (Z.obj j)) (op i) g ↔
      f ≫ π Z j = π Y i ≫ const.map g := by
  rw [homEquiv_π_apply]
  exact (Equiv.eq_symm_apply _).symm.trans (Eq.congr_right (homConstEquiv_symm_ι Y g))

/-- The pro-morphism with given double-limit coordinates has the corresponding stage
projections. -/
@[simp]
theorem homEquiv_symm_apply_comp_π (x : limit (homStage Y Z ⋙ colim)) (j : J) :
    (homEquiv Y Z).symm x ≫ π Z j =
      (homConstEquiv Y (Z.obj j)).symm (limit.π (homStage Y Z ⋙ colim) j x) := by
  obtain ⟨f, rfl⟩ := (homEquiv Y Z).surjective x
  rw [Equiv.symm_apply_apply, homEquiv_π_apply]
  exact ((homConstEquiv Y (Z.obj j)).symm_apply_apply _).symm

end Hom

section Naturality

variable {Y Y' : I ⥤ C} {Z Z' : J ⥤ C}

/-- Under the double-limit formula, precomposition with `lim.map a` and postcomposition with
`lim.map b` become the stagewise maps `h ↦ a.app i ≫ h ≫ b.app j`. -/
theorem homEquiv_naturality (a : Y' ⟶ Y) (f : mk Y ⟶ mk Z) (b : Z ⟶ Z') :
    homEquiv Y' Z' (lim.map a ≫ f ≫ lim.map b) =
      limMap (Functor.whiskerRight (homStageMap a b) colim) (homEquiv Y Z f) := by
  refine Types.limit_ext _ _ _ fun j ↦ ?_
  -- Stagewise, `homStageMap a b` is postcomposition with `b.app j` followed by precomposition
  -- with `a`.
  have hab : colimMap ((homStageMap a b).app j) =
      colimMap (Functor.whiskerLeft Y.op (yoneda.map (b.app j))) ≫
        colimMap (Functor.whiskerRight (NatTrans.op a) (yoneda.obj (Z'.obj j))) :=
    colim.map_comp _ _
  have h := homConstEquiv_lim_map_comp Y a ((f ≫ π Z j) ≫ const.map (b.app j))
  rw [homConstEquiv_comp_const_map, ← ConcreteCategory.comp_apply, ← hab] at h
  simp only [Functor.comp_obj, colim_obj, limMap_π_apply, homEquiv_π_apply, Category.assoc,
    lim_map_π, Functor.whiskerRight_app, colim_map] at h ⊢
  exact h

end Naturality

end Pro

end TauCeti
