/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal

/-!
# Discrete modules over quotient rings

For a two-sided ideal `I` of a topological ring `A`, discrete modules over `A / I`
are equivalent to discrete `A`-modules annihilated by `I`. The quotient carries its
quotient topology. No closedness or completeness assumption is needed for this
comparison: continuity descends because the quotient projection is a quotient map.

The inverse uses Mathlib's `Module.IsTorsionBySet.module`; both functors keep the
underlying abelian groups and maps. This comparison allows central-character
conditions to be presented by quotient algebras.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups* (2007), §3.2,
  for discrete modules over completed enveloping algebras and their quotients.
-/

noncomputable section

public section

universe v u

open CategoryTheory

namespace Ideal

open TauCeti

variable {A : Type u} [Ring A] [TopologicalSpace A] (I : Ideal A) [I.IsTwoSided]

/-- Discrete modules annihilated by a two-sided ideal. -/
def discreteAnnihilatedModules : ObjectProperty (ModuleCat.{v} A) :=
  discreteModules A ⊓ fun M => Module.IsTorsionBySet A M (I : Set A)

omit [I.IsTwoSided] in
/-- Membership means discrete continuity and annihilation by the ideal. -/
theorem discreteAnnihilatedModules_iff (M : ModuleCat.{v} A) :
    discreteAnnihilatedModules I M ↔
      discreteModules A M ∧ Module.IsTorsionBySet A M (I : Set A) :=
  Iff.rfl

/-- Restriction along the quotient projection detects discrete continuity. -/
theorem discreteModules_restrictScalars_quotient_iff (M : ModuleCat.{v} (A ⧸ I)) :
    discreteModules A ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M) ↔
      discreteModules (A ⧸ I) M := by
  rw [discreteModules_iff_isOpen, discreteModules_iff_isOpen]
  -- Identify the carrier of restriction of scalars with `M` before elaborating its orbit maps.
  change (∀ m x : M, IsOpen {a : A | Ideal.Quotient.mk I a • m = x}) ↔
    ∀ m x : M, IsOpen {a : A ⧸ I | a • m = x}
  exact forall_congr' fun m => forall_congr' fun x =>
    (Ideal.isQuotientMap_quotient_mk I).isOpen_preimage
      (s := {a : A ⧸ I | a • m = x})

/-- Restriction of discrete quotient modules to modules annihilated by `I`. -/
-- Exposed so the unit and counit formulas can use elements of the original carrier.
@[expose]
def discreteQuotientRestriction : (discreteModules.{v} (A ⧸ I)).FullSubcategory ⥤
    (discreteAnnihilatedModules.{v} I).FullSubcategory :=
  (discreteAnnihilatedModules I).lift
    ((discreteModules (A ⧸ I)).ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I))
    fun M => (discreteAnnihilatedModules_iff I _).mpr
      ⟨(discreteModules_restrictScalars_quotient_iff I M.obj).mpr M.property,
      fun m a => by
        exact (congrArg (fun b : A ⧸ I =>
          @SMul.smul (A ⧸ I) M.obj M.obj.isModule.toSMul b m)
          (Ideal.Quotient.eq_zero_iff_mem.mpr a.property)).trans (zero_smul _ _)⟩

/-- The quotient-module structure on the same abelian group, supplied by annihilation. -/
-- The carrier must remain available for the action and map formulas below.
@[expose]
def discreteQuotientDescentObj
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) : ModuleCat.{v} (A ⧸ I) :=
  letI := ((discreteAnnihilatedModules_iff I M.obj).mp M.property).2.module
  ModuleCat.of (A ⧸ I) M.obj

/-- The quotient action agrees with the original action on representatives. -/
@[simp]
theorem discreteQuotientDescentObj_mk_smul
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) (a : A) (m : M.obj) :
    @SMul.smul (A ⧸ I) (discreteQuotientDescentObj I M)
      (discreteQuotientDescentObj I M).isModule.toSMul (Ideal.Quotient.mk I a) m = a • m :=
  (rfl)

/-- The descended module is discrete for the quotient topology. -/
theorem discreteModules_discreteQuotientDescentObj
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    discreteModules (A ⧸ I) (discreteQuotientDescentObj I M) := by
  rw [← discreteModules_restrictScalars_quotient_iff]
  exact ((discreteAnnihilatedModules_iff I M.obj).mp M.property).1

/-- Descent of an annihilated discrete module to the quotient, retaining its carrier and maps. -/
-- Exposed for the same-carrier unit and counit formulas; the action is still characterized above.
@[expose]
def discreteQuotientDescent : (discreteAnnihilatedModules.{v} I).FullSubcategory ⥤
    (discreteModules.{v} (A ⧸ I)).FullSubcategory where
  obj M := ⟨discreteQuotientDescentObj I M, discreteModules_discreteQuotientDescentObj I M⟩
  map {M N} f := ObjectProperty.homMk (ModuleCat.ofHom
    (X := discreteQuotientDescentObj I M) (Y := discreteQuotientDescentObj I N)
    { toFun := f.hom
      map_add' := f.hom.hom.map_add
      map_smul' := fun a m => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact f.hom.hom.map_smul a m })

/-- The restriction functor is native restriction of scalars after inclusion. -/
@[simp]
theorem discreteQuotientRestriction_comp_ι :
    discreteQuotientRestriction.{v} I ⋙ (discreteAnnihilatedModules I).ι =
      (discreteModules (A ⧸ I)).ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I) := by
  rfl

/-- The underlying module of descent is the canonical quotient action. -/
@[simp]
theorem discreteQuotientDescent_obj_obj
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    ((discreteQuotientDescent I).obj M).obj = discreteQuotientDescentObj I M := by
  rfl

/-- Descent keeps the underlying abelian groups and maps. -/
@[simp]
theorem discreteQuotientDescent_comp_forget :
    discreteQuotientDescent.{v} I ⋙ (discreteModules (A ⧸ I)).ι ⋙
        forget₂ (ModuleCat (A ⧸ I)) AddCommGrpCat =
      (discreteAnnihilatedModules I).ι ⋙ forget₂ (ModuleCat A) AddCommGrpCat := by
  rfl

/-- Descent followed by restriction is naturally the identity, by identity maps. -/
def discreteQuotientDescentRestrictionIso :
    discreteQuotientDescent.{v} I ⋙ discreteQuotientRestriction I ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    { hom := ObjectProperty.homMk (ModuleCat.ofHom
        (X := ((discreteQuotientDescent I ⋙ discreteQuotientRestriction I).obj M).obj)
        (Y := M.obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl })
      inv := ObjectProperty.homMk (ModuleCat.ofHom
        (X := M.obj)
        (Y := ((discreteQuotientDescent I ⋙ discreteQuotientRestriction I).obj M).obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun _ _ => rfl }) })

/-- Restriction followed by descent is naturally the identity, by identity maps. -/
def discreteQuotientRestrictionDescentIso :
    discreteQuotientRestriction.{v} I ⋙ discreteQuotientDescent I ≅ 𝟭 _ :=
  NatIso.ofComponents (fun M =>
    { hom := ObjectProperty.homMk (ModuleCat.ofHom
        (X := ((discreteQuotientRestriction I ⋙ discreteQuotientDescent I).obj M).obj)
        (Y := M.obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun a m => by
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
            rfl })
      inv := ObjectProperty.homMk (ModuleCat.ofHom
        (X := M.obj)
        (Y := ((discreteQuotientRestriction I ⋙ discreteQuotientDescent I).obj M).obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun a m => by
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
            rfl }) })

@[simp]
theorem discreteQuotientDescentRestrictionIso_hom_app_apply
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) (m : M.obj) :
    dsimp% (((discreteQuotientDescentRestrictionIso I).hom.app M).hom.hom m) = m := by
  rfl

@[simp]
theorem discreteQuotientDescentRestrictionIso_inv_app_apply
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) (m : M.obj) :
    dsimp% (((discreteQuotientDescentRestrictionIso I).inv.app M).hom.hom m) = m := by
  rfl

@[simp]
theorem discreteQuotientRestrictionDescentIso_hom_app_apply
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) (m : M.obj) :
    dsimp% (((discreteQuotientRestrictionDescentIso I).hom.app M).hom.hom m) = m := by
  rfl

@[simp]
theorem discreteQuotientRestrictionDescentIso_inv_app_apply
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) (m : M.obj) :
    dsimp% (((discreteQuotientRestrictionDescentIso I).inv.app M).hom.hom m) = m := by
  rfl

/-- Discrete quotient modules are equivalent to discrete modules annihilated by the ideal. -/
def discreteQuotientEquivalence : (discreteModules.{v} (A ⧸ I)).FullSubcategory ≌
    (discreteAnnihilatedModules.{v} I).FullSubcategory where
  functor := discreteQuotientRestriction I
  inverse := discreteQuotientDescent I
  unitIso := (discreteQuotientRestrictionDescentIso I).symm
  counitIso := discreteQuotientDescentRestrictionIso I
  functor_unitIso_comp M := by ext; rfl

@[simp]
theorem discreteQuotientEquivalence_functor :
    (discreteQuotientEquivalence.{v} I).functor = discreteQuotientRestriction I := by
  rfl

@[simp]
theorem discreteQuotientEquivalence_inverse :
    (discreteQuotientEquivalence.{v} I).inverse = discreteQuotientDescent I := by
  rfl

@[simp]
theorem discreteQuotientEquivalence_unitIso :
    (discreteQuotientEquivalence.{v} I).unitIso =
      (discreteQuotientRestrictionDescentIso I).symm ≪≫
        eqToIso (by rw [discreteQuotientEquivalence_functor,
          discreteQuotientEquivalence_inverse]) := by
  rfl

@[simp]
theorem discreteQuotientEquivalence_counitIso :
    (discreteQuotientEquivalence.{v} I).counitIso =
      eqToIso (by rw [discreteQuotientEquivalence_functor,
        discreteQuotientEquivalence_inverse]) ≪≫ discreteQuotientDescentRestrictionIso I := by
  rfl

end Ideal
