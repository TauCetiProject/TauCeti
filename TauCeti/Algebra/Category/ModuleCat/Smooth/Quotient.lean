/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import TauCeti.Topology.Algebra.Ring.TwoSidedIdeal
public import TauCeti.Algebra.Category.ModuleCat.Twist
public import TauCeti.CategoryTheory.Monoidal.Action.LinearFunctor

/-!
# Discrete modules over quotient rings

For a two-sided ideal `I` of a topological ring `A`, discrete modules over `A / I`
are equivalent to discrete `A`-modules annihilated by `I`. The quotient carries its
quotient topology. No closedness or completeness assumption is needed for this
comparison: continuity descends because the quotient projection is a quotient map.

The inverse uses Mathlib's `Module.IsTorsionBySet.module`; both functors keep the
underlying abelian groups and maps. This comparison allows central-character
conditions to be presented by quotient algebras.

The comparison is equivariant for twisting by ring automorphisms. If a monoid `H` acts on `A`
by automorphisms preserving `I` with continuous inverses, the action descends to `A ⧸ I`
(`MonoidHom.quotientRingAut`), both sides carry twisting actions
(`Ideal.discreteQuotientMonoidalLeftAction`, `Ideal.discreteAnnihilatedMonoidalLeftAction`), and
both functors of `Ideal.discreteQuotientEquivalence` are left-linear for them
(`Ideal.leftLinearDiscreteQuotientEquivalenceFunctor`,
`Ideal.leftLinearDiscreteQuotientEquivalenceInverse`). The lineators of the restriction functor
are identity maps of the underlying modules.

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
    I.isQuotientMap_mkQ.isOpen_preimage
      (s := {a : A ⧸ I | a • m = x})

/-- Restriction of discrete quotient modules to modules annihilated by `I`. -/
-- Exposed so that the underlying modules are available in the lineator formulas below.
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

/-- Restricting the descended action recovers the original action. -/
@[simp]
theorem restrictScalars_discreteQuotientDescentObj_smul
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) (a : A) (m : M.obj) :
    @SMul.smul A ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
      (discreteQuotientDescentObj I M))
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj
        (discreteQuotientDescentObj I M)).isModule.toSMul a m = a • m :=
  (ModuleCat.restrictScalars.smul_def' (M := discreteQuotientDescentObj I M) _ a m).trans
    (discreteQuotientDescentObj_mk_smul I M a m)

/-- The descended module is discrete for the quotient topology. -/
theorem discreteModules_discreteQuotientDescentObj
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    discreteModules (A ⧸ I) (discreteQuotientDescentObj I M) := by
  rw [discreteModules_iff]
  intro m
  let : TopologicalSpace M.obj := ⊥
  let : TopologicalSpace (discreteQuotientDescentObj I M) := ⊥
  apply I.isQuotientMap_mkQ.continuous_iff.mpr
  exact (discreteModules_iff.mp
    ((discreteAnnihilatedModules_iff I M.obj).mp M.property).1 m).congr
      fun a => (discreteQuotientDescentObj_mk_smul I M a m).symm

/-- Descent of an annihilated discrete module to the quotient, retaining its carrier and maps. -/
def discreteQuotientDescent : (discreteAnnihilatedModules.{v} I).FullSubcategory ⥤
    (discreteModules.{v} (A ⧸ I)).FullSubcategory where
  obj M := ⟨discreteQuotientDescentObj I M, discreteModules_discreteQuotientDescentObj I M⟩
  map {M N} f := ObjectProperty.homMk (ModuleCat.ofHom
    (X := discreteQuotientDescentObj I M) (Y := discreteQuotientDescentObj I N)
    { toFun := f.hom
      map_add' := f.hom.hom.map_add
      map_smul' := fun a m => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (congrArg f.hom (discreteQuotientDescentObj_mk_smul I M a m)).trans
          ((f.hom.hom.map_smul a m).trans
            (discreteQuotientDescentObj_mk_smul I N a (f.hom m)).symm) })

/-- The restriction functor is native restriction of scalars after inclusion. -/
@[simp]
theorem discreteQuotientRestriction_comp_ι :
    discreteQuotientRestriction.{v} I ⋙ (discreteAnnihilatedModules I).ι =
      (discreteModules (A ⧸ I)).ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I) := by
  rfl

/-- The underlying module of restriction is native restriction of scalars. -/
@[simp]
theorem discreteQuotientRestriction_obj_obj
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) :
    ((discreteQuotientRestriction I).obj M).obj =
      (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M.obj := (rfl)

/-- The underlying module of descent is the canonical quotient action. -/
@[simp]
theorem discreteQuotientDescent_obj_obj
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    ((discreteQuotientDescent I).obj M).obj = discreteQuotientDescentObj I M := by
  rfl

/-- Restriction acts on morphisms by native restriction of scalars. -/
@[simp]
theorem discreteQuotientRestriction_map_hom
    {M N : (discreteModules.{v} (A ⧸ I)).FullSubcategory} (f : M ⟶ N) :
    ((discreteQuotientRestriction I).map f).hom =
      eqToHom (discreteQuotientRestriction_obj_obj I M) ≫
        (ModuleCat.restrictScalars (Ideal.Quotient.mk I)).map f.hom ≫
          eqToHom (discreteQuotientRestriction_obj_obj I N).symm := (rfl)

/-- Descent keeps the underlying maps after identifying its canonical quotient actions. -/
@[simp]
theorem discreteQuotientDescent_map_apply
    {M N : (discreteAnnihilatedModules.{v} I).FullSubcategory} (f : M ⟶ N) (m : M.obj) :
    (eqToHom (discreteQuotientDescent_obj_obj I N)).hom
      (((discreteQuotientDescent I).map f).hom.hom
        ((eqToHom (discreteQuotientDescent_obj_obj I M).symm).hom m)) = f.hom m := (rfl)

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
          map_smul' := fun a m => restrictScalars_discreteQuotientDescentObj_smul I M a m })
      inv := ObjectProperty.homMk (ModuleCat.ofHom
        (X := M.obj)
        (Y := ((discreteQuotientDescent I ⋙ discreteQuotientRestriction I).obj M).obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun a m =>
            (restrictScalars_discreteQuotientDescentObj_smul I M a m).symm }) })

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
            exact (discreteQuotientDescentObj_mk_smul I
              ((discreteQuotientRestriction I).obj M) a m).trans
                (ModuleCat.restrictScalars.smul_def' (M := M.obj) _ a m) })
      inv := ObjectProperty.homMk (ModuleCat.ofHom
        (X := M.obj)
        (Y := ((discreteQuotientRestriction I ⋙ discreteQuotientDescent I).obj M).obj)
        { toFun := fun m => m
          map_add' := fun _ _ => rfl
          map_smul' := fun a m => by
            obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
            exact ((discreteQuotientDescentObj_mk_smul I
              ((discreteQuotientRestriction I).obj M) a m).trans
                (ModuleCat.restrictScalars.smul_def' (M := M.obj) _ a m)).symm }) })

/-- Descent followed by restriction retains the original abelian group. -/
theorem discreteQuotientDescentRestriction_obj_forget
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    (forget₂ (ModuleCat A) AddCommGrpCat).obj
      ((discreteQuotientDescent I ⋙ discreteQuotientRestriction I).obj M).obj =
        (forget₂ (ModuleCat A) AddCommGrpCat).obj M.obj := (rfl)

/-- Restriction followed by descent retains the original abelian group. -/
theorem discreteQuotientRestrictionDescent_obj_forget
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) :
    (forget₂ (ModuleCat (A ⧸ I)) AddCommGrpCat).obj
      ((discreteQuotientRestriction I ⋙ discreteQuotientDescent I).obj M).obj =
        (forget₂ (ModuleCat (A ⧸ I)) AddCommGrpCat).obj M.obj := (rfl)

@[simp]
theorem discreteQuotientDescentRestrictionIso_hom_app_forget
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    AddCommGrpCat.ofHom
      ((discreteQuotientDescentRestrictionIso I).hom.app M).hom.hom.toAddMonoidHom =
        eqToHom (discreteQuotientDescentRestriction_obj_forget I M) := (rfl)

@[simp]
theorem discreteQuotientDescentRestrictionIso_inv_app_forget
    (M : (discreteAnnihilatedModules.{v} I).FullSubcategory) :
    AddCommGrpCat.ofHom
      ((discreteQuotientDescentRestrictionIso I).inv.app M).hom.hom.toAddMonoidHom =
        eqToHom (discreteQuotientDescentRestriction_obj_forget I M).symm := (rfl)

@[simp]
theorem discreteQuotientRestrictionDescentIso_hom_app_forget
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) :
    AddCommGrpCat.ofHom
      ((discreteQuotientRestrictionDescentIso I).hom.app M).hom.hom.toAddMonoidHom =
        eqToHom (discreteQuotientRestrictionDescent_obj_forget I M) := (rfl)

@[simp]
theorem discreteQuotientRestrictionDescentIso_inv_app_forget
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) :
    AddCommGrpCat.ofHom
      ((discreteQuotientRestrictionDescentIso I).inv.app M).hom.hom.toAddMonoidHom =
        eqToHom (discreteQuotientRestrictionDescent_obj_forget I M).symm := (rfl)

/-- Discrete quotient modules are equivalent to discrete modules annihilated by the ideal. -/
-- Exposed so that the underlying modules are available in the lineator formulas below.
@[expose]
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

section Twist

open MonoidalCategory MonoidalLeftAction Functor.LaxLeftLinear Functor.OplaxLeftLinear

variable {H : Type*} [Monoid H] (a : H →* RingAut A) (hI : ∀ h, I.map (a h : A →+* A) = I)
  (ha : ∀ h, Continuous (a h).symm)

omit [I.IsTwoSided] in
include hI ha in
/-- Twisting by automorphisms that preserve `I` and have continuous inverses preserves the discrete
modules annihilated by `I`. -/
lemma isStableUnderLeftAction_discreteAnnihilatedModules :
    letI := a.restrictScalarsMonoidalLeftAction.{v}
    (discreteAnnihilatedModules.{v} I).IsStableUnderLeftAction (Discrete H) :=
  MonoidHom.isStableUnderLeftAction_restrictScalarsMonoidalLeftAction_iff.2 fun h M hM => by
    rw [discreteAnnihilatedModules_iff] at hM ⊢
    refine ⟨discreteModules_restrictScalars (ha h) hM.1, fun m x => ?_⟩
    have hx : (x : A) ∈ I.comap (a h).symm := by
      rw [← Ideal.map_comap_of_equiv, hI h]
      exact x.2
    exact (ModuleCat.restrictScalars.smul_def _ _ m).trans (@hM.2 m ⟨_, hx⟩)

/-- The twisting action of `H` on the discrete `A`-modules annihilated by `I`: the element `h`
acts by restriction of scalars along `(a h)⁻¹`. -/
-- Exposed so that the action is definitionally the restriction of the twisting action on all
-- modules, as needed to compare it with the twisting action on other full subcategories.
@[expose, instance_reducible]
noncomputable def discreteAnnihilatedMonoidalLeftAction :
    MonoidalLeftAction (Discrete H) (discreteAnnihilatedModules.{v} I).FullSubcategory :=
  letI := a.restrictScalarsMonoidalLeftAction.{v}
  letI := I.isStableUnderLeftAction_discreteAnnihilatedModules a hI ha
  inferInstance

/-- The twisting action of `H` on the discrete `A ⧸ I`-modules, through the automorphisms
`a.quotientRingAut I hI` of `A ⧸ I` induced by `a`. -/
-- Exposed so that the action is definitionally the restriction of the twisting action on all
-- `A ⧸ I`-modules, as needed to compare it with other actions.
@[expose, instance_reducible]
noncomputable def discreteQuotientMonoidalLeftAction :
    MonoidalLeftAction (Discrete H) (discreteModules.{v} (A ⧸ I)).FullSubcategory :=
  letI := (a.quotientRingAut I hI).restrictScalarsMonoidalLeftAction.{v}
  letI := (a.quotientRingAut I hI).isStableUnderLeftAction_discreteModules.{v}
    fun h => a.continuous_quotientRingAut_symm I hI (ha h)
  inferInstance

/-- The quotient presentation `discreteQuotientEquivalence I` is equivariant: restricting the
scalars of a discrete `A ⧸ I`-module along the quotient map commutes with the twisting actions of
`H` on `A ⧸ I` and on `A`. Both twists of a module `M` are restriction of scalars along
`Ideal.Quotient.mk I ∘ (a h)⁻¹`, and the lineators are identity maps of `M`. -/
@[instance_reducible]
noncomputable def leftLinearDiscreteQuotientEquivalenceFunctor :
    letI := I.discreteQuotientMonoidalLeftAction.{v} a hI ha
    letI := I.discreteAnnihilatedMonoidalLeftAction.{v} a hI ha
    (discreteQuotientEquivalence.{v} I).functor.LeftLinear (Discrete H) :=
  letI := a.restrictScalarsMonoidalLeftAction.{v}
  letI := (a.quotientRingAut I hI).restrictScalarsMonoidalLeftAction.{v}
  letI := (a.quotientRingAut I hI).isStableUnderLeftAction_discreteModules.{v}
    fun h => a.continuous_quotientRingAut_symm I hI (ha h)
  letI := I.isStableUnderLeftAction_discreteAnnihilatedModules.{v} a hI ha
  letI := (Ideal.Quotient.mk I).leftLinearRestrictScalars.{v}
    fun h x => (a.quotientRingAut_apply_mk I hI h x).symm
  inferInstanceAs (((discreteAnnihilatedModules I).lift
    ((discreteModules (A ⧸ I)).ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I)) _).LeftLinear
      (Discrete H))

/-- The lineators of the quotient presentation are identity maps of the underlying modules. -/
lemma leftLinearDiscreteQuotientEquivalenceFunctor_μₗ_hom_apply (c : Discrete H)
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) (x : M.obj) :
    letI := I.discreteQuotientMonoidalLeftAction.{v} a hI ha
    letI := I.discreteAnnihilatedMonoidalLeftAction.{v} a hI ha
    letI := I.leftLinearDiscreteQuotientEquivalenceFunctor.{v} a hI ha
    (μₗ (discreteQuotientEquivalence.{v} I).functor c M).hom x = x :=
  -- By definition the functor is `lift` of `ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I)`,
  -- and its structure is `ObjectProperty.laxLeftLinearLift` of the composite of `ι` (identity
  -- lineators, `ObjectProperty.ι_μₗ`) with `RingHom.leftLinearRestrictScalars`. Simp cannot
  -- rewrite with `ObjectProperty.lift_μₗ_hom` through the private body of this structure, so
  -- the ring-level formula closes the goal up to that unfolding.
  (Ideal.Quotient.mk I).leftLinearRestrictScalars_μₗ_apply (a := a) (b := a.quotientRingAut I hI)
    (fun h x => (a.quotientRingAut_apply_mk I hI h x).symm) c M.obj x

/-- The inverse lineators of the quotient presentation are identity maps of the underlying
modules. -/
lemma leftLinearDiscreteQuotientEquivalenceFunctor_δₗ_hom_apply (c : Discrete H)
    (M : (discreteModules.{v} (A ⧸ I)).FullSubcategory) (x : M.obj) :
    letI := I.discreteQuotientMonoidalLeftAction.{v} a hI ha
    letI := I.discreteAnnihilatedMonoidalLeftAction.{v} a hI ha
    letI := I.leftLinearDiscreteQuotientEquivalenceFunctor.{v} a hI ha
    (δₗ (discreteQuotientEquivalence.{v} I).functor c M).hom x = x :=
  -- By definition the functor is `lift` of `ι ⋙ ModuleCat.restrictScalars (Ideal.Quotient.mk I)`,
  -- and its structure is `ObjectProperty.oplaxLeftLinearLift` of the composite of `ι` (identity
  -- lineators, `ObjectProperty.ι_δₗ`) with `RingHom.leftLinearRestrictScalars`. Simp cannot
  -- rewrite with `ObjectProperty.lift_δₗ_hom` through the private body of this structure, so
  -- the ring-level formula closes the goal up to that unfolding.
  (Ideal.Quotient.mk I).leftLinearRestrictScalars_δₗ_apply (a := a) (b := a.quotientRingAut I hI)
    (fun h x => (a.quotientRingAut_apply_mk I hI h x).symm) c M.obj x

/-- Descent of discrete modules annihilated by `I` to `A ⧸ I`-modules is equivariant for the
twisting actions, as the inverse of the equivariant equivalence `discreteQuotientEquivalence I`.
-/
@[instance_reducible]
noncomputable def leftLinearDiscreteQuotientEquivalenceInverse :
    letI := I.discreteQuotientMonoidalLeftAction.{v} a hI ha
    letI := I.discreteAnnihilatedMonoidalLeftAction.{v} a hI ha
    (discreteQuotientEquivalence.{v} I).inverse.LeftLinear (Discrete H) :=
  letI := I.discreteQuotientMonoidalLeftAction.{v} a hI ha
  letI := I.discreteAnnihilatedMonoidalLeftAction.{v} a hI ha
  letI := I.leftLinearDiscreteQuotientEquivalenceFunctor.{v} a hI ha
  (discreteQuotientEquivalence I).inverseLeftLinear (Discrete H)

end Twist

end Ideal
