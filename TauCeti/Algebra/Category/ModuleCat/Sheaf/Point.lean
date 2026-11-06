/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import TauCeti.Algebra.Homology.DerivedCategory.Equivalence

/-!
# Module sheaves on the point site

The point site is the discrete one-object category with the bottom Grothendieck topology.
A sheaf of modules over the constant ring sheaf on this site is the same thing as a module:
evaluation at the sole object is an equivalence, inverse to the constant module sheaf functor.
The induced equivalence of unbounded derived categories acts by termwise evaluation, respects
shifts and distinguished triangles, and agrees with evaluation before localization. This is the
ordinary derived comparison; it does not assert a comparison of enhanced mapping spaces.

The coefficient ring need not be commutative. Both the module universe and the coefficient-ring
universe are independent of the (small) point site.

The abelian equivalence uses Mathlib's `SheafOfModules.evaluation` and
`PresheafOfModules.isoMk`. Its derived lift uses
`CategoryTheory.Equivalence.mapDerivedCategory`; the localization square and single-degree
comparisons are available through `CategoryTheory.Functor.mapDerivedCategoryFactors` and
`CategoryTheory.Functor.mapDerivedCategorySingleFunctor` applied to `evaluation R`.
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti.ModulePointSite

/-- The one-object site, with its trivial topology. -/
abbrev Point := Discrete PUnit

/-- The unique object of the opposite of the point site. -/
def point : Pointᵒᵖ := op ⟨PUnit.unit⟩

/-- The constant ring sheaf on the point site. -/
-- Its values must compute in the types of modules over this ring sheaf.
@[expose] def ringSheaf (R : Type u) [Ring R] :
    Sheaf (⊥ : GrothendieckTopology Point) RingCat.{u} :=
  ⟨(Functor.const Pointᵒᵖ).obj (RingCat.of R), Presheaf.isSheaf_bot _⟩

variable (R : Type u) [Ring R]

@[simp]
lemma ringSheaf_obj_obj (U : Pointᵒᵖ) : (ringSheaf R).obj.obj U = RingCat.of R := (rfl)

@[simp]
lemma ringSheaf_obj_map {U V : Pointᵒᵖ} (f : U ⟶ V) :
    (ringSheaf R).obj.map f = 𝟙 (RingCat.of R) := (rfl)

/-- A module regarded as a sheaf of modules on the point site. -/
-- Its object part must compute for the elementwise restriction and comparison formulas.
@[expose] def constant : ModuleCat.{v} R ⥤ SheafOfModules.{v} (ringSheaf R) where
  obj M :=
    { val :=
        { obj := fun _ ↦ M
          map := fun _ ↦ ModuleCat.ofHom LinearMap.id
          map_id := fun _ ↦ by ext; rfl
          map_comp := fun _ _ ↦ by ext; rfl }
      isSheaf := Presheaf.isSheaf_bot _ }
  map f := ⟨{ app := fun _ ↦ f, naturality := fun _ ↦ by ext; rfl }⟩

/-- Evaluation of a module sheaf at the sole object of the point site. -/
-- Its object part identifies the carriers appearing in the comparison formulas.
@[expose] def evaluation : SheafOfModules.{v} (ringSheaf R) ⥤ ModuleCat.{v} R :=
  SheafOfModules.evaluation (ringSheaf R) point

@[simp]
lemma constant_obj_val_obj (M : ModuleCat.{v} R) (U : Pointᵒᵖ) :
    ((constant R).obj M).val.obj U = M := (rfl)

@[simp]
lemma constant_obj_val_map_apply (M : ModuleCat.{v} R) {U V : Pointᵒᵖ}
    (f : U ⟶ V) (m : M) : ((constant R).obj M).val.map f m = m := (rfl)

@[simp]
lemma constant_map_val_app {M N : ModuleCat.{v} R} (f : M ⟶ N) (U : Pointᵒᵖ) :
    ((constant R).map f).val.app U = f := (rfl)

@[simp]
lemma evaluation_obj (M : SheafOfModules.{v} (ringSheaf R)) :
    (evaluation R).obj M = M.val.obj point := (rfl)

@[simp]
lemma evaluation_map {M N : SheafOfModules.{v} (ringSheaf R)} (f : M ⟶ N) :
    (evaluation R).map f = f.val.app point := (rfl)

instance : (constant R).Additive where
  map_add := by intros; ext; rfl

instance : (evaluation R).Additive := inferInstanceAs
  (SheafOfModules.forget (ringSheaf R) ⋙ PresheafOfModules.evaluation _ point).Additive

/-- A module sheaf on the point site is canonically the constant sheaf on its value. -/
def unitIso : 𝟭 (SheafOfModules.{v} (ringSheaf R)) ≅ evaluation R ⋙ constant R :=
  NatIso.ofComponents (fun (M : SheafOfModules.{v} (ringSheaf R)) ↦
    (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (M₁ := M.val)
      (M₂ := ((constant R).obj ((evaluation R).obj M)).val) (fun U ↦ by
        have hU : U = point := Subsingleton.elim _ _
        subst U
        exact Iso.refl _)
      (by
        intro U V f
        have hU : U = point := Subsingleton.elim _ _
        have hV : V = point := Subsingleton.elim _ _
        subst U; subst V
        have hf : f = 𝟙 point := Subsingleton.elim _ _
        subst f
        -- All objects are the point and its only restriction map is the identity.
        ext x
        simp only [PresheafOfModules.map_id]
        rfl))) (by
    intro M N f
    ext U
    have hU : U = point := Subsingleton.elim _ _
    subst U
    rfl)

/-- Evaluation of a constant module sheaf recovers the original module. -/
def counitIso : constant R ⋙ evaluation R ≅ 𝟭 (ModuleCat.{v} R) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)

/-- Evaluation identifies module sheaves on the one-object point site with modules. -/
def equivalence : SheafOfModules.{v} (ringSheaf R) ≌ ModuleCat.{v} R where
  functor := evaluation R
  inverse := constant R
  unitIso := unitIso R
  counitIso := counitIso R
  functor_unitIso_comp M := by
    rfl

/-- The unit comparison is the identity when evaluated at the point. -/
@[simp]
lemma unitIso_hom_app_val_app_point (M : SheafOfModules.{v} (ringSheaf R)) :
    ((unitIso R).hom.app M).val.app point = 𝟙 (M.val.obj point) := (rfl)

/-- The inverse unit comparison is the identity when evaluated at the point. -/
@[simp]
lemma unitIso_inv_app_val_app_point (M : SheafOfModules.{v} (ringSheaf R)) :
    ((unitIso R).inv.app M).val.app point = 𝟙 (M.val.obj point) := (rfl)

@[simp]
lemma counitIso_hom_app (M : ModuleCat.{v} R) :
    (counitIso R).hom.app M = 𝟙 M := (rfl)

@[simp]
lemma counitIso_inv_app (M : ModuleCat.{v} R) :
    (counitIso R).inv.app M = 𝟙 M := (rfl)

@[simp]
lemma equivalence_functor : (equivalence R).functor = evaluation R := (rfl)

@[simp]
lemma equivalence_inverse : (equivalence R).inverse = constant R := (rfl)

instance : (equivalence R).functor.Additive := by
  rw [equivalence_functor]
  infer_instance

instance : (evaluation R).IsEquivalence := (equivalence R).isEquivalence_functor

instance : (constant R).IsEquivalence := (equivalence R).isEquivalence_inverse

section Derived

universe w₁ w₂

variable [HasDerivedCategory.{w₁} (SheafOfModules.{v} (ringSheaf R))]
  [HasDerivedCategory.{w₂} (ModuleCat.{v} R)]

/-- The ordinary unbounded derived category of module sheaves on the point site is equivalent
to the unbounded derived category of modules, by termwise evaluation. -/
noncomputable def derivedEquivalence :
    DerivedCategory (SheafOfModules.{v} (ringSheaf R)) ≌ DerivedCategory (ModuleCat.{v} R) :=
  (equivalence.{u, v} R).mapDerivedCategory.{w₁, w₂}

@[simp]
lemma derivedEquivalence_functor :
    (derivedEquivalence.{u, v, w₁, w₂} R).functor =
      (evaluation.{u, v} R).mapDerivedCategory.{w₁, w₂} := by
  exact (equivalence.{u, v} R).mapDerivedCategory_functor.{w₁, w₂}

@[simp]
lemma derivedEquivalence_inverse :
    (derivedEquivalence.{u, v, w₁, w₂} R).inverse =
      (constant.{u, v} R).mapDerivedCategory.{w₂, w₁} := by
  exact (equivalence.{u, v} R).mapDerivedCategory_inverse.{w₁, w₂}

/-- The derived equivalence commutes with every integer shift. -/
noncomputable instance : (derivedEquivalence.{u, v, w₁, w₂} R).functor.CommShift ℤ :=
  inferInstanceAs ((equivalence.{u, v} R).mapDerivedCategory.{w₁, w₂}.functor.CommShift ℤ)

/-- The derived equivalence carries distinguished triangles to distinguished triangles. -/
instance : (derivedEquivalence.{u, v, w₁, w₂} R).functor.IsTriangulated :=
  inferInstanceAs ((equivalence.{u, v} R).mapDerivedCategory.{w₁, w₂}.functor.IsTriangulated)

/-- The inverse derived equivalence has the shift structure compatible with the adjunction. -/
noncomputable instance : (derivedEquivalence.{u, v, w₁, w₂} R).inverse.CommShift ℤ :=
  (derivedEquivalence.{u, v, w₁, w₂} R).commShiftInverse ℤ

/-- The unit and counit of the derived equivalence commute with integer shifts. -/
instance : (derivedEquivalence.{u, v, w₁, w₂} R).CommShift ℤ :=
  (derivedEquivalence.{u, v, w₁, w₂} R).commShift_of_functor ℤ

/-- Both directions of the point-site derived equivalence preserve distinguished triangles. -/
instance : (derivedEquivalence.{u, v, w₁, w₂} R).IsTriangulated :=
  Equivalence.IsTriangulated.mk' _ inferInstance

end Derived

end TauCeti.ModulePointSite
