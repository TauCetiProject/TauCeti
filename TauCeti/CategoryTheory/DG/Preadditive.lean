/-
Copyright (c) 2026 Wentao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.CategoryTheory.DG.Functor
public import Mathlib.Algebra.Module.TransferInstance

/-!
# Additive structure on the closed category of a DG category

The canonical equivalence between closed morphisms and degree-zero cocycles transports the
additive group and base-ring module structures to the existing underlying category. Composition
is bilinear by the DG composition laws. Taking closed components and passing to their homotopy
classes preserve these operations, so the canonical functor to `H⁰` is additive and linear.
DG functors also induce additive linear functors between the closed categories.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory

namespace TauCeti

universe v u u'

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

-- The homotopy category retains the original object carrier.
attribute [local implicit_reducible] DGHomotopyCategory.of DGHomotopyCategory.underlying

/-- Closed morphisms form an additive group by the canonical equivalence with cocycles. -/
noncomputable instance instAddCommGroupDGClosedHom
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    AddCommGroup (X ⟶ Y) :=
  (dgClosedHomEquiv R X Y).addCommGroup

/-- The canonical cocycle equivalence is additive for the transported group structure. -/
noncomputable def dgClosedHomAddEquiv
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    (X ⟶ Y) ≃+ dgCycles R (ForgetEnrichment.to _ X) (ForgetEnrichment.to _ Y) :=
  (dgClosedHomEquiv R X Y).addEquiv

/-- Closed morphisms are a base-ring module by transport through their cocycle equivalence. -/
noncomputable instance instModuleDGClosedHom
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    Module R (X ⟶ Y) :=
  (dgClosedHomAddEquiv R X Y).module R

/-- The additive cocycle equivalence takes a morphism to its closed component. -/
@[simp]
theorem dgClosedHomAddEquiv_apply_coe
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    (dgClosedHomAddEquiv R X Y f).1 = dgClosedHom R f := by
  simp only [dgClosedHomAddEquiv, Equiv.addEquiv_apply, dgClosedHomEquiv_apply_coe]

/-- Taking the closed component preserves zero. -/
@[simp]
theorem dgClosedHom_zero
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    dgClosedHom R (0 : X ⟶ Y) = 0 := by
  simpa only [dgClosedHomAddEquiv_apply_coe, Submodule.coe_zero] using
    congrArg Subtype.val (map_zero (dgClosedHomAddEquiv R X Y))

/-- Taking the closed component preserves addition. -/
@[simp]
theorem dgClosedHom_add
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f g : X ⟶ Y) :
    dgClosedHom R (f + g) = dgClosedHom R f + dgClosedHom R g := by
  simpa only [dgClosedHomAddEquiv_apply_coe, Submodule.coe_add] using
    congrArg Subtype.val (map_add (dgClosedHomAddEquiv R X Y) f g)

/-- Taking the closed component preserves scalar multiplication. -/
@[simp]
theorem dgClosedHom_smul
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (r : R) (f : X ⟶ Y) :
    dgClosedHom R (r • f) = r • dgClosedHom R f := by
  simpa only [AddEquiv.linearEquiv_apply, dgClosedHomAddEquiv_apply_coe,
    Submodule.coe_smul] using
    congrArg Subtype.val ((dgClosedHomAddEquiv R X Y).linearEquiv R |>.map_smul r f)

/-- The closed category is preadditive by bilinearity of degree-zero DG composition. -/
noncomputable instance instPreadditiveDGClosedCategory :
    Preadditive (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) where
  homGroup X Y := inferInstance
  add_comp X Y Z f g k := by
    apply dgClosedHom_injective R
    simp only [dgClosedHom_comp, dgClosedHom_add, add_dgCompZero]
  comp_add X Y Z f g k := by
    apply dgClosedHom_injective R
    simp only [dgClosedHom_comp, dgClosedHom_add, dgCompZero_add]

/-- The closed category is linear over the base ring. -/
noncomputable instance instLinearDGClosedCategory :
    Linear R (ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) where
  homModule X Y := inferInstance
  smul_comp X Y Z r f g := by
    apply dgClosedHom_injective R
    simp only [dgClosedHom_comp, dgClosedHom_smul, smul_dgCompZero]
  comp_smul X Y Z f r g := by
    apply dgClosedHom_injective R
    simp only [dgClosedHom_comp, dgClosedHom_smul, dgCompZero_smul]

noncomputable instance : (dgClosedToHomotopy (C := C) R).Additive where
  map_add {X Y f g} := by
    simp only [dgClosedToHomotopy_map, dgClosedHom_add]
    exact DGHomotopyCategory.homOf_add R (dgClosedHom R f) (dgClosedHom R g)
      (dgClosedHom_mem_dgCycles R f) (dgClosedHom_mem_dgCycles R g)

noncomputable instance : (dgClosedToHomotopy (C := C) R).Linear R where
  map_smul {X Y} f r := by
    simp only [dgClosedToHomotopy_map, dgClosedHom_smul]
    exact DGHomotopyCategory.homOf_smul R r (dgClosedHom R f)
      (dgClosedHom_mem_dgCycles R f)

variable {D : Type u'} [DGCategory R D]
  (F : EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) C D)

noncomputable instance : F.forget.Additive where
  map_add {X Y f g} := by
    apply dgClosedHom_injective R
    simp only [EnrichedFunctor.forget_map, F.dgClosedHom_forget_map, dgClosedHom_add, map_add]

noncomputable instance : F.forget.Linear R where
  map_smul {X Y} f r := by
    apply dgClosedHom_injective R
    simp only [EnrichedFunctor.forget_map, F.dgClosedHom_forget_map, dgClosedHom_smul, map_smul]

end TauCeti
