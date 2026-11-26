/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Idempotented.NondegMod
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Nondegenerate modules over a unital algebra

Let `H` be a unital algebra over a commutative ring `A`. A module `M` over the unitization `A ⊕ H`
is nondegenerate exactly when `1 ∈ H` acts as the identity, and then the action of `H ⊆ A ⊕ H`
makes `M` an `H`-module. Conversely an `H`-module is a module over `A ⊕ H` through the algebra map
`A ⊕ H → H`, `(a, h) ↦ a • 1 + h`, and it is nondegenerate. These constructions are inverse
equivalences `NondegMod A H ≌ ModuleCat H` (`TauCeti.nondegModEquivModuleCat`); for `H = A` this
is `NondegMod A A ≌ ModuleCat A`.

## Main definitions

* `TauCeti.IsNondegenerate.module`: the `H`-module structure of a nondegenerate module.
* `TauCeti.nondegModEquivModuleCat A H`: the equivalence `NondegMod A H ≌ ModuleCat H`.

## Main results

* `TauCeti.isNondegenerate_iff_one_smul`: over a unital `H`, a module is nondegenerate exactly when
  `1 ∈ H` acts as the identity.
-/

public section

universe v u₁ u₂

open CategoryTheory

namespace TauCeti

variable {A : Type u₁} {H : Type u₂} [CommRing A] [Ring H] [Algebra A H]

section Module

variable {M : Type*} [AddCommGroup M] [Module (Unitization A H) M]

/-- Over a unital algebra `H`, a module over `A ⊕ H` is nondegenerate exactly when `1 ∈ H` acts
as the identity. -/
theorem isNondegenerate_iff_one_smul :
    IsNondegenerate A H M ↔ ∀ m : M, ((1 : H) : Unitization A H) • m = m := by
  refine ⟨fun hM m ↦ ?_, fun h ↦ isNondegenerate_iff.2 fun m ↦ ⟨1, .one, h m⟩⟩
  obtain ⟨e, -, he⟩ := isNondegenerate_iff.1 hM m
  exact inr_smul_eq_of_mul_eq he (one_mul e)

/-- In a nondegenerate module over the unitization of a unital algebra, `1 ∈ H` acts as the
identity. -/
theorem IsNondegenerate.one_smul (hM : IsNondegenerate A H M) (m : M) :
    ((1 : H) : Unitization A H) • m = m :=
  isNondegenerate_iff_one_smul.1 hM m

/-- In a nondegenerate module over the unitization of a unital algebra, `a ∈ A` acts as
`a • 1 ∈ H`. -/
theorem IsNondegenerate.inl_smul (hM : IsNondegenerate A H M) (a : A) (m : M) :
    (Unitization.inl a : Unitization A H) • m = ((algebraMap A H a : H) : Unitization A H) • m := by
  rw [inl_smul_eq_inr_smul (hM.one_smul m), Algebra.algebraMap_eq_smul_one]

/-- The `H`-module structure of a nondegenerate module over the unitization `A ⊕ H` of a unital
algebra `H`: `h` acts as `h ∈ A ⊕ H`. -/
abbrev IsNondegenerate.module (hM : IsNondegenerate A H M) : Module H M where
  smul h m := (h : Unitization A H) • m
  one_smul := hM.one_smul
  mul_smul h h' m := by
    change ((h * h' : H) : Unitization A H) • m = _
    rw [Unitization.inr_mul, mul_smul]
    rfl
  smul_zero h := smul_zero (h : Unitization A H)
  smul_add h := smul_add (h : Unitization A H)
  add_smul h h' m := by
    change ((h + h' : H) : Unitization A H) • m = _
    rw [Unitization.inr_add, add_smul]
    rfl
  zero_smul m := by
    change ((0 : H) : Unitization A H) • m = 0
    rw [Unitization.inr_zero, zero_smul]

end Module

variable (A H)

/-- The algebra map `A ⊕ H → H`, `(a, h) ↦ a • 1 + h`, from the unitization of a unital algebra. -/
noncomputable abbrev unitizationToSelf : Unitization A H →+* H :=
  (Unitization.lift (NonUnitalAlgHom.id A H)).toRingHom

theorem unitizationToSelf_inr (h : H) : unitizationToSelf A H h = h := by
  simp [unitizationToSelf]

/-- An `H`-module, viewed as a module over `A ⊕ H` through `A ⊕ H → H`, is nondegenerate. -/
theorem isNondegenerate_restrictScalars (M : ModuleCat.{v} H) :
    IsNondegenerate A H ((ModuleCat.restrictScalars (unitizationToSelf A H)).obj M) :=
  isNondegenerate_iff_one_smul.2 fun m ↦ by
    change unitizationToSelf A H ((1 : H) : Unitization A H) • (m : M) = m
    rw [unitizationToSelf_inr, one_smul]

/-- The functor from `H`-modules to nondegenerate modules over `A ⊕ H`, restricting scalars along
`A ⊕ H → H`. -/
noncomputable def moduleCatToNondegMod : ModuleCat.{v} H ⥤ NondegMod.{v} A H :=
  (nondegenerateModuleProperty.{v} A H).lift (ModuleCat.restrictScalars (unitizationToSelf A H))
    fun M ↦ (nondegenerateModuleProperty_iff _).2 (isNondegenerate_restrictScalars A H M)

/-- The functor from nondegenerate modules over `A ⊕ H` to `H`-modules, through the action of
`H ⊆ A ⊕ H`. -/
noncomputable def nondegModToModuleCat : NondegMod.{v} A H ⥤ ModuleCat.{v} H where
  obj X := @ModuleCat.of H _ X.obj _ ((nondegenerateModuleProperty_iff _).1 X.property).module
  map {X Y} f :=
    letI := ((nondegenerateModuleProperty_iff _).1 X.property).module
    letI := ((nondegenerateModuleProperty_iff _).1 Y.property).module
    ModuleCat.ofHom
      { toFun := f.hom.hom
        map_add' := map_add f.hom.hom
        map_smul' := fun h m ↦ f.hom.hom.map_smul (h : Unitization A H) m }

variable {A H} in
/-- A nondegenerate module is its own image under `nondegModToModuleCat` followed by
`moduleCatToNondegMod`: `a • 1 + h` acts as `(a, h)`. -/
private noncomputable def unitLinearEquiv (X : NondegMod.{v} A H) :
    X.obj ≃ₗ[Unitization A H]
      ((moduleCatToNondegMod A H).obj ((nondegModToModuleCat A H).obj X)).obj where
  toFun := id
  invFun := id
  map_add' _ _ := rfl
  map_smul' r m := by
    have hX := (nondegenerateModuleProperty_iff _).1 X.property
    change r • m = ((unitizationToSelf A H r : H) : Unitization A H) • m
    induction r using Unitization.ind with
    | inl_add_inr a h =>
      rw [add_smul, hX.inl_smul, ← add_smul, ← Unitization.inr_add]
      simp [unitizationToSelf]
  left_inv _ := rfl
  right_inv _ := rfl

variable {A H} in
/-- An `H`-module is its own image under `moduleCatToNondegMod` followed by
`nondegModToModuleCat`. -/
private noncomputable def counitLinearEquiv (M : ModuleCat.{v} H) :
    (nondegModToModuleCat A H).obj ((moduleCatToNondegMod A H).obj M) ≃ₗ[H] M where
  toFun := id
  invFun := id
  map_add' _ _ := rfl
  map_smul' h m := by
    change (h : Unitization A H) • (show (ModuleCat.restrictScalars (unitizationToSelf A H)).obj M
      from m) = (h • (show M from m) : M)
    rw [ModuleCat.restrictScalars.smul_def, unitizationToSelf_inr]
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Nondegenerate modules over a unital algebra are modules**: `NondegMod A H ≌ ModuleCat H`. -/
noncomputable def nondegModEquivModuleCat : NondegMod.{v} A H ≌ ModuleCat.{v} H where
  functor := nondegModToModuleCat A H
  inverse := moduleCatToNondegMod A H
  unitIso := NatIso.ofComponents (fun X ↦
    (nondegenerateModuleProperty.{v} A H).fullyFaithfulι.preimageIso
      (unitLinearEquiv X).toModuleIso) fun _ ↦ rfl
  counitIso := NatIso.ofComponents (fun M ↦ (counitLinearEquiv M).toModuleIso) fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

end TauCeti
