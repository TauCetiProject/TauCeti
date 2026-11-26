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

variable {A : Type u₁} {H : Type u₂}

section Module

variable [CommSemiring A] [Semiring H] [Algebra A H]
  {M : Type*} [AddCommMonoid M] [Module (Unitization A H) M]

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
algebra `H`: `h` acts as `h ∈ A ⊕ H` (`TauCeti.IsNondegenerate.smul_def`). -/
abbrev IsNondegenerate.module (hM : IsNondegenerate A H M) : Module H M where
  smul h m := (h : Unitization A H) • m
  one_smul := hM.one_smul
  -- The axioms are those of `A ⊕ H` transported along `Unitization.inr`; each term has the
  -- type of the field once `h • m` is unfolded to `(h : Unitization A H) • m`.
  mul_smul h h' m :=
    (congrArg (fun x : Unitization A H ↦ x • m) (Unitization.inr_mul A h h')).trans (mul_smul _ _ m)
  smul_zero h := smul_zero (h : Unitization A H)
  smul_add h := smul_add (h : Unitization A H)
  add_smul h h' m :=
    (congrArg (fun x : Unitization A H ↦ x • m) (Unitization.inr_add A h h')).trans (add_smul _ _ m)
  zero_smul m :=
    (congrArg (fun x : Unitization A H ↦ x • m) (Unitization.inr_zero A)).trans (zero_smul _ m)

/-- In the `H`-module structure of a nondegenerate module, `h` acts as `h ∈ A ⊕ H`. -/
theorem IsNondegenerate.smul_def (hM : IsNondegenerate A H M) (h : H) (m : M) :
    letI := hM.module
    h • m = (h : Unitization A H) • m :=
  rfl

end Module

section ModuleCat

variable [CommRing A] [Ring H] [Algebra A H]

/-- An `H`-module, viewed as a module over `A ⊕ H` through the algebra map `A ⊕ H → H`,
`(a, h) ↦ a • 1 + h`, is nondegenerate. -/
theorem isNondegenerate_restrictScalars (M : ModuleCat.{v} H) :
    IsNondegenerate A H ((ModuleCat.restrictScalars
      (Unitization.lift (NonUnitalAlgHom.id A H) : Unitization A H →+* H)).obj M) :=
  isNondegenerate_iff_one_smul.2 fun m ↦ by
    rw [ModuleCat.restrictScalars.smul_def]
    simp only [Unitization.lift_apply, RingHom.coe_coe, NonUnitalAlgHom.toAlgHom_apply,
      Unitization.fst_inr, map_zero, Unitization.snd_inr, NonUnitalAlgHom.coe_id, id_eq, zero_add]
    exact one_smul H (show M from m)

variable (A H)

/-- The functor from `H`-modules to nondegenerate modules over `A ⊕ H`, restricting scalars along
`A ⊕ H → H`, `(a, h) ↦ a • 1 + h`. -/
@[expose] noncomputable def moduleCatToNondegMod : ModuleCat.{v} H ⥤ NondegMod.{v} A H :=
  (nondegenerateModuleProperty.{v} A H).lift
    (ModuleCat.restrictScalars (Unitization.lift (NonUnitalAlgHom.id A H) : Unitization A H →+* H))
    fun M ↦ (nondegenerateModuleProperty_iff _).2 (isNondegenerate_restrictScalars M)

/-- The functor from nondegenerate modules over `A ⊕ H` to `H`-modules, through the action of
`H ⊆ A ⊕ H`. -/
@[expose] noncomputable def nondegModToModuleCat : NondegMod.{v} A H ⥤ ModuleCat.{v} H where
  obj X := @ModuleCat.of H _ X.obj _ ((nondegenerateModuleProperty_iff _).1 X.property).module
  map {X Y} f :=
    letI := ((nondegenerateModuleProperty_iff _).1 X.property).module
    letI := ((nondegenerateModuleProperty_iff _).1 Y.property).module
    ModuleCat.ofHom
      { toFun := f.hom.hom
        map_add' := map_add f.hom.hom
        map_smul' := fun h m ↦ f.hom.hom.map_smul (h : Unitization A H) m }

variable {A H}

/-- In `(moduleCatToNondegMod A H).obj M`, `(a, h) ∈ A ⊕ H` acts on `M` as `a • 1 + h ∈ H`. -/
@[simp]
theorem moduleCatToNondegMod_obj_smul (M : ModuleCat.{v} H) (r : Unitization A H)
    (m : ((moduleCatToNondegMod A H).obj M).obj) :
    r • m = (Unitization.lift (NonUnitalAlgHom.id A H) r : H) • (show M from m) :=
  rfl

/-- `moduleCatToNondegMod` sends a linear map to the same function. -/
@[simp]
theorem moduleCatToNondegMod_map_hom_apply {M N : ModuleCat.{v} H} (f : M ⟶ N)
    (m : ((moduleCatToNondegMod A H).obj M).obj) :
    ((moduleCatToNondegMod A H).map f).hom m = f (show M from m) :=
  rfl

/-- In `(nondegModToModuleCat A H).obj X`, `h ∈ H` acts on `X` as `h ∈ A ⊕ H`. -/
@[simp]
theorem nondegModToModuleCat_obj_smul (X : NondegMod.{v} A H) (h : H)
    (m : (nondegModToModuleCat A H).obj X) :
    h • m = (h : Unitization A H) • (show X.obj from m) :=
  rfl

/-- `nondegModToModuleCat` sends a homomorphism of nondegenerate modules to the same function. -/
@[simp]
theorem nondegModToModuleCat_map_apply {X Y : NondegMod.{v} A H} (f : X ⟶ Y)
    (m : (nondegModToModuleCat A H).obj X) :
    (nondegModToModuleCat A H).map f m = f.hom (show X.obj from m) :=
  rfl

/-- A nondegenerate module is its own image under `nondegModToModuleCat` followed by
`moduleCatToNondegMod`: `a • 1 + h` acts as `(a, h)`. -/
private noncomputable def unitLinearEquiv (X : NondegMod.{v} A H) :
    X.obj ≃ₗ[Unitization A H]
      ((moduleCatToNondegMod A H).obj ((nondegModToModuleCat A H).obj X)).obj where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' r m := by
    have hX := (nondegenerateModuleProperty_iff _).1 X.property
    refine Eq.trans ?_
      ((moduleCatToNondegMod_obj_smul ((nondegModToModuleCat A H).obj X) r m).trans
        (nondegModToModuleCat_obj_smul X _ m)).symm
    induction r using Unitization.ind with
    | inl_add_inr a h =>
      rw [add_smul, hX.inl_smul, ← add_smul, ← Unitization.inr_add]
      -- the lift `A ⊕ H → H` sends `(a, h)` to `a • 1 + h`
      exact congrArg (fun x : H ↦ (x : Unitization A H) • m) (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

/-- An `H`-module is its own image under `moduleCatToNondegMod` followed by
`nondegModToModuleCat`. -/
private noncomputable def counitLinearEquiv (M : ModuleCat.{v} H) :
    (nondegModToModuleCat A H).obj ((moduleCatToNondegMod A H).obj M) ≃ₗ[H] M where
  toFun m := m
  invFun m := m
  map_add' _ _ := rfl
  map_smul' h m := by
    refine ((nondegModToModuleCat_obj_smul _ h m).trans
      (moduleCatToNondegMod_obj_smul M _ m)).trans ?_
    -- the lift `A ⊕ H → H` restricts to the identity on `H`
    exact congrArg (fun x : H ↦ x • (show M from m)) (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

variable (A H)

/-- **Nondegenerate modules over a unital algebra are modules**: `NondegMod A H ≌ ModuleCat H`. -/
noncomputable def nondegModEquivModuleCat : NondegMod.{v} A H ≌ ModuleCat.{v} H where
  functor := nondegModToModuleCat A H
  inverse := moduleCatToNondegMod A H
  unitIso := NatIso.ofComponents (fun X ↦
    (nondegenerateModuleProperty.{v} A H).fullyFaithfulι.preimageIso
      (unitLinearEquiv X).toModuleIso) fun _ ↦ rfl
  counitIso := NatIso.ofComponents (fun M ↦ (counitLinearEquiv M).toModuleIso) fun _ ↦ rfl
  functor_unitIso_comp _ := rfl

variable {A H}

/-- The functor of `TauCeti.nondegModEquivModuleCat` is `TauCeti.nondegModToModuleCat`. -/
@[simp]
theorem nondegModEquivModuleCat_functor :
    (nondegModEquivModuleCat.{v} A H).functor = nondegModToModuleCat A H := by
  rfl

/-- The inverse of `TauCeti.nondegModEquivModuleCat` is `TauCeti.moduleCatToNondegMod`. -/
@[simp]
theorem nondegModEquivModuleCat_inverse :
    (nondegModEquivModuleCat.{v} A H).inverse = moduleCatToNondegMod A H := by
  rfl

end ModuleCat

end TauCeti
