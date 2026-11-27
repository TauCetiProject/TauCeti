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

The module-level statements, `TauCeti.isNondegenerate_iff_one_smul` and the `H`-module structure
`TauCeti.IsNondegenerate.module`, are in `TauCeti.RingTheory.Idempotented.Basic`.

## Main definitions

* `TauCeti.nondegModEquivModuleCat A H`: the equivalence `NondegMod A H ≌ ModuleCat H`.
-/

public section

universe v u₁ u₂

open CategoryTheory

namespace TauCeti

variable {A : Type u₁} {H : Type u₂}

section ModuleCat

variable [CommRing A] [Ring H] [Algebra A H]

/-- An `H`-module, viewed as a module over `A ⊕ H` through the algebra map `A ⊕ H → H`,
`(a, h) ↦ a • 1 + h`, is nondegenerate. -/
theorem isNondegenerate_restrictScalars (M : ModuleCat.{v} H) :
    IsNondegenerate A H ((ModuleCat.restrictScalars
      (Unitization.lift (NonUnitalAlgHom.id A H) : Unitization A H →+* H)).obj M) :=
  isNondegenerate_iff_one_smul.2 fun m ↦ by
    -- `1 ∈ A ⊕ H` acts through its image `1 ∈ H`, on the carrier `M` of the restricted module
    rw [ModuleCat.restrictScalars.smul_def]
    refine (congrArg (· • (show M from m)) ?_).trans (one_smul H _)
    simp

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
    -- unfold both actions; `m` is cast to the carrier the first lemma is stated on, which is
    -- `X.obj` by definition
    rw [RingHom.id_apply, moduleCatToNondegMod_obj_smul _ r
      (show ((moduleCatToNondegMod A H).obj ((nondegModToModuleCat A H).obj X)).obj from m),
      nondegModToModuleCat_obj_smul]
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
    -- unfold both actions, casting `m` as in the first lemma's right side
    rw [RingHom.id_apply, nondegModToModuleCat_obj_smul, moduleCatToNondegMod_obj_smul _ _
      (show ((moduleCatToNondegMod A H).obj M).obj from m)]
    -- the lift `A ⊕ H → H` restricts to the identity on `H`
    exact congrArg (fun x : H ↦ x • (show M from m)) (by simp)
  left_inv _ := rfl
  right_inv _ := rfl

variable (A H)

/-- **Nondegenerate modules over a unital algebra are modules**: `NondegMod A H ≌ ModuleCat H`. -/
noncomputable def nondegModEquivModuleCat : NondegMod.{v} A H ≌ ModuleCat.{v} H where
  functor := nondegModToModuleCat A H
  inverse := moduleCatToNondegMod A H
  -- Every component of the unit and counit is the identity function on carriers, so the
  -- naturality squares and the triangle identity hold by `rfl`.
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
