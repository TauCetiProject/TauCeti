/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Balanced.CharacterModule
public import TauCeti.LinearAlgebra.TensorProduct.Balanced.FinitelyGenerated

import TauCeti.Logic.Small.Opposite

/-!
# Flat modules over a possibly noncommutative ring

A left module `M` over `A` is flat if the inclusions of finitely generated
right ideals remain injective upon tensoring on the right with `M`. In fact
the same holds for every right ideal and every injective map of right modules.
The character module of `M` satisfies Baer's extension criterion exactly when
`M` is flat. This gives Lambek's characterization by injectivity of the
character module.

The reduction to finitely generated ideals parallels Mathlib's
`Module.Flat.iff_rTensor_injective` for commutative rings.

## References

* T. Y. Lam, *Lectures on Modules and Rings*, (4.12), pp. 125–126 (opposite-ring form).
* J. Lambek, *A module is flat if and only if its character module is injective*, pp. 237–241.
-/

public section

universe u v

open MulOpposite
open scoped CharacterModule

namespace TauCeti.Module

open BalancedTensorProduct

variable {A : Type u} {M : Type v} [Ring A] [AddCommGroup M] [Module A M]

variable (A M) in
/-- A left module is flat if tensoring with it preserves the inclusions of finitely
generated right ideals in the regular right module. -/
@[mk_iff]
class BalancedFlat : Prop where
  out ⦃I : Submodule Aᵐᵒᵖ A⦄ : I.FG →
    Function.Injective (map (I.subtype.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
      (fun a x ↦ I.subtype.map_smul (op a) x) (fun _ _ ↦ rfl))

/-- For a flat module, the tensor map of the inclusion of any right ideal is injective. -/
theorem BalancedFlat.injective_map_subtype [BalancedFlat A M] (I : Submodule Aᵐᵒᵖ A) :
    Function.Injective (map (I.subtype.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
      (fun a x ↦ I.subtype.map_smul (op a) x) (fun _ _ ↦ rfl)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨J, hJ, hJI, y, rfl⟩ := I.exists_fg_le_eq_balancedTensor_map_inclusion x
  let i := map (I.subtype.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
    (fun a x ↦ I.subtype.map_smul (op a) x) (fun _ _ ↦ rfl)
  let j := map (J.subtype.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
    (fun a x ↦ J.subtype.map_smul (op a) x) (fun _ _ ↦ rfl)
  let k := map ((J.inclusion hJI).restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
    (fun a x ↦ (J.inclusion hJI).map_smul (op a) x) (fun _ _ ↦ rfl)
  -- The two inclusions compose to the inclusion of `J` in the regular right module.
  have hcomp : i.comp k = j :=
    (map_comp ((J.inclusion hJI).restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
      (I.subtype.restrictScalars ℤ) LinearMap.id (fun a x ↦ (J.inclusion hJI).map_smul (op a) x)
      (fun _ _ ↦ rfl) (fun a x ↦ I.subtype.map_smul (op a) x) (fun _ _ ↦ rfl)).symm
  have hy : j y = 0 := by
    rw [← hcomp, LinearMap.comp_apply]
    exact hx
  have : y = 0 := (injective_iff_map_eq_zero _).mp (BalancedFlat.out (A := A) (M := M) hJ) _ hy
  rw [this, map_zero]

/-- A left module is flat if and only if maps from right ideals to its character module
extend over the regular right module. -/
theorem balancedFlat_iff_baer_characterModule :
    BalancedFlat A M ↔ _root_.Module.Baer Aᵐᵒᵖ (CharacterModule M) := by
  let e : A ≃ₗ[Aᵐᵒᵖ] Aᵐᵒᵖ :=
    { (opAddEquiv : A ≃+ Aᵐᵒᵖ) with map_smul' := fun _ _ ↦ rfl }
  constructor
  · intro hflat I g
    let J := Submodule.comap e.toLinearMap (I : Submodule Aᵐᵒᵖ Aᵐᵒᵖ)
    let eJ := e.ofSubmodule' (I : Submodule Aᵐᵒᵖ Aᵐᵒᵖ)
    obtain ⟨h, hh⟩ := (injective_map_id_iff_surjective_lcomp (M := M) J.subtype).mp
      (BalancedFlat.injective_map_subtype J) (g ∘ₗ eJ.toLinearMap)
    refine ⟨h ∘ₗ e.symm.toLinearMap, fun a ha ↦ ?_⟩
    simpa only [LinearMap.lcomp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      Submodule.subtype_apply, LinearEquiv.apply_symm_apply, eJ,
      LinearEquiv.ofSubmodule'_symm_apply]
      using DFunLike.congr_fun hh (eJ.symm ⟨a, ha⟩)
  · intro h
    constructor
    intro I _
    rw [injective_map_id_iff_surjective_lcomp]
    intro g
    obtain ⟨f, hf⟩ := h.extension_property I.subtype Subtype.val_injective g
    exact ⟨f, by simpa only [LinearMap.lcomp_apply'] using hf⟩

/-- Tensoring with a flat left module preserves injective maps of right modules
in arbitrary universes. -/
theorem BalancedFlat.preserves_injective_linearMap [BalancedFlat A M]
    {P Q : Type*} [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup Q] [Module Aᵐᵒᵖ Q]
    (i : P →ₗ[Aᵐᵒᵖ] Q) (hi : Function.Injective i) :
    Function.Injective (map (i.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
      (fun a p ↦ i.map_smul (op a) p) (fun _ _ ↦ rfl)) := by
  rw [injective_map_id_iff_surjective_lcomp]
  intro g
  obtain ⟨h, hh⟩ :=
    (balancedFlat_iff_baer_characterModule.mp ‹BalancedFlat A M›).extension_property i hi g
  exact ⟨h, by simpa only [LinearMap.lcomp_apply'] using hh⟩

/-- **Lambek's criterion.** A left module is flat if and only if its character module is
injective as a right module. -/
theorem balancedFlat_iff_injective_characterModule [Small.{v} A] :
    BalancedFlat A M ↔ _root_.Module.Injective Aᵐᵒᵖ (CharacterModule M) :=
  balancedFlat_iff_baer_characterModule.trans _root_.Module.Baer.iff_injective

/-- If the ring is small in the universe of the left module, flatness can be tested by
tensoring injective maps between right modules in that universe. -/
theorem balancedFlat_iff_preserves_injective_linearMap [Small.{v} A] :
    BalancedFlat A M ↔
      ∀ ⦃P Q : Type v⦄ [AddCommGroup P] [Module Aᵐᵒᵖ P] [AddCommGroup Q] [Module Aᵐᵒᵖ Q]
        (i : P →ₗ[Aᵐᵒᵖ] Q), Function.Injective i →
          Function.Injective (map (i.restrictScalars ℤ) (LinearMap.id : M →ₗ[ℤ] M)
            (fun a p ↦ i.map_smul (op a) p) (fun _ _ ↦ rfl)) := by
  refine ⟨fun _ _ _ _ _ _ _ i hi ↦ BalancedFlat.preserves_injective_linearMap i hi, fun h ↦ ?_⟩
  apply balancedFlat_iff_injective_characterModule.mpr
  constructor
  intro P Q _ _ _ _ i hi g
  obtain ⟨f, hf⟩ := (injective_map_id_iff_surjective_lcomp i).mp (h i hi) g
  exact ⟨f, DFunLike.congr_fun hf⟩

end TauCeti.Module
