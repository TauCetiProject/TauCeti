/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Limits.WeakLimits.WeakKernels
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

import Mathlib.LinearAlgebra.Span.Basic

/-!
# Weak kernels in full subcategories of `ModuleCat`

For a full subcategory `S.FullSubcategory` of `ModuleCat.{v} R` containing an object `R₀` linearly
equivalent to `R`, the range of a weak kernel `c.ι` of a morphism `φ : A ⟶ B` equals the kernel
`LinearMap.ker φ.hom.hom` (`CategoryTheory.ObjectProperty.range_ι_eq_ker_of_isWeakLimit` and
`CategoryTheory.ObjectProperty.range_weakKernel_ι_eq_ker`).

## Main results

* `CategoryTheory.ObjectProperty.range_ι_eq_ker_of_isWeakLimit`: the range of any weak kernel fork
  of `φ` in `S.FullSubcategory` is `LinearMap.ker φ.hom.hom`.
* `CategoryTheory.ObjectProperty.range_weakKernel_ι_eq_ker`: specialization to `weakKernel.ι φ`.
-/

public section

namespace CategoryTheory.ObjectProperty

open CategoryTheory.Limits

universe u v

variable {R : Type u} [Ring R] (S : ObjectProperty (ModuleCat.{v} R))

/-- For a full subcategory `S` of `ModuleCat.{v} R` containing an object `R₀` linearly equivalent to
`R`, the range of a weak kernel fork `c.ι` of `φ` is the kernel of `φ`. -/
theorem range_ι_eq_ker_of_isWeakLimit {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    {A B : S.FullSubcategory} {φ : A ⟶ B} {c : KernelFork φ} (hc : IsWeakLimit c) :
    LinearMap.range c.ι.hom.hom = LinearMap.ker φ.hom.hom := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    have hw : (c.ι ≫ φ).hom.hom y = 0 := by
      rw [KernelFork.condition, ObjectProperty.zero_hom, ModuleCat.hom_zero, LinearMap.zero_apply]
    rw [ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp, LinearMap.comp_apply] at hw
    exact hw
  · intro x hx
    let g : R₀ ⟶ A := ObjectProperty.homMk
      (ModuleCat.ofHom (LinearMap.toSpanSingleton R A.obj x ∘ₗ eR.toLinearMap))
    have hg_hom : (g ≫ φ).hom = 0 := by
      rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
      refine ModuleCat.hom_ext (LinearMap.ext fun r ↦ ?_)
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply, LinearMap.comp_apply,
        LinearMap.toSpanSingleton_apply, map_smul, LinearMap.mem_ker.mp hx, smul_zero,
        ModuleCat.hom_zero, LinearMap.zero_apply]
    have hg : g ≫ φ = 0 := ObjectProperty.hom_ext _ hg_hom
    have hu := congrArg (fun k ↦ k.hom.hom (eR.symm 1))
      (hc.fac (KernelFork.ofι g hg) WalkingParallelPair.zero)
    rw [Fork.app_zero_eq_ι, Fork.app_zero_eq_ι, KernelFork.ι_ofι,
      ObjectProperty.FullSubcategory.comp_hom, ModuleCat.hom_comp, LinearMap.comp_apply] at hu
    have hgx : g.hom.hom (eR.symm 1) = x := by
      rw [ObjectProperty.homMk_hom, ModuleCat.hom_ofHom, LinearMap.comp_apply,
        LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.toSpanSingleton_apply_one]
    exact ⟨(hc.lift (KernelFork.ofι g hg)).hom.hom (eR.symm 1), hu.trans hgx⟩

/-- For a full subcategory `S` of `ModuleCat.{v} R` containing an object `R₀` linearly equivalent to
`R`, the range of a weak kernel `weakKernel.ι φ` is the kernel of `φ`. -/
theorem range_weakKernel_ι_eq_ker {R₀ : S.FullSubcategory} (eR : R₀.obj ≃ₗ[R] R)
    {A B : S.FullSubcategory} (φ : A ⟶ B) [HasWeakKernel φ] :
    LinearMap.range (weakKernel.ι φ).hom.hom = LinearMap.ker φ.hom.hom :=
  S.range_ι_eq_ker_of_isWeakLimit eR (c := Fork.ofι (weakKernel.ι φ) _)
    (weakKernelIsWeakKernel φ)

end CategoryTheory.ObjectProperty
