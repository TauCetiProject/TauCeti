/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Morphisms into finite direct sums of representations

A morphism into a finite direct sum is determined by its component morphisms. The resulting
linear equivalence lets dimension computations use a concrete direct-sum representation without
replacing it by a categorical biproduct.
-/

public section

open CategoryTheory Representation DirectSum

namespace Rep

universe v

variable {k G : Type*} [CommSemiring k] [Monoid G] {ι : Type v} [Fintype ι]
  (A : Rep.{v} k G) (B : ι → Rep.{v} k G)

/-- Morphisms into a finite direct sum are families of morphisms into its summands. -/
noncomputable def homDirectSumLinearEquiv :
    (A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) ≃ₗ[k] (∀ i, A ⟶ B i) := by
  classical
  let e := DirectSum.linearEquivFunOnFintype k ι (fun i ↦ (B i : Type v))
  have he (g : G) (x : ⨁ i, (B i : Type v)) (i : ι) :
      e (directSum (fun i ↦ (B i).ρ) g x) i = (B i).ρ g (e x i) := by
    simp [e, directSum_apply]
  let f (φ : A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) (i : ι) : A ⟶ B i :=
    Rep.ofHom ⟨(LinearMap.proj i).comp (e.toLinearMap.comp φ.hom.toLinearMap),
      fun g ↦ LinearMap.ext fun x ↦ by
        simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe]
        simp only [IntertwiningMap.coe_toLinearMap]
        rw [Rep.hom_comm_apply φ]
        exact he g (φ.hom x) i⟩
  let l (φ : ∀ i, A ⟶ B i) : A →ₗ[k] ⨁ i, (B i : Type v) :=
    e.symm.toLinearMap.comp (LinearMap.pi fun i ↦ (φ i).hom.toLinearMap)
  let h (φ : ∀ i, A ⟶ B i) : A ⟶ Rep.of (directSum fun i ↦ (B i).ρ) :=
    Rep.ofHom ⟨l φ, fun g ↦ LinearMap.ext fun x ↦ by
      apply e.injective
      ext i
      simp only [LinearMap.comp_apply]
      rw [he]
      simp [l, IntertwiningMap.coe_toLinearMap, Rep.hom_comm_apply]⟩
  exact
    { toFun := f
      invFun := h
      left_inv φ := by
        apply Rep.hom_ext
        apply IntertwiningMap.ext
        apply LinearMap.ext
        intro x
        apply e.injective
        ext i
        simp [h, l, f, IntertwiningMap.coe_toLinearMap]
      right_inv φ := by
        funext i
        ext x
        simp [h, l, f]
      map_add' φ ψ := by
        funext i
        ext x
        simp [f, Rep.add_hom, IntertwiningMap.coe_toLinearMap]
      map_smul' r φ := by
        funext i
        ext x
        simp [f, Rep.smul_hom, IntertwiningMap.coe_toLinearMap] }

/-- A component morphism evaluates to the corresponding coordinate in the direct sum. -/
@[simp]
theorem homDirectSumLinearEquiv_apply
    (φ : A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) (i : ι) (x : A) :
    (homDirectSumLinearEquiv A B φ i).hom x = φ.hom x i := by
  classical
  simp only [homDirectSumLinearEquiv, LinearEquiv.coe_mk, LinearMap.coe_mk,
    AddHom.coe_mk, Rep.hom_ofHom,
    IntertwiningMap.coe_mk, LinearMap.comp_apply,
    LinearMap.proj_apply, LinearEquiv.coe_coe, IntertwiningMap.coe_toLinearMap,
    DirectSum.linearEquivFunOnFintype_apply]

/-- The inverse assembles the supplied component morphisms. -/
@[simp]
theorem homDirectSumLinearEquiv_symm_apply (φ : ∀ i, A ⟶ B i) (x : A) (i : ι) :
    ((homDirectSumLinearEquiv A B).symm φ).hom x i = (φ i).hom x := by
  classical
  exact congrFun ((DirectSum.linearEquivFunOnFintype k ι
    (fun i ↦ (B i : Type v))).apply_symm_apply (fun j ↦ (φ j).hom x)) i

end Rep
