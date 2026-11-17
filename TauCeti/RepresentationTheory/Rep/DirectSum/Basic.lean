/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Finite direct sums of representations

An intertwining map into a finite direct sum is determined by its components
(`Representation.IntertwiningMap.directSumLinearEquiv`, for carriers in arbitrary universes), and
so is a morphism of `Rep` (`Rep.homDirectSumLinearEquiv`). The resulting linear equivalences let
dimension computations use a concrete direct-sum representation without replacing it by a
categorical biproduct.

The natural identification with a dependent product conjugates the direct-sum action to the
componentwise action, so finite direct sums can also be studied through product linear maps.
-/

public section

open CategoryTheory Representation DirectSum

namespace Representation

/-- The finite direct-sum action becomes the componentwise action under the natural
identification with the dependent product. -/
theorem conj_directSum_linearEquivFunOnFintype
    {k G ι : Type*} [CommSemiring k] [Monoid G] [Fintype ι]
    {V : ι → Type*} [∀ i, AddCommMonoid (V i)] [∀ i, Module k (V i)]
    (ρ : ∀ i, Representation k G (V i)) (g : G) :
    (DirectSum.linearEquivFunOnFintype k ι V).conj (directSum ρ g) =
      LinearMap.piMap (fun i ↦ ρ i g) := by
  classical
  apply LinearMap.ext
  intro x
  funext i
  simp only [LinearEquiv.conj_apply_apply, LinearMap.coe_piMap, Pi.map_apply,
    DirectSum.linearEquivFunOnFintype_apply, directSum_apply, DirectSum.lmap_apply]
  rw [← DirectSum.linearEquivFunOnFintype_apply k ι V, LinearEquiv.apply_symm_apply]

end Representation

namespace Representation.IntertwiningMap

variable {k G V ι : Type*} [CommSemiring k] [Monoid G] [Finite ι] [AddCommMonoid V] [Module k V]
  {W : ι → Type*} [∀ i, AddCommMonoid (W i)] [∀ i, Module k (W i)]
  (τ : Representation k G V) (σ : ∀ i, Representation k G (W i))

/-- Intertwining maps into a finite direct sum are families of intertwining maps into its
summands. The carriers may lie in different universes. -/
noncomputable def directSumLinearEquiv :
    IntertwiningMap τ (directSum σ) ≃ₗ[k] ∀ i, IntertwiningMap τ (σ i) := by
  classical
  let := Fintype.ofFinite ι
  let e := DirectSum.linearEquivFunOnFintype k ι W
  have he (g : G) (x : ⨁ i, W i) (i : ι) : e (directSum σ g x) i = σ i g (e x i) := by
    simp [e, directSum_apply]
  exact
    { toFun f i := ⟨LinearMap.proj i ∘ₗ e.toLinearMap ∘ₗ f.toLinearMap, fun g ↦
        LinearMap.ext fun x ↦ by
          simp only [LinearMap.comp_apply, LinearMap.proj_apply, LinearEquiv.coe_coe,
            coe_toLinearMap]
          rw [f.isIntertwining, he]⟩
      invFun f := ⟨e.symm.toLinearMap ∘ₗ LinearMap.pi fun i ↦ (f i).toLinearMap, fun g ↦
        LinearMap.ext fun x ↦ e.injective <| funext fun i ↦ by
          simp only [LinearMap.comp_apply]
          rw [he]
          simp [isIntertwining]⟩
      left_inv f := ext <| LinearMap.ext fun x ↦ e.injective <| funext fun i ↦ by simp
      right_inv f := funext fun i ↦ ext <| LinearMap.ext fun x ↦ by simp
      map_add' f f' := funext fun i ↦ ext <| LinearMap.ext fun x ↦ by simp
      map_smul' c f := funext fun i ↦ ext <| LinearMap.ext fun x ↦ by simp }

/-- A component intertwining map evaluates to the corresponding coordinate in the direct sum. -/
@[simp]
theorem directSumLinearEquiv_apply (f : IntertwiningMap τ (directSum σ)) (i : ι) (x : V) :
    directSumLinearEquiv τ σ f i x = f x i := by
  classical
  let := Fintype.ofFinite ι
  simp [directSumLinearEquiv]

/-- The inverse assembles the supplied component intertwining maps. -/
@[simp]
theorem directSumLinearEquiv_symm_apply (f : ∀ i, IntertwiningMap τ (σ i)) (x : V) (i : ι) :
    (directSumLinearEquiv τ σ).symm f x i = f i x := by
  rw [← directSumLinearEquiv_apply τ σ, LinearEquiv.apply_symm_apply]

/-- Taking a component commutes with precomposition. -/
@[simp]
theorem directSumLinearEquiv_comp {V' : Type*} [AddCommMonoid V'] [Module k V']
    {τ' : Representation k G V'} (f : IntertwiningMap τ (directSum σ)) (g : IntertwiningMap τ' τ)
    (i : ι) : directSumLinearEquiv τ' σ (f.comp g) i = (directSumLinearEquiv τ σ f i).comp g := by
  ext x
  simp

end Representation.IntertwiningMap

namespace Rep

universe v

variable {k G : Type*} [CommSemiring k] [Monoid G] {ι : Type v} [Finite ι]
  (A : Rep.{v} k G) (B : ι → Rep.{v} k G)

/-- Morphisms into a finite direct sum are families of morphisms into its summands. -/
noncomputable def homDirectSumLinearEquiv :
    (A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) ≃ₗ[k] (∀ i, A ⟶ B i) where
  toFun φ i := Rep.ofHom (IntertwiningMap.directSumLinearEquiv A.ρ (fun i ↦ (B i).ρ) φ.hom i)
  invFun φ := Rep.ofHom ((IntertwiningMap.directSumLinearEquiv A.ρ (fun i ↦ (B i).ρ)).symm
    fun i ↦ (φ i).hom)
  left_inv φ := by simp
  right_inv φ := by simp
  map_add' φ ψ := funext fun i ↦ by simp [Rep.ofHom_add, Rep.add_hom]
  map_smul' r φ := funext fun i ↦ by simp [Rep.ofHom_smul, Rep.smul_hom]

/-- A component morphism evaluates to the corresponding coordinate in the direct sum. -/
@[simp]
theorem homDirectSumLinearEquiv_apply
    (φ : A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) (i : ι) (x : A) :
    (homDirectSumLinearEquiv A B φ i).hom x = φ.hom x i :=
  IntertwiningMap.directSumLinearEquiv_apply _ _ φ.hom i x

/-- The inverse assembles the supplied component morphisms. -/
@[simp]
theorem homDirectSumLinearEquiv_symm_apply (φ : ∀ i, A ⟶ B i) (x : A) (i : ι) :
    ((homDirectSumLinearEquiv A B).symm φ).hom x i = (φ i).hom x :=
  IntertwiningMap.directSumLinearEquiv_symm_apply _ _ (fun i ↦ (φ i).hom) x i

/-- Taking a component commutes with precomposition. -/
@[simp]
theorem homDirectSumLinearEquiv_comp {A' : Rep.{v} k G} (f : A' ⟶ A)
    (φ : A ⟶ Rep.of (directSum fun i ↦ (B i).ρ)) (i : ι) :
    homDirectSumLinearEquiv A' B (f ≫ φ) i =
      f ≫ homDirectSumLinearEquiv A B φ i := by
  ext x
  simp

end Rep
