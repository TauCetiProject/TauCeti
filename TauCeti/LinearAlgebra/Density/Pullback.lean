/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic

/-!
# Linear pullback of densities

Pullback of a density along any linear map `L : V →ₗ[ℝ] W` between linearly equivalent real vector
spaces (`TauCeti.Density.compLinearMap`, requiring only `Nonempty (V ≃ₗ[ℝ] W)`), with determinant
scaling (`compLinearMap_eq_abs_det_smul`) and the linear-equivalence specialization
(`compLinearEquiv : Density W m ≃ₗ[ℝ] Density V m`).
-/

public section

noncomputable section

namespace TauCeti.Density

section LinearMap

variable {U V W : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {m : ℕ}

/-- Pullback of a density along `L : V →ₗ[ℝ] W` between linearly equivalent spaces. -/
def compLinearMap (μ : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) : Density V m where
  toFun v := μ (L ∘ v)
  map_comp T v := by
    obtain ⟨e⟩ := h
    let S : W →ₗ[ℝ] W := L.comp e.symm.toLinearMap
    let T' : W →ₗ[ℝ] W := (e : V →ₗ[ℝ] W) ∘ₗ T ∘ₗ (e.symm : W →ₗ[ℝ] V)
    have h₁ : L ∘ (T ∘ v) = ((S.comp T' : W →ₗ[ℝ] W) : W → W) ∘ (e ∘ v) := by ext i; simp [S, T']
    have h₂ : L ∘ v = (S : W → W) ∘ (e ∘ v) := by ext i; simp [S]
    rw [h₁, μ.comp_apply, LinearMap.det_comp, abs_mul, mul_assoc,
      mul_left_comm |LinearMap.det S|, ← μ.comp_apply, ← h₂, LinearMap.det_conj T e]

/-- Evaluation of `compLinearMap` on a tuple of vectors. -/
@[simp] theorem compLinearMap_apply (μ : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W))
    (v : Fin m → V) : μ.compLinearMap L h v = μ (L ∘ v) := (rfl)

/-- Pullback along `LinearMap.id` is the identity. -/
@[simp] theorem compLinearMap_id (μ : Density V m) (h : Nonempty (V ≃ₗ[ℝ] V)) :
    μ.compLinearMap LinearMap.id h = μ := by ext; simp

/-- `compLinearMap` is contravariant under composition. -/
theorem compLinearMap_comp (μ : Density W m) (L : U →ₗ[ℝ] V) (M : V →ₗ[ℝ] W)
    (h₁ : Nonempty (U ≃ₗ[ℝ] V)) (h₂ : Nonempty (V ≃ₗ[ℝ] W)) :
    μ.compLinearMap (M.comp L) (h₁.elim fun e₁ ↦ h₂.elim fun e₂ ↦ ⟨e₁.trans e₂⟩) =
      (μ.compLinearMap M h₂).compLinearMap L h₁ := by ext; simp [Function.comp_assoc]

/-- Pullback of a density along an endomorphism scales by `|LinearMap.det L|`. -/
theorem compLinearMap_eq_abs_det_smul (μ : Density V m) (L : V →ₗ[ℝ] V)
    (h : Nonempty (V ≃ₗ[ℝ] V)) : μ.compLinearMap L h = |LinearMap.det L| • μ := by
  ext v; exact μ.comp_apply L v

/-- Pulling back zero via `compLinearMap` gives zero. -/
@[simp] theorem zero_compLinearMap (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) :
    (0 : Density W m).compLinearMap L h = 0 := by ext; simp

/-- `compLinearMap` distributes over addition. -/
@[simp] theorem add_compLinearMap (μ ν : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) :
    (μ + ν).compLinearMap L h = μ.compLinearMap L h + ν.compLinearMap L h := by ext; simp

/-- `compLinearMap` commutes with scalar multiplication. -/
@[simp] theorem smul_compLinearMap {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ] (c : R)
    (μ : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) :
    (c • μ).compLinearMap L h = c • μ.compLinearMap L h := by ext; simp

/-- `compLinearMap` commutes with negation. -/
@[simp] theorem neg_compLinearMap (μ : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) :
    (-μ).compLinearMap L h = -μ.compLinearMap L h := by ext; simp

/-- `compLinearMap` distributes over subtraction. -/
@[simp] theorem sub_compLinearMap (μ ν : Density W m) (L : V →ₗ[ℝ] W) (h : Nonempty (V ≃ₗ[ℝ] W)) :
    (μ - ν).compLinearMap L h = μ.compLinearMap L h - ν.compLinearMap L h := by ext; simp

end LinearMap

section Equiv

variable {U V W : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {m : ℕ}

/-- Pullback of a density along a linear equivalence, as a linear equivalence. -/
def compLinearEquiv (e : V ≃ₗ[ℝ] W) : Density W m ≃ₗ[ℝ] Density V m where
  toFun μ := μ.compLinearMap e ⟨e⟩
  invFun μ := μ.compLinearMap e.symm ⟨e.symm⟩
  left_inv μ := by ext v; simp [Function.comp_def]
  right_inv μ := by ext v; simp [Function.comp_def]
  map_add' μ ν := add_compLinearMap μ ν e ⟨e⟩
  map_smul' c μ := smul_compLinearMap c μ e ⟨e⟩

/-- Evaluation of `compLinearEquiv` on a tuple of vectors. -/
@[simp] theorem compLinearEquiv_apply (e : V ≃ₗ[ℝ] W) (μ : Density W m) (v : Fin m → V) :
    compLinearEquiv e μ v = μ (e ∘ v) := (rfl)

/-- The inverse of `compLinearEquiv e` is `compLinearEquiv e.symm`. -/
@[simp] theorem compLinearEquiv_symm (e : V ≃ₗ[ℝ] W) :
    (compLinearEquiv (m := m) e).symm = compLinearEquiv e.symm := by ext; rfl

/-- Pulling back along `e.toLinearMap` agrees with `compLinearEquiv e`. -/
@[simp] theorem compLinearMap_toLinearMap (μ : Density W m) (e : V ≃ₗ[ℝ] W)
    (h : Nonempty (V ≃ₗ[ℝ] W)) : μ.compLinearMap e.toLinearMap h = compLinearEquiv e μ := by
  ext; simp

/-- Pullback along `LinearEquiv.refl` is the identity equivalence. -/
@[simp] theorem compLinearEquiv_refl :
    compLinearEquiv (m := m) (LinearEquiv.refl ℝ V) = LinearEquiv.refl ℝ (Density V m) := by
  ext; simp [Function.comp_def]

/-- Pullback along linear equivalences is contravariant under `LinearEquiv.trans`. -/
theorem compLinearEquiv_trans (e₁ : U ≃ₗ[ℝ] V) (e₂ : V ≃ₗ[ℝ] W) :
    compLinearEquiv (m := m) (e₁.trans e₂) =
      (compLinearEquiv e₂).trans (compLinearEquiv e₁) := by
  ext; simp [Function.comp_def]

end Equiv

end TauCeti.Density
