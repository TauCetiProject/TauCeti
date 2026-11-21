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
spaces (`TauCeti.Density.compLinearMap`, requiring only `Nonempty (V ≃ₗ[ℝ] W)`), specialized to
endomorphisms (`compEnd`) and linear equivalences (`compLinearEquiv`), with functoriality,
determinant scaling (`compEnd_eq_abs_det_smul`), and invertibility (`compLinearEquiv_injective`).
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

section End

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- Pullback of a density along a linear endomorphism. -/
def compEnd (μ : Density V m) (L : V →ₗ[ℝ] V) : Density V m := μ.compLinearMap L ⟨.refl ℝ V⟩

/-- Evaluation of `compEnd` on a tuple of vectors. -/
@[simp] theorem compEnd_apply (μ : Density V m) (L : V →ₗ[ℝ] V) (v : Fin m → V) :
    μ.compEnd L v = μ (L ∘ v) := (rfl)

/-- For an endomorphism, `compLinearMap` agrees with `compEnd`. -/
theorem compLinearMap_eq_compEnd (μ : Density V m) (L : V →ₗ[ℝ] V) (h : Nonempty (V ≃ₗ[ℝ] V)) :
    μ.compLinearMap L h = μ.compEnd L := by ext; simp

/-- Endomorphism pullback scales a density by `|LinearMap.det L|`. -/
theorem compEnd_eq_abs_det_smul (μ : Density V m) (L : V →ₗ[ℝ] V) :
    μ.compEnd L = |LinearMap.det L| • μ := by ext v; exact μ.comp_apply L v

/-- Pullback along `LinearMap.id` is the identity. -/
@[simp] theorem compEnd_id (μ : Density V m) : μ.compEnd LinearMap.id = μ := compLinearMap_id μ _

/-- Endomorphism pullback is contravariant under composition. -/
theorem compEnd_comp (μ : Density V m) (L M : V →ₗ[ℝ] V) :
    μ.compEnd (M.comp L) = (μ.compEnd M).compEnd L := compLinearMap_comp μ L M _ _

/-- Pulling back zero along an endomorphism gives zero. -/
@[simp] theorem zero_compEnd (L : V →ₗ[ℝ] V) :
    (0 : Density V m).compEnd L = 0 := zero_compLinearMap L _

/-- Endomorphism pullback distributes over addition. -/
@[simp] theorem add_compEnd (μ ν : Density V m) (L : V →ₗ[ℝ] V) :
    (μ + ν).compEnd L = μ.compEnd L + ν.compEnd L := add_compLinearMap μ ν L _

/-- Endomorphism pullback commutes with scalar multiplication. -/
@[simp] theorem smul_compEnd {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ] (c : R)
    (μ : Density V m) (L : V →ₗ[ℝ] V) :
    (c • μ).compEnd L = c • μ.compEnd L := smul_compLinearMap c μ L _

/-- Endomorphism pullback commutes with negation. -/
@[simp] theorem neg_compEnd (μ : Density V m) (L : V →ₗ[ℝ] V) :
    (-μ).compEnd L = -μ.compEnd L := neg_compLinearMap μ L _

/-- Endomorphism pullback distributes over subtraction. -/
@[simp] theorem sub_compEnd (μ ν : Density V m) (L : V →ₗ[ℝ] V) :
    (μ - ν).compEnd L = μ.compEnd L - ν.compEnd L := sub_compLinearMap μ ν L _

end End

section Equiv

variable {U V W : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {m : ℕ}

/-- Pullback of a density along a linear equivalence. -/
def compLinearEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W) : Density V m := μ.compLinearMap e ⟨e⟩

/-- Evaluation of `compLinearEquiv` on a tuple of vectors. -/
@[simp] theorem compLinearEquiv_apply (μ : Density W m) (e : V ≃ₗ[ℝ] W) (v : Fin m → V) :
    μ.compLinearEquiv e v = μ (e ∘ v) := (rfl)

/-- Pulling back along `e.toLinearMap` agrees with `compLinearEquiv e`. -/
@[simp] theorem compLinearMap_toLinearMap (μ : Density W m) (e : V ≃ₗ[ℝ] W)
    (h : Nonempty (V ≃ₗ[ℝ] W)) : μ.compLinearMap e.toLinearMap h = μ.compLinearEquiv e := by
  ext; simp

/-- Pulling back along an automorphism agrees with `compEnd e.toLinearMap`. -/
theorem compLinearEquiv_eq_compEnd (μ : Density V m) (e : V ≃ₗ[ℝ] V) :
    μ.compLinearEquiv e = μ.compEnd e.toLinearMap := by ext; simp

/-- Pullback along `LinearEquiv.refl` is the identity. -/
@[simp] theorem compLinearEquiv_refl (μ : Density V m) :
    μ.compLinearEquiv (LinearEquiv.refl ℝ V) = μ := compLinearMap_id μ _

/-- Pullback along linear equivalences is contravariant under `LinearEquiv.trans`. -/
theorem compLinearEquiv_trans (μ : Density W m) (e₁ : U ≃ₗ[ℝ] V) (e₂ : V ≃ₗ[ℝ] W) :
    μ.compLinearEquiv (e₁.trans e₂) = (μ.compLinearEquiv e₂).compLinearEquiv e₁ :=
  compLinearMap_comp μ e₁.toLinearMap e₂.toLinearMap ⟨e₁⟩ ⟨e₂⟩

/-- Pulling back along `e` then `e.symm` recovers `μ`. -/
@[simp] theorem compLinearEquiv_compLinearEquiv_symm (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    (μ.compLinearEquiv e).compLinearEquiv e.symm = μ := by
  rw [← compLinearEquiv_trans, LinearEquiv.symm_trans_self, compLinearEquiv_refl]

/-- Pulling back along `e.symm` then `e` recovers `μ`. -/
@[simp] theorem compLinearEquiv_symm_compLinearEquiv (μ : Density V m) (e : V ≃ₗ[ℝ] W) :
    (μ.compLinearEquiv e.symm).compLinearEquiv e = μ := by
  rw [← compLinearEquiv_trans, LinearEquiv.self_trans_symm, compLinearEquiv_refl]

/-- Pullback along a linear equivalence is injective. -/
theorem compLinearEquiv_injective (e : V ≃ₗ[ℝ] W) :
    Function.Injective (fun μ : Density W m ↦ μ.compLinearEquiv e) :=
  Function.LeftInverse.injective (g := fun μ ↦ μ.compLinearEquiv e.symm)
    fun μ ↦ μ.compLinearEquiv_compLinearEquiv_symm e

/-- Pulling back zero along a linear equivalence gives zero. -/
@[simp] theorem zero_compLinearEquiv (e : V ≃ₗ[ℝ] W) :
    (0 : Density W m).compLinearEquiv e = 0 := zero_compLinearMap e.toLinearMap _

/-- A density pulled back along `e` vanishes iff the original density vanishes. -/
@[simp] theorem compLinearEquiv_eq_zero_iff (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    μ.compLinearEquiv e = 0 ↔ μ = 0 :=
  ⟨fun h ↦ compLinearEquiv_injective e (h.trans (zero_compLinearEquiv e).symm),
    fun h ↦ by rw [h, zero_compLinearEquiv]⟩

/-- Pullback along a linear equivalence distributes over addition. -/
@[simp] theorem add_compLinearEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) :
    (μ + ν).compLinearEquiv e = μ.compLinearEquiv e + ν.compLinearEquiv e :=
  add_compLinearMap μ ν _ _

/-- Pullback along a linear equivalence commutes with scalar multiplication. -/
@[simp] theorem smul_compLinearEquiv {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ] (c : R)
    (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    (c • μ).compLinearEquiv e = c • μ.compLinearEquiv e := smul_compLinearMap c μ _ _

/-- Pullback along a linear equivalence commutes with negation. -/
@[simp] theorem neg_compLinearEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    (-μ).compLinearEquiv e = -μ.compLinearEquiv e := neg_compLinearMap μ _ _

/-- Pullback along a linear equivalence distributes over subtraction. -/
@[simp] theorem sub_compLinearEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) :
    (μ - ν).compLinearEquiv e = μ.compLinearEquiv e - ν.compLinearEquiv e :=
  sub_compLinearMap μ ν _ _

end Equiv

end TauCeti.Density
