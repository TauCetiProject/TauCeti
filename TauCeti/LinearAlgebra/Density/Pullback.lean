/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Density.Basic

/-!
# Linear pullback of densities

Unlike alternating maps, a density on `W` does not pull back along linear maps from spaces of a
different dimension, because its transformation law uses the ambient endomorphism determinant. It
does pull back along every linear endomorphism of `V` (`TauCeti.Density.compEnd`), along every
linear equivalence `V ≃ₗ[ℝ] W` (`TauCeti.Density.compLinearEquiv`), and hence along every
linear map `L : V →ₗ[ℝ] W` between linearly equivalent real vector spaces
(`TauCeti.Density.compLinearMapOfEquiv`), independently of the chosen equivalence. No
finite-dimensionality assumption is needed.

## Main definitions

* `TauCeti.Density.compEnd`: pullback of a density along a linear endomorphism.
* `TauCeti.Density.compLinearEquiv`: pullback of a density along a linear equivalence.
* `TauCeti.Density.compLinearMapOfEquiv`: pullback of a density along any linear map between
  linearly equivalent spaces.

## Main results

* `TauCeti.Density.compEnd_apply_eq_abs_det_mul`: endomorphism pullback multiplies every tuple
  value by `|LinearMap.det L|`.
* `TauCeti.Density.compLinearMapOfEquiv_eq`: `compLinearMapOfEquiv` is independent of the chosen
  linear equivalence.
-/

public section

noncomputable section

namespace TauCeti.Density

section End

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {m : ℕ}

/-- Pullback of a density along a linear endomorphism. No finite-dimensionality assumption is
needed because `LinearMap.det` is multiplicative on endomorphisms in general. -/
def compEnd (μ : Density V m) (L : V →ₗ[ℝ] V) : Density V m where
  toFun v := μ (L ∘ v)
  map_comp T v := by
    have hcomp : L ∘ (T ∘ v) = ((L.comp T : V →ₗ[ℝ] V) : V → V) ∘ v := rfl
    rw [hcomp, μ.comp_apply, LinearMap.det_comp, abs_mul, mul_assoc,
      mul_left_comm |LinearMap.det L|, ← μ.comp_apply]

/-- Evaluation of `compEnd` on a tuple of vectors. -/
@[simp]
theorem compEnd_apply (μ : Density V m) (L : V →ₗ[ℝ] V) (v : Fin m → V) :
    μ.compEnd L v = μ (L ∘ v) := (rfl)

/-- Pulling back a density along an endomorphism multiplies every tuple value by the absolute
determinant of the endomorphism. -/
theorem compEnd_apply_eq_abs_det_mul (μ : Density V m) (L : V →ₗ[ℝ] V) (v : Fin m → V) :
    μ.compEnd L v = |LinearMap.det L| * μ v :=
  μ.comp_apply L v

/-- Pullback along the identity endomorphism is the identity on densities. -/
@[simp]
theorem compEnd_id (μ : Density V m) : μ.compEnd LinearMap.id = μ := by
  ext v
  rfl

/-- Endomorphism pullback is contravariant under composition. -/
theorem compEnd_comp (μ : Density V m) (L M : V →ₗ[ℝ] V) :
    μ.compEnd (M.comp L) = (μ.compEnd M).compEnd L := by
  ext v
  rfl

/-- Pulling back the zero density along an endomorphism gives zero. -/
@[simp]
theorem zero_compEnd (L : V →ₗ[ℝ] V) : (0 : Density V m).compEnd L = 0 := by
  ext v
  rfl

/-- Endomorphism pullback distributes over addition of densities. -/
@[simp]
theorem add_compEnd (μ ν : Density V m) (L : V →ₗ[ℝ] V) :
    (μ + ν).compEnd L = μ.compEnd L + ν.compEnd L := by
  ext v
  rfl

/-- Endomorphism pullback commutes with scalar multiplication. -/
@[simp]
theorem smul_compEnd {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ]
    (c : R) (μ : Density V m) (L : V →ₗ[ℝ] V) :
    (c • μ).compEnd L = c • μ.compEnd L := by
  ext v
  rfl

/-- Endomorphism pullback commutes with negation. -/
@[simp]
theorem neg_compEnd (μ : Density V m) (L : V →ₗ[ℝ] V) :
    (-μ).compEnd L = -μ.compEnd L := by
  ext v
  rfl

/-- Endomorphism pullback distributes over subtraction of densities. -/
@[simp]
theorem sub_compEnd (μ ν : Density V m) (L : V →ₗ[ℝ] V) :
    (μ - ν).compEnd L = μ.compEnd L - ν.compEnd L := by
  ext v
  rfl

end End

section Equiv

variable {U V W : Type*} [AddCommGroup U] [Module ℝ U]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W] {m : ℕ}

/-- Pullback of a density along a linear equivalence, with no finite-dimensionality assumption. -/
def compLinearEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W) : Density V m where
  toFun v := μ (e ∘ v)
  map_comp T v := by
    let T' : W →ₗ[ℝ] W := (e : V →ₗ[ℝ] W) ∘ₗ T ∘ₗ (e.symm : W →ₗ[ℝ] V)
    have hconj : (e : V → W) ∘ (T ∘ v) = (T' : W → W) ∘ (e ∘ v) := by
      ext i
      simp [T']
    rw [hconj, μ.comp_apply, LinearMap.det_conj T e]

/-- Evaluation of `compLinearEquiv` on a tuple of vectors. -/
@[simp]
theorem compLinearEquiv_apply (μ : Density W m) (e : V ≃ₗ[ℝ] W) (v : Fin m → V) :
    μ.compLinearEquiv e v = μ (e ∘ v) := (rfl)

/-- Pullback along the identity linear equivalence is the identity on densities. -/
@[simp]
theorem compLinearEquiv_refl (μ : Density V m) :
    μ.compLinearEquiv (LinearEquiv.refl ℝ V) = μ := by
  ext v
  rfl

/-- Pullback along linear equivalences is contravariant under `LinearEquiv.trans`. -/
theorem compLinearEquiv_trans (μ : Density W m) (e₁ : U ≃ₗ[ℝ] V) (e₂ : V ≃ₗ[ℝ] W) :
    μ.compLinearEquiv (e₁.trans e₂) = (μ.compLinearEquiv e₂).compLinearEquiv e₁ := by
  ext v
  rfl

/-- Pulling back the zero density along a linear equivalence gives zero. -/
@[simp]
theorem zero_compLinearEquiv (e : V ≃ₗ[ℝ] W) :
    (0 : Density W m).compLinearEquiv e = 0 := by
  ext v
  rfl

/-- Pullback along a linear equivalence distributes over addition of densities. -/
@[simp]
theorem add_compLinearEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) :
    (μ + ν).compLinearEquiv e = μ.compLinearEquiv e + ν.compLinearEquiv e := by
  ext v
  rfl

/-- Pullback along a linear equivalence commutes with scalar multiplication. -/
@[simp]
theorem smul_compLinearEquiv {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ]
    (c : R) (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    (c • μ).compLinearEquiv e = c • μ.compLinearEquiv e := by
  ext v
  rfl

/-- Pullback along a linear equivalence commutes with negation. -/
@[simp]
theorem neg_compLinearEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W) :
    (-μ).compLinearEquiv e = -μ.compLinearEquiv e := by
  ext v
  rfl

/-- Pullback along a linear equivalence distributes over subtraction of densities. -/
@[simp]
theorem sub_compLinearEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) :
    (μ - ν).compLinearEquiv e = μ.compLinearEquiv e - ν.compLinearEquiv e := by
  ext v
  rfl

/-- Pullback of a density along any linear map `L : V →ₗ[ℝ] W` when a linear equivalence
`e : V ≃ₗ[ℝ] W` is available. The resulting density depends only on `μ` and `L`,
not on `e`. -/
def compLinearMapOfEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W)
    (L : V →ₗ[ℝ] W) : Density V m :=
  (μ.compLinearEquiv e).compEnd ((e.symm : W →ₗ[ℝ] V).comp L)

/-- Evaluation of `compLinearMapOfEquiv` on a tuple of vectors. -/
@[simp]
theorem compLinearMapOfEquiv_apply (μ : Density W m) (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W)
    (v : Fin m → V) : μ.compLinearMapOfEquiv e L v = μ (L ∘ v) := by
  simp only [compLinearMapOfEquiv, compEnd_apply, compLinearEquiv_apply]
  congr 1
  ext i
  simp

/-- `compLinearMapOfEquiv` is independent of the chosen linear equivalence between `V` and `W`. -/
theorem compLinearMapOfEquiv_eq (μ : Density W m) (e₁ e₂ : V ≃ₗ[ℝ] W)
    (L : V →ₗ[ℝ] W) :
    μ.compLinearMapOfEquiv e₁ L = μ.compLinearMapOfEquiv e₂ L := by
  ext v
  simp

/-- Pulling back the zero density via `compLinearMapOfEquiv` gives zero. -/
@[simp]
theorem zero_compLinearMapOfEquiv (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W) :
    (0 : Density W m).compLinearMapOfEquiv e L = 0 := by
  ext v
  simp

/-- `compLinearMapOfEquiv` distributes over addition of densities. -/
@[simp]
theorem add_compLinearMapOfEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W) :
    (μ + ν).compLinearMapOfEquiv e L =
      μ.compLinearMapOfEquiv e L + ν.compLinearMapOfEquiv e L := by
  ext v
  simp

/-- `compLinearMapOfEquiv` commutes with scalar multiplication. -/
@[simp]
theorem smul_compLinearMapOfEquiv {R : Type*} [SMul R ℝ] [SMulCommClass R ℝ ℝ]
    (c : R) (μ : Density W m) (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W) :
    (c • μ).compLinearMapOfEquiv e L = c • μ.compLinearMapOfEquiv e L := by
  ext v
  simp

/-- `compLinearMapOfEquiv` commutes with negation. -/
@[simp]
theorem neg_compLinearMapOfEquiv (μ : Density W m) (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W) :
    (-μ).compLinearMapOfEquiv e L = -μ.compLinearMapOfEquiv e L := by
  ext v
  simp

/-- `compLinearMapOfEquiv` distributes over subtraction of densities. -/
@[simp]
theorem sub_compLinearMapOfEquiv (μ ν : Density W m) (e : V ≃ₗ[ℝ] W) (L : V →ₗ[ℝ] W) :
    (μ - ν).compLinearMapOfEquiv e L =
      μ.compLinearMapOfEquiv e L - ν.compLinearMapOfEquiv e L := by
  ext v
  simp

end Equiv

end TauCeti.Density
