/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Euclidean
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# Loops of images of `ℝⁿ` under paths of invertible matrices

A continuous path `M` of invertible complex matrices whose images of the real subspace `ℝⁿ ⊆ ℂⁿ`
close up frames the loop `t ↦ M t ℝⁿ` (`Matrix.realImage`) of maximal totally real subspaces of
`ℂⁿ`. A continuous two-parameter family of such paths is a homotopy of these loops, along which
the Maslov index is constant. For an invertible matrix `M`, the Maslov phase of `M ℝⁿ` relative to
`ℝⁿ` is `det M / conj (det M)`, which is `det U ^ 2` for a unitary matrix `U`.

## Main declarations

* `TauCeti.TotallyRealLoop.ofRealImage`: the loop `t ↦ M t ℝⁿ` of a continuous path `M` of
  invertible matrices whose images of `ℝⁿ` close up.
* `TauCeti.TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy`: homotopy invariance of the
  Maslov index along a continuous family of such paths.
* `Matrix.maslovPhase_eq_det_div_conj_det`: the Maslov phase of `M ℝⁿ` relative to `ℝⁿ`.
* `Matrix.UnitaryGroup.maslovPhase_eq_det_sq`: its unitary case `det U ^ 2`.
-/

public section

noncomputable section

open Matrix
open scoped ComplexConjugate unitInterval

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The loop `t ↦ M t ℝⁿ` of maximal totally real subspaces of `ℂⁿ` framed by a continuous path
`M` of invertible matrices whose images of `ℝⁿ` close up. -/
def TotallyRealLoop.ofRealImage (M : I → GL n ℂ) (hM : Continuous M)
    (h01 : (M 0 : Matrix n n ℂ).realImage = (M 1 : Matrix n n ℂ).realImage) :
    TotallyRealLoop (EuclideanSpace ℂ n) where
  toFun t := (M t : Matrix n n ℂ).realImage
  exists_frame := ⟨realSubspace n, isMaximalTotallyReal_realSubspace,
    fun t ↦ (M t : Matrix n n ℂ).toEuclideanCLE (M t).det_ne_zero,
    GeneralLinearGroup.continuous_toEuclideanCLE hM, fun _ ↦ realImage_eq_map_toEuclideanCLE _⟩
  toFun_zero_eq_toFun_one := h01

/-- The loop of images of `ℝⁿ` under `M` at time `t` is `M t ℝⁿ`. -/
@[simp]
theorem TotallyRealLoop.ofRealImage_apply (M : I → GL n ℂ) (hM : Continuous M)
    (h01 : (M 0 : Matrix n n ℂ).realImage = (M 1 : Matrix n n ℂ).realImage) (t : I) :
    ofRealImage M hM h01 t = (M t : Matrix n n ℂ).realImage :=
  (rfl)

/-- **Homotopy invariance through images of `ℝⁿ`.** Two loops of maximal totally real subspaces of
`ℂⁿ` have the same Maslov index when they are the loops `t ↦ F (0, t) ℝⁿ` and `t ↦ F (1, t) ℝⁿ`
of a continuous family `F` of invertible matrices along which every loop `t ↦ F (s, t) ℝⁿ` closes
up. -/
theorem TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy
    (Λ₀ Λ₁ : TotallyRealLoop (EuclideanSpace ℂ n)) (F : I × I → GL n ℂ) (hF : Continuous F)
    (h₀ : ∀ t, Λ₀ t = (F (0, t) : Matrix n n ℂ).realImage)
    (h₁ : ∀ t, Λ₁ t = (F (1, t) : Matrix n n ℂ).realImage)
    (h01 : ∀ s, (F (s, 0) : Matrix n n ℂ).realImage = (F (s, 1) : Matrix n n ℂ).realImage) :
    Λ₀.maslovIndex = Λ₁.maslovIndex := by
  refine Λ₀.maslovIndex_eq_of_homotopy Λ₁ (L₀ := realSubspace n)
    (fun p ↦ (F p : Matrix n n ℂ).toEuclideanCLE (F p).det_ne_zero)
    (GeneralLinearGroup.continuous_toEuclideanCLE hF) (fun t ↦ ?_) (fun t ↦ ?_) (fun s ↦ ?_)
  · rw [h₀, realImage_eq_map_toEuclideanCLE]
  · rw [h₁, realImage_eq_map_toEuclideanCLE]
  · rw [← realImage_eq_map_toEuclideanCLE, ← realImage_eq_map_toEuclideanCLE]
    exact h01 s

end TauCeti

namespace Matrix

open TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The Maslov phase of the maximal totally real subspace `M ℝⁿ` relative to `ℝⁿ`, for a matrix
`M` (necessarily invertible), is `det M / conj (det M)`. The subspace is given as any `L = M ℝⁿ`,
so that the lemma applies whatever proof of maximal total reality the phase carries. -/
theorem maslovPhase_eq_det_div_conj_det (M : Matrix n n ℂ) {L : Submodule ℝ (EuclideanSpace ℂ n)}
    (hL : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ) L)
    (hLM : L = M.realImage) :
    isMaximalTotallyReal_realSubspace.maslovPhase hL = M.det / conj M.det := by
  have hM : M.det ≠ 0 := isMaximalTotallyReal_realImage_iff.1 (hLM ▸ hL)
  -- `det_toEuclideanCLE` is stated over a general `RCLike` field, so its instances on
  -- `EuclideanSpace ℂ n` agree with the ones in the phase only up to unfolding and `rw` cannot
  -- match it; restate it for the `toLinearEquiv` coercion produced by `maslovPhase_map`.
  have hdetM : LinearMap.det ((M.toEuclideanCLE hM).toLinearEquiv :
      EuclideanSpace ℂ n →ₗ[ℂ] EuclideanSpace ℂ n) = M.det :=
    det_toEuclideanCLE _ hM
  rw [IsMaximalTotallyReal.maslovPhase_congr _ _
      (isMaximalTotallyReal_realSubspace.map_linearEquiv (M.toEuclideanCLE hM).toLinearEquiv)
      (hLM.trans (realImage_eq_map_toEuclideanCLE hM)),
    IsMaximalTotallyReal.maslovPhase_map, hdetM]

namespace UnitaryGroup

/-- The Maslov phase of the Lagrangian `U ℝⁿ` relative to `ℝⁿ`, for a unitary matrix `U`, is
`det U / conj (det U) = det U ^ 2`. The subspace is given as any `L = U ℝⁿ`, so that the lemma
applies whatever proof of maximal total reality the phase carries. -/
theorem maslovPhase_eq_det_sq (U : unitaryGroup n ℂ) {L : Submodule ℝ (EuclideanSpace ℂ n)}
    (hL : IsMaximalTotallyReal
      ((LinearMap.lsmul ℂ (EuclideanSpace ℂ n) Complex.I).restrictScalars ℝ) L)
    (hLU : L = (U : Matrix n n ℂ).realImage) :
    isMaximalTotallyReal_realSubspace.maslovPhase hL = (U : Matrix n n ℂ).det ^ 2 := by
  have hdet : (U : Matrix n n ℂ).det ≠ 0 := GeneralLinearGroup.det_ne_zero (Unitary.toUnits U)
  rw [maslovPhase_eq_det_div_conj_det _ hL hLU, div_eq_iff ((map_ne_zero _).2 hdet)]
  -- `conj (det U) * det U = 1` since `det U` is unitary.
  have hconj : conj (U : Matrix n n ℂ).det * (U : Matrix n n ℂ).det = 1 :=
    Unitary.star_mul_self_of_mem (det_of_mem_unitary U.property)
  linear_combination -(U : Matrix n n ℂ).det * hconj

end UnitaryGroup

end Matrix
