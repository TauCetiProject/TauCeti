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
the Maslov index is constant.

## Main declarations

* `TauCeti.TotallyRealLoop.ofRealImage`: the loop `t ↦ M t ℝⁿ` of a continuous path `M` of
  invertible matrices whose images of `ℝⁿ` close up.
* `TauCeti.TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy`: homotopy invariance of the
  Maslov index along a continuous family of such paths.
-/

public section

noncomputable section

open Matrix
open scoped unitInterval

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
