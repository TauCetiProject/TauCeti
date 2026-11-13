/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TotallyReal.Lagrangian
public import TauCeti.LinearAlgebra.TotallyReal.Maslov.Index

/-!
# Deforming loops of totally real subspaces to Lagrangian loops

A loop `Λ t = A t L₀` of maximal totally real subspaces of `ℂⁿ` (`TauCeti.TotallyRealLoop`) has
the Maslov index of a loop `t ↦ U t ℝⁿ` with every `U t` unitary
(`TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`). Each `U t ℝⁿ` is Lagrangian for the
standard symplectic form `Im ⟪·, ·⟫` of `ℂⁿ` (`TauCeti.im_inner_eq_zero_of_mem_realImage`). This
is how the Maslov index of a totally real boundary condition is compared with invariants defined
only for Lagrangian loops, such as the Robbin–Salamon index of their closed-loop specialization.

The two loops are joined by a homotopy through loops of maximal totally real subspaces with
continuous frames. Write `Λ t = M t ℝⁿ` (`Matrix.realImage`) for a continuous path `M` of
invertible matrices. The closed frame `M` deforms through closed frames to a path `U` of unitary
matrices, by orthonormalizing its real frames and then contracting the positive factor of their
polar decomposition (`TauCeti.exists_realImage_homotopy_unitaryGroup`). Homotopy invariance of the
Maslov index (`TauCeti.TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy`) then compares the
two loops.

## Main declarations

* `TauCeti.TotallyRealLoop.ofRealImage`: the loop `t ↦ M t ℝⁿ` of a continuous path `M` of
  invertible matrices whose images of `ℝⁿ` close up.
* `TauCeti.TotallyRealLoop.maslovIndex_eq_of_realImage_homotopy`: homotopy invariance of the
  Maslov index along a continuous family of such paths.
* `TauCeti.TotallyRealLoop.exists_unitary_maslovIndex_eq`: every loop of maximal totally real
  subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` with `U` a continuous path of
  unitary matrices.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix C.3 (loops of totally real subspaces, their
  Maslov index, and the comparison with Lagrangian loops).
* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford University
  Press, 2017, Section 2.3 (the Lagrangian Grassmannian `U(n) / O(n)` and its Maslov index).
-/

public section

noncomputable section

open Matrix
open scoped unitInterval

namespace TauCeti

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Loops of totally real subspaces of `ℂⁿ` -/

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

/-- **Loops of totally real subspaces deform to Lagrangian loops.** Every loop `Λ` of maximal
totally real subspaces of `ℂⁿ` has the Maslov index of a loop `t ↦ U t ℝⁿ` of Lagrangian
subspaces, for a continuous path `U` of unitary matrices. -/
theorem TotallyRealLoop.exists_unitary_maslovIndex_eq
    (Λ : TotallyRealLoop (EuclideanSpace ℂ n)) :
    ∃ U : I → unitaryGroup n ℂ, Continuous U ∧
      ∃ Λ' : TotallyRealLoop (EuclideanSpace ℂ n),
        (∀ t, Λ' t = (U t : Matrix n n ℂ).realImage) ∧
        Λ'.maslovIndex = Λ.maslovIndex := by
  obtain ⟨L₀, hL₀, A, hAc, hA⟩ := Λ.exists_frame
  obtain ⟨C, hC⟩ := isMaximalTotallyReal_realSubspace.exists_linearEquiv_map_eq hL₀
  -- The frame `t ↦ A t ∘ C` of `Λ`, based at `ℝⁿ`, as a path of invertible matrices.
  let M : I → GL n ℂ := fun t ↦
    GeneralLinearGroup.ofEuclideanCLE (C.toContinuousLinearEquiv.trans (A t))
  have hMc : Continuous M := GeneralLinearGroup.continuous_ofEuclideanCLE <|
    (hAc.clm_comp (continuous_const (y := (C.toContinuousLinearEquiv :
      EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n)))).congr fun _ ↦
        ContinuousLinearEquiv.comp_coe _ _
  have hMΛ (t : I) : (M t : Matrix n n ℂ).realImage = Λ t := by
    rw [GeneralLinearGroup.realImage_ofEuclideanCLE, hA t, ← hC, ← Submodule.map_comp]
    refine congrArg (fun f ↦ (realSubspace n).map f) (LinearMap.ext fun v ↦ ?_)
    simp
  obtain ⟨F, hFc, hF0, hFclosed, hF1⟩ :=
    exists_realImage_homotopy_unitaryGroup hMc (by rw [hMΛ, hMΛ]; exact Λ.toFun_zero_eq_toFun_one)
  have hF1c : Continuous fun t : I ↦ F (1, t) := hFc.comp (Continuous.prodMk_right 1)
  refine ⟨fun t ↦ ⟨F (1, t), hF1 t⟩, (Units.continuous_val.comp hF1c).subtype_mk _,
    TotallyRealLoop.ofRealImage _ hF1c (hFclosed 1),
    TotallyRealLoop.ofRealImage_apply _ hF1c (hFclosed 1),
    (Λ.maslovIndex_eq_of_realImage_homotopy _ F hFc (fun t ↦ ?_)
      (TotallyRealLoop.ofRealImage_apply _ hF1c (hFclosed 1)) hFclosed).symm⟩
  rw [← hMΛ]
  exact (hF0 t).symm

end TauCeti
