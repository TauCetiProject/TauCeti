/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.BilinearForm
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Topology.Instances.Matrix

/-!
# Matrices as continuous bilinear forms

A square matrix `M` over a complete nontrivially normed field `𝕜` gives the continuous bilinear
form `(x, y) ↦ x ⬝ᵥ M *ᵥ y` on `n → 𝕜` (`Matrix.toContinuousLinearMap₂'`), the continuous version
of Mathlib's `Matrix.toLinearMap₂'`. This file records its kernel, symmetry and nondegeneracy in
terms of the matrix, and that a path of matrices with entrywise derivatives gives a path of
continuous bilinear forms with the corresponding derivative, so that the signature theory of paths
of continuous bilinear forms applies to paths of matrices.

## Main definitions

* `Matrix.toContinuousLinearMap₂'`: the continuous bilinear form of a square matrix.

## Main results

* `Matrix.ker_toContinuousLinearMap₂'`: the kernel of the bilinear form of `M` is the kernel of
  `Mᵀ`.
* `Matrix.nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero`: the bilinear form
  of `M` is nondegenerate exactly when `M` is invertible.
* `Matrix.hasDerivWithinAt_toContinuousLinearMap₂'`: entrywise derivatives of a path of matrices
  give the derivative of its bilinear forms.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

section ContinuousBilinearForm

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]

/-- The continuous bilinear form `(x, y) ↦ x ⬝ᵥ M *ᵥ y` on `n → 𝕜` of a square matrix `M`. -/
noncomputable def toContinuousLinearMap₂' (M : Matrix n n 𝕜) :
    (n → 𝕜) →L[𝕜] (n → 𝕜) →L[𝕜] 𝕜 :=
  (toLinearMap₂' 𝕜 M).toContinuousBilinearMap

@[simp]
theorem toContinuousLinearMap₂'_apply (M : Matrix n n 𝕜) (x y : n → 𝕜) :
    M.toContinuousLinearMap₂' x y = x ⬝ᵥ M *ᵥ y := by
  simp [toContinuousLinearMap₂', toLinearMap₂'_apply']

/-- Forgetting continuity of the bilinear form of `M` gives `Matrix.toLinearMap₂'`. -/
@[simp]
theorem toBilinForm_toContinuousLinearMap₂' (M : Matrix n n 𝕜) :
    M.toContinuousLinearMap₂'.toBilinForm = toLinearMap₂' 𝕜 M :=
  LinearMap.BilinForm.toBilinForm_toContinuousBilinearMap _

/-- The quadratic form of the bilinear form of `M` is `Matrix.toQuadraticForm'`. -/
theorem toQuadraticMap_toBilinForm_toContinuousLinearMap₂' (M : Matrix n n 𝕜) :
    M.toContinuousLinearMap₂'.toBilinForm.toQuadraticMap = M.toQuadraticForm' := by
  rw [toBilinForm_toContinuousLinearMap₂']
  -- `Matrix.toQuadraticForm'` is by definition the quadratic map of `Matrix.toLinearMap₂'`.
  rfl

/-- The bilinear form of `M` is nondegenerate exactly when `M` is invertible. -/
theorem nondegenerate_toBilinForm_toContinuousLinearMap₂'_iff_det_ne_zero (M : Matrix n n 𝕜) :
    M.toContinuousLinearMap₂'.toBilinForm.Nondegenerate ↔ M.det ≠ 0 := by
  rw [toBilinForm_toContinuousLinearMap₂']
  exact LinearMap.nondegenerate_toLinearMap₂'_iff_det_ne_zero

/-- The bilinear form of a symmetric matrix is symmetric. -/
theorem isSymm_toBilinForm_toContinuousLinearMap₂' {M : Matrix n n 𝕜} (hM : M.IsSymm) :
    M.toContinuousLinearMap₂'.toBilinForm.IsSymm := by
  refine ⟨fun x y ↦ ?_⟩
  simp only [ContinuousLinearMap.toBilinForm_apply, toContinuousLinearMap₂'_apply]
  rw [dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

/-- The kernel of the bilinear form of `M`, the vectors `x` with `x ⬝ᵥ M *ᵥ y = 0` for all `y`, is
the kernel of `Mᵀ`. -/
theorem ker_toContinuousLinearMap₂' (M : Matrix n n 𝕜) :
    M.toContinuousLinearMap₂'.ker = LinearMap.ker Mᵀ.mulVecLin := by
  have hxy (x y : n → 𝕜) : M.toContinuousLinearMap₂' x y = (Mᵀ *ᵥ x) ⬝ᵥ y := by
    rw [toContinuousLinearMap₂'_apply, dotProduct_mulVec, ← mulVec_transpose]
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker, mulVecLin_apply, ContinuousLinearMap.coe_coe]
  constructor
  · intro h
    funext i
    have hi : M.toContinuousLinearMap₂' x (Pi.single i 1) = 0 := by simp [h]
    rwa [hxy, dotProduct_single, mul_one] at hi
  · intro h
    ext y
    simp [hxy, h]

/-- The bilinear forms of matrices, as a continuous linear map on the entries. -/
private noncomputable def toContinuousLinearMap₂'CLM :
    (n → n → 𝕜) →L[𝕜] (n → 𝕜) →L[𝕜] (n → 𝕜) →L[𝕜] 𝕜 :=
  -- The domain and codomain are given so that the continuity instances can be found.
  LinearMap.toContinuousLinearMap (E := n → n → 𝕜) (F' := (n → 𝕜) →L[𝕜] (n → 𝕜) →L[𝕜] 𝕜)
    { toFun M := (of M).toContinuousLinearMap₂'
      map_add' M N := by
        ext x y
        simp [← of_add_of, add_mulVec, dotProduct_add]
      map_smul' c M := by
        ext x y
        simp [← smul_of, smul_mulVec, dotProduct_smul] }

/-- Entrywise derivatives of a path of matrices give the derivative of its bilinear forms. -/
theorem hasDerivWithinAt_toContinuousLinearMap₂' {A : 𝕜 → Matrix n n 𝕜} {A' : Matrix n n 𝕜}
    {s : Set 𝕜} {t : 𝕜} (h : ∀ i j, HasDerivWithinAt (fun r ↦ A r i j) (A' i j) s t) :
    HasDerivWithinAt (fun r ↦ (A r).toContinuousLinearMap₂') A'.toContinuousLinearMap₂' s t := by
  have hA : HasDerivWithinAt (fun r ↦ of.symm (A r)) (of.symm A') s t :=
    hasDerivWithinAt_pi.2 fun i ↦ hasDerivWithinAt_pi.2 fun j ↦ h i j
  -- The target space is given so that its normed instances can be found.
  exact HasFDerivAt.comp_hasDerivWithinAt (E := (n → 𝕜) →L[𝕜] (n → 𝕜) →L[𝕜] 𝕜) t
    toContinuousLinearMap₂'CLM.hasFDerivAt hA

/-- A continuous path of matrices gives a continuous path of bilinear forms. -/
theorem continuousOn_toContinuousLinearMap₂' {X : Type*} [TopologicalSpace X]
    {A : X → Matrix n n 𝕜} {s : Set X} (hA : ContinuousOn A s) :
    ContinuousOn (fun r ↦ (A r).toContinuousLinearMap₂') s := by
  have h : ContinuousOn (fun r ↦ of.symm (A r)) s :=
    continuousOn_pi.2 fun i ↦ continuousOn_pi.2 fun j ↦
      (continuous_id.matrix_elem i j).comp_continuousOn hA
  exact toContinuousLinearMap₂'CLM.continuous.comp_continuousOn h

end ContinuousBilinearForm

end Matrix
