/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.ContinuousBilinearForm
public import TauCeti.Analysis.Matrix.HermitianSignature.Crossing

/-!
# Crossing forms of matrices

The *crossing form* of a matrix `A` and a matrix `A'` (`Matrix.crossingForm`) is the quadratic
form `x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a real symmetric `A` it is isometric
to the crossing form `ContinuousLinearMap.crossingForm` of the corresponding continuous bilinear
forms `Matrix.toContinuousLinearMap₂'` (`Matrix.crossingFormIsometryEquiv`), so that the
signature theory of paths of continuous bilinear forms at their crossings applies to paths of
matrices.

## Main definitions

* `Matrix.crossingForm`: the quadratic form of `A'` on the kernel of `A`.
* `Matrix.crossingFormIsometryEquiv`: for real symmetric `A`, the crossing form of the bilinear
  forms of `A` and `A'` is isometric to the crossing form of `A` and `A'`.
-/

public section

namespace Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ### Crossing forms of matrices -/

/-- The **crossing form** of a square matrix `A` and a matrix `A'`: the quadratic form
`x ↦ x ⬝ᵥ A' *ᵥ x` restricted to the kernel of `A`. For a path of symmetric matrices `A` with
derivative `A'` at a parameter where `A` is singular, it is the crossing form of Robbin and Salamon
of the path of graphs `{x + i A x}` relative to `ℝⁿ`. -/
noncomputable def crossingForm {R : Type*} [CommRing R] (A A' : Matrix n n R) :
    QuadraticForm R (LinearMap.ker A.mulVecLin) :=
  A'.toQuadraticForm'.restrict (LinearMap.ker A.mulVecLin)

@[simp]
theorem crossingForm_apply {R : Type*} [CommRing R] (A A' : Matrix n n R)
    (x : LinearMap.ker A.mulVecLin) : crossingForm A A' x = (x : n → R) ⬝ᵥ A' *ᵥ x := by
  simp [crossingForm, toQuadraticForm', toLinearMap₂'_apply']

/-- For a real symmetric matrix `A`, the crossing form of the bilinear forms of `A` and `A'` is
the crossing form of `A` and `A'`, read on the same kernel. -/
noncomputable def crossingFormIsometryEquiv {A : Matrix n n ℝ} (hA : A.IsSymm)
    (A' : Matrix n n ℝ) :
    (ContinuousLinearMap.crossingForm A.toContinuousLinearMap₂'
      A'.toContinuousLinearMap₂').IsometryEquiv (crossingForm A A') :=
  ⟨LinearEquiv.ofEq _ _ (by rw [ker_toContinuousLinearMap₂', hA.eq]), fun v ↦ by simp⟩

end Matrix
