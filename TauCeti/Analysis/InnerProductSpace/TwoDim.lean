/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.TwoDim
public import TauCeti.Analysis.InnerProductSpace.Orientation

/-!
# Oriented Euclidean planes

The quarter turn `J = o.rightAngleRotation` of an oriented Euclidean plane carries the first vector
of every positively oriented orthonormal basis `(e₀, e₁)` to the second, `J e₀ = e₁`, and hence
`J e₁ = -e₀`. So in any such basis `J` is the standard quarter turn.

On the complex plane, the continuous oriented volume form is normalized on the standard complex
basis `(1, I)`. On a pair of vectors it is the area form `dx ∧ dy`, `(v, w) ↦ Im (conj v * w)`.
-/

public section

open ComplexConjugate

noncomputable section

namespace Orientation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (Module.finrank ℝ E = 2)]
  (o : Orientation ℝ E (Fin 2)) {b : OrthonormalBasis (Fin 2) ℝ E}

/-- The quarter turn of an oriented plane carries the first vector of a positively oriented
orthonormal basis to the second. -/
theorem rightAngleRotation_basis_zero (hb : b.toBasis.orientation = o) :
    o.rightAngleRotation (b 0) = b 1 := by
  have hω : o.areaForm (b 0) (b 1) = 1 := by
    have h : ![b 0, b 1] = b.toBasis := by
      ext i
      fin_cases i <;> simp
    rw [areaForm_to_volumeForm, o.volumeForm_robust b hb, h, Module.Basis.det_self]
  rw [← b.sum_repr' (o.rightAngleRotation (b 0)), Fin.sum_univ_two]
  simp [inner_rightAngleRotation_right, o.areaForm_swap (b 1), hω]

/-- The quarter turn of an oriented plane carries the second vector of a positively oriented
orthonormal basis to the negative of the first. -/
theorem rightAngleRotation_basis_one (hb : b.toBasis.orientation = o) :
    o.rightAngleRotation (b 1) = -b 0 := by
  rw [← o.rightAngleRotation_basis_zero hb, rightAngleRotation_rightAngleRotation]

end Orientation

namespace Complex

attribute [local instance] Complex.finrank_real_complex_fact

/-- The normalized complex volume form evaluates to one on the basis `(1, I)`. -/
theorem orientation_volumeFormL_one_I :
    Complex.orientation.volumeFormL ![1, I] = 1 := by
  simpa [coe_basisOneI] using
    Complex.orientation.volumeFormL_apply_orthonormal Complex.orthonormalBasisOneI rfl

/-- The continuous volume form of `ℂ` is the area form `dx ∧ dy`: on a pair of vectors `(v, w)` it
is `Im (conj v * w)`. -/
theorem orientation_volumeFormL_apply (v : Fin 2 → ℂ) :
    Complex.orientation.volumeFormL v = (conj (v 0) * v 1).im := by
  rw [Orientation.volumeFormL_apply, ← Complex.areaForm, Orientation.areaForm_to_volumeForm]
  congr 1
  ext i
  fin_cases i <;> rfl

end Complex
