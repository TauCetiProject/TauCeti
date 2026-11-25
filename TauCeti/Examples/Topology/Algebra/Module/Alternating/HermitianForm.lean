/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.Alternating.HermitianForm
public import TauCeti.Analysis.InnerProductSpace.TwoDim

/-!
# Examples: the Hermitian form of `dx ∧ dy` on `ℂ`

The area form `ω = dx ∧ dy` of `ℂ`, Mathlib's continuous volume form of the standard orientation
(`Complex.orientation_volumeFormL_apply`), has `ω(1, i) = 1`. Its Hermitian form
`H_ω(v, w) = ω(v, i w) + i·ω(v, w)` is the standard Hermitian product `conj v · w`. Exchanging
the real and imaginary parts, `ω(v, w) + i·ω(v, i w)`, would give the non-real value `i` at
`(1, 1)`.
-/

public section

open Complex ComplexConjugate

namespace TauCeti.HermitianFormExamples

attribute [local instance] Complex.finrank_real_complex_fact

/-- The area form `dx ∧ dy` takes the value one on `(1, i)`. -/
example : Complex.orientation.volumeFormL ![1, I] = 1 :=
  Complex.orientation_volumeFormL_one_I

/-- **The Hermitian form of `dx ∧ dy` is `conj v · w`.** -/
example (v w : ℂ) : Complex.orientation.volumeFormL.hermitianForm v w = conj v * w := by
  apply Complex.ext
  · rw [ContinuousAlternatingMap.re_hermitianForm, Complex.orientation_volumeFormL_apply]
    simp
  · rw [ContinuousAlternatingMap.im_hermitianForm, Complex.orientation_volumeFormL_apply]
    simp

/-- **Exchanging the parts gives a non-real value.** With `ω(v, w)` as the real part and
`ω(v, i w)` as the imaginary part, the value at `(1, 1)` would be `i`. -/
example :
    (⟨Complex.orientation.volumeFormL ![1, 1], Complex.orientation.volumeFormL ![1, I • 1]⟩ :
      ℂ) = I := by
  apply Complex.ext <;> simp only [Complex.orientation_volumeFormL_apply] <;> simp

end TauCeti.HermitianFormExamples
