/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.LinearAlgebra.Complex.Module
import TauCeti.FieldTheory.SquareClassGroup.Real
import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange

/-!
# The Witt index of `⟨1, 1⟩` over `ℝ` and over `ℂ`

The plane `⟨1, 1⟩` is positive definite over `ℝ`, so it is anisotropic and has Witt index `0`.
Over `ℂ` the unit `-1 = i²` is a square, so `⟨1, 1⟩` is the hyperbolic plane and has Witt
index `1`. Complexification therefore raises the Witt index of `⟨1, 1⟩` from `0` to `1`, and the
anisotropic part of the complexification, which is zero, is not the complexification of the
anisotropic part, which is a plane. This is the standard example showing that the hypothesis of
`TauCeti.RegularFormClass.anisotropicPart_baseChange` cannot be dropped, and that the inequality
`TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange` can be strict.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §3 and §4.
-/

namespace TauCeti.RegularFormClass

/-- Over `ℝ`, the positive definite plane `⟨1, 1⟩` is anisotropic, so its Witt index is `0`. -/
example : wittIndex (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩) = 0 := by
  simp

/-- Over `ℂ`, the plane `⟨1, 1⟩` is the hyperbolic plane, because `-1 = i²`, so its Witt index
is `1`. -/
example : wittIndex (Quotient.mk (regularFormSetoid ℂ) ⟨2, ![1, 1]⟩) = 1 :=
  wittIndex_mk_binary_of_isSquare (Units.isSquare_coe_iff.mp ⟨Complex.I, by simp⟩)

/-- **The anisotropic part does not commute with complexification.** The complexification of the
anisotropic real plane `⟨1, 1⟩` is hyperbolic, so its anisotropic part is zero, whereas the
complexification of the anisotropic part of `⟨1, 1⟩` is a plane. -/
example :
    anisotropicPart (baseChange ℂ (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) ≠
      baseChange ℂ (anisotropicPart (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) :=
  anisotropicPart_baseChange_mk_binary_ne (by simp) ⟨Complex.I, by simp⟩

/-- Complexification raises the Witt index of `⟨1, 1⟩` from `0` to `1`. -/
example :
    wittIndex (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩) <
      wittIndex (baseChange ℂ (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) := by
  have h : wittIndex (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩) = 0 := by simp
  rw [h, baseChange_mk, RegularFormPresentation.baseChange_binary,
    wittIndex_mk_binary_of_isSquare (Units.isSquare_coe_iff.mp ⟨Complex.I, by simp⟩)]
  exact zero_lt_one

end TauCeti.RegularFormClass
