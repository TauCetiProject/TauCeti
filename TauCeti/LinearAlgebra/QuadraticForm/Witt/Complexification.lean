/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import TauCeti.FieldTheory.SquareClassGroup.Real
public import TauCeti.LinearAlgebra.QuadraticForm.Witt.BaseChange

/-!
# The Witt index of `⟨1, 1⟩` over `ℝ` and over `ℂ`

The plane `⟨1, 1⟩` is positive definite over `ℝ`, so it is anisotropic and has Witt index `0`.
Over `ℂ` the unit `-1 = i²` is a square, so `⟨1, 1⟩` is the hyperbolic plane and has Witt
index `1`. Complexification therefore raises the Witt index of `⟨1, 1⟩` from `0` to `1`, and the
anisotropic part of the complexification, which is zero, is not the complexification of the
anisotropic part, which is a plane. This is the standard example showing that the hypothesis of
`TauCeti.RegularFormClass.anisotropicPart_baseChange` cannot be dropped, and that the inequality
`TauCeti.RegularFormClass.wittIndex_le_wittIndex_baseChange` can be strict.

## Main results

* `TauCeti.RegularFormClass.wittIndex_mk_one_one_real`: over `ℝ`, `⟨1, 1⟩` has Witt index `0`.
* `TauCeti.RegularFormClass.wittIndex_mk_one_one_complex`: over `ℂ`, `⟨1, 1⟩` has Witt index `1`.
* `TauCeti.RegularFormClass.anisotropicPart_baseChange_complex_mk_one_one_ne`: the anisotropic
  part of `⟨1, 1⟩` does not commute with complexification.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter I, §3 and §4.
-/

public section

namespace TauCeti.RegularFormClass

/-- Over `ℝ`, the positive definite plane `⟨1, 1⟩` is anisotropic, so its Witt index is `0`. -/
theorem wittIndex_mk_one_one_real :
    wittIndex (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩) = 0 :=
  wittIndex_mk_binary_of_not_isSquare (by simp)

/-- Over `ℂ`, the plane `⟨1, 1⟩` is the hyperbolic plane, because `-1 = i²`, so its Witt index
is `1`. -/
theorem wittIndex_mk_one_one_complex :
    wittIndex (Quotient.mk (regularFormSetoid ℂ) ⟨2, ![1, 1]⟩) = 1 :=
  wittIndex_mk_binary_of_isSquare (Units.isSquare_coe_iff.mp ⟨Complex.I, by simp⟩)

/-- **The anisotropic part does not commute with complexification.** The complexification of the
anisotropic real plane `⟨1, 1⟩` is hyperbolic, so its anisotropic part is zero, whereas the
complexification of the anisotropic part of `⟨1, 1⟩` is a plane. -/
theorem anisotropicPart_baseChange_complex_mk_one_one_ne :
    anisotropicPart (baseChange ℂ (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) ≠
      baseChange ℂ (anisotropicPart (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) :=
  anisotropicPart_baseChange_mk_binary_ne (by simp) ⟨Complex.I, by simp⟩

/-- **Worked example.** Complexification raises the Witt index of `⟨1, 1⟩` from `0` to `1`. -/
example :
    wittIndex (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩) <
      wittIndex (baseChange ℂ (Quotient.mk (regularFormSetoid ℝ) ⟨2, ![1, 1]⟩)) := by
  rw [baseChange_mk_binary, wittIndex_mk_one_one_real]
  simp [wittIndex_mk_one_one_complex]

end TauCeti.RegularFormClass
