/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.VonMangoldt

/-!
# Conjugation of arithmetic weights on ideals

Passing from a weight to an ideal arithmetic function commutes with conjugation. So does taking
the von Mangoldt transform, which gives the coefficients for the negative logarithmic derivative
of a multiplicatively weighted L-series.
-/

public section

namespace TauCeti

variable {K : Type*} [Field K] [NumberField K]

/-- The ideal arithmetic function of a conjugate weight is the pointwise conjugate. -/
@[simp]
theorem MultiplicativeIdealWeight.toIdealArithmeticFunction_conj (χ : MultiplicativeIdealWeight K) :
    χ.conj.toIdealArithmeticFunction = star χ.toIdealArithmeticFunction := by
  funext I
  simp [MultiplicativeIdealWeight.toIdealArithmeticFunction_apply]

/-- The von Mangoldt transform commutes with coefficientwise conjugation. -/
@[simp]
theorem IdealArithmeticFunction.vonMangoldtTransform_star (f : IdealArithmeticFunction K) :
    (star f).vonMangoldtTransform = star f.vonMangoldtTransform := by
  funext I
  have hreal : star (IdealArithmeticFunction.vonMangoldt I) =
      IdealArithmeticFunction.vonMangoldt I :=
    Complex.conj_eq_iff_im.mpr IdealArithmeticFunction.vonMangoldt_im
  simp only [IdealArithmeticFunction.vonMangoldtTransform_apply, Pi.star_apply, star_mul', hreal]

end TauCeti
