/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric.Basic

/-!
# Differentiation of the regularized Kummer function

The regularized confluent hypergeometric function is
`Complex.regularizedHGFun {a} {b} z`. Its derivative shifts both parameters by one
and multiplies by `a`. Unlike the unregularized formula, this identity holds for
all lower parameters, including the poles of Gamma. It supplies the derivatives
needed for Kummer's and Weber's differential equations. We specialize the general
multiset-parameter derivative formula from `RegularizedHypergeometric.Basic`.

## References

* NIST Digital Library of Mathematical Functions, §13.3, equation 13.3.15,
  divided by `Γ(b)`, <https://dlmf.nist.gov/13.3#E15>.
-/

public section

noncomputable section

namespace Complex

/-- The derivative of the regularized Kummer function, valid at every parameter
(DLMF 13.3.15 after division by `Γ(b)`). -/
theorem hasDerivAt_regularizedHGFun_singleton (a b z : ℂ) :
    HasDerivAt (regularizedHGFun {a} {b})
      (a * regularizedHGFun {a + 1} {b + 1} z) z := by
  simpa using hasDerivAt_regularizedHGFun (a := {a}) (b := {b}) (by simp) z

/-- The derivative of the regularized Kummer function, as a function. -/
theorem deriv_regularizedHGFun_singleton (a b : ℂ) :
    deriv (regularizedHGFun {a} {b}) =
      fun z => a * regularizedHGFun {a + 1} {b + 1} z :=
  funext fun z => (hasDerivAt_regularizedHGFun_singleton a b z).deriv

end Complex
