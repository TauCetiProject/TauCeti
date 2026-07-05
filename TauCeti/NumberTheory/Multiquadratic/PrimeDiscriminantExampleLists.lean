/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.NumberTheory.Multiquadratic.PrimeDiscriminants

/-!
# Prime-discriminant lists for the first genus-field examples

The multiquadratic roadmap's genus-field worked examples use the prime-discriminant lists
`[-4, 5]` for `ℚ(√-5)` and `[-4, -3, -7]` for `ℚ(√-21)`. This file gives those shared lists
a neutral home for the Legendre-character, degree, and Galois worked examples.
-/

public section

namespace TauCeti.Multiquadratic

/-- The prime-discriminant list `[-4, 5]` for the genus-field generators of `ℚ(√-5)`. -/
abbrev negFourFivePrimeDiscriminants : Fin 2 → ℤ :=
  ![(-4 : ℤ), 5]

/-- The prime-discriminant list `[-4, -3, -7]` for the genus-field generators of
`ℚ(√-21)`. -/
abbrev negFourNegThreeNegSevenPrimeDiscriminants : Fin 3 → ℤ :=
  ![(-4 : ℤ), -3, -7]

end TauCeti.Multiquadratic
