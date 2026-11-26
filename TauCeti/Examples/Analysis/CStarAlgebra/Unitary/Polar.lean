/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Unitary.Polar

/-!
# The polar unitary of an invertible complex number

For an invertible element `x` of a unital C⋆-algebra, `Units.polarUnitary x` is the unitary factor
of the polar decomposition `x = u |x|`; by `Units.joined_polarUnitary`
(`TauCeti/Analysis/CStarAlgebra/Unitary/Polar.lean`) it is joined to `x` through invertible
elements. This file checks the simplest case: the polar unitary of the invertible `2 ∈ ℂ` is `1`
(`TauCeti.polarUnitary_two_complex`).
-/

public section

namespace TauCeti

open scoped ComplexOrder in
/-- The polar unitary of the invertible `2 ∈ ℂ` is `1`. -/
theorem polarUnitary_two_complex : (Units.mk0 (2 : ℂ) two_ne_zero).polarUnitary = 1 :=
  Units.polarUnitary_eq_one (by norm_num)

end TauCeti
