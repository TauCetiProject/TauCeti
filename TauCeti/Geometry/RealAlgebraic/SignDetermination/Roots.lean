/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import TauCeti.Geometry.RealAlgebraic.SignDetermination.Polynomial

/-! # Sign determination at polynomial roots

`tarskiQuery p q` sums the signs of `q` at the distinct roots of `p`.
For nonzero `p`, these are precisely its zeros in the coefficient ring.
For `p = 0`, the query is defined to be zero; it does not describe the infinite zero set.
`tarskiQuery_eq_sum_signCount` is the BKR matrix identity at polynomial roots;
`fullInverse_mulVec_tarskiQuery` recovers the number of distinct roots
realizing each sign condition.
These identities hold over any compatibly ordered commutative ring; no real-closed-field
hypothesis is required.

## References

For Tarski queries and their use in sign determination, see S. Basu, R. Pollack,
and M.-F. Roy, [Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 10. The sign-matrix method originates with M. Ben-Or,
D. Kozen, and J. Reif, “The complexity of elementary algebra and geometry”,
Journal of Computer and System Sciences 32 (1986), 251–264.
-/

public section

open SignType Finset TauCeti.SignDetermination
open scoped Matrix

namespace Polynomial


section Moments

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]

/-- The sign-matrix identity for Tarski queries at distinct polynomial roots. -/
theorem tarskiQuery_eq_sum_signCount {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) (e : J → ℕ) :
    tarskiQuery p (∏ j, Q j ^ e j) =
      ∑ σ : J → SignType, (∏ j, (σ j : ℤ) ^ e j) *
        (signCount p.roots.toFinset Q σ : ℤ) := by
  rw [tarskiQuery_eq_signSum, signSum_eq_sum_signCount]

/-- Inverting the full matrix of Tarski queries counts distinct roots for each sign condition. -/
theorem fullInverse_mulVec_tarskiQuery {J : Type*} [Fintype J] [DecidableEq J]
    (p : R[X]) (Q : J → R[X]) :
    fullInverse J *ᵥ (fun e => (tarskiQuery p (∏ j, Q j ^ (e j).val) : ℚ)) =
      fun σ => (signCount p.roots.toFinset Q σ : ℚ) := by
  simp only [tarskiQuery_eq_signSum, fullInverse_mulVec_signSum]

end Moments

end Polynomial
