/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Burau.Skein
public import TauCeti.KnotTheory.Homfly.Reduced
import TauCeti.KnotTheory.Markov.Skein

/-!
# The Alexander specialization of HOMFLY

The classical, unknot-normalized HOMFLY polynomial specializes at `a = 1` and
`z = s⁻¹ - s` to the normalized Burau Alexander invariant, with Alexander parameter
`s²`. This identifies the determinant algorithm with the Conway skein specialization
for every braid closure, not just for particular knots. It does not require the
geometric Markov theorem.

HOMFLY is stored as a Laurent polynomial in both variables. Consequently its evaluation
requires `z` to be a unit. The comparison is stated for a coefficient homomorphism into
any commutative ring and units `s`, `z` with `z = s⁻¹ - s`; it applies, for example, in the
rational function field at an indeterminate `s`. It does not assert an evaluation of the
Laurent HOMFLY polynomial at `z = 0`.

The proof uses `MarkovBraid.eq_of_skein`: both algorithms have unknot value one,
vanish on adding an uncrossed strand, and satisfy the same oriented skein relation.
The unreduced HOMFLY polynomial cannot be used here: its unknot value vanishes at
`a = 1`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 3, 6 and 8 (HOMFLY and the Conway-normalized Alexander polynomial).
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3 (the Burau Alexander formula).
-/

public section

namespace TauCeti.MarkovBraid

open LaurentPolynomial KnotTheory BraidGroup

variable {K R : Type*} [Field K] [CommRing R]

/-- **The Alexander specialization of HOMFLY.** At `a = 1` and `z = s⁻¹ - s`, the
unknot-normalized HOMFLY polynomial equals the normalized Burau invariant at Alexander
parameter `s²`. The unit `z` permits evaluation of the inner Laurent variable. -/
theorem eval₂_reducedHomfly_eq_normalizedBurauAlexander (β : MarkovBraid)
    (f : K →+* R) (s z : Rˣ) (hz : (z : R) = ((s⁻¹ : Rˣ) : R) - (s : R)) :
    eval₂ (eval₂ f z) 1 (β.reducedHomfly K) = β.normalizedBurauAlexander s := by
  let e : LaurentPolynomial (LaurentPolynomial K) →+* R := eval₂ (eval₂ f z) 1
  have heT (i : ℤ) : e (T i) = 1 := by simp [e]
  have hez : e (C (T 1)) = (z : R) := by simp [e]
  have heU : e (homflyUnknot K) = 0 := by
    simp [homflyUnknot_def, map_mul, map_sub, heT]
  have h := eq_of_skein (R := R) (M := R) 1 (z : R) 0
    (F := fun γ ↦ e (γ.reducedHomfly K)) (G := fun γ ↦ γ.normalizedBurauAlexander s)
    (fun _ _ h ↦ congrArg e (h.reducedHomfly_eq K))
    (fun _ _ h ↦ h.normalizedBurauAlexander_eq s)
    (fun n c i ↦ ?_) (fun n c i ↦ ?_) (fun n b ↦ ?_) (fun n b ↦ ?_) (by simp [e])
  · exact congrFun h β
  · simpa [map_sub, map_mul, heT, hez] using
      congrArg e (reducedHomfly_skein K (1 : BraidGroup (n + 1)) c i)
  · simpa [hz] using normalizedBurauAlexander_skein (1 : BraidGroup (n + 1)) c i s
  · simp only [reducedHomfly_strandIncl, map_mul, heU, zero_mul, zero_smul]
  · simp

end TauCeti.MarkovBraid
