/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Div

/-!
# Clearing a common power of `X` from a family of polynomials

Given a family of polynomials that is not identically zero, the least exponent occurring
with a nonzero coefficient across the family is the largest power of `X` dividing every member.
Dividing by that power leaves at least one polynomial with nonzero constant term. The family
may be infinite: the least exponent exists by well-ordering of the natural numbers.

This elementary polynomial result is used in two function-field linear-independence arguments:
Stichtenoth, *Algebraic Function Fields and Codes*, Lemma 1.1.7 and Proposition 1.1.15.

## Main results

* `TauCeti.Polynomial.exists_common_X_pow_factor`: a family of polynomials, not all zero, is
  `X ^ m` times a family in which some member has nonzero constant term.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Lemma 1.1.7 and Proposition 1.1.15.
-/

public section

open Polynomial

namespace TauCeti

universe u

variable {k : Type u} [Semiring k]

namespace Polynomial

/-- Dividing a family of polynomials, not all zero, by the largest common power of `X`
leaves at least one quotient with nonzero constant term. The exponent is the least index carrying
a nonzero coefficient across the family. -/
theorem exists_common_X_pow_factor {ι : Type*} (s : Set ι) (p : ι → k[X])
    (hne : ∃ i ∈ s, p i ≠ 0) :
    ∃ m, ∃ q : ι → k[X], (∀ i ∈ s, p i = X ^ m * q i) ∧
      ∃ j ∈ s, (q j).coeff 0 ≠ 0 := by
  classical
  have hex : ∃ d, ∃ i ∈ s, (p i).coeff d ≠ 0 := by
    obtain ⟨i, hi, hpi⟩ := hne
    obtain ⟨d, hd⟩ := Polynomial.support_nonempty.mpr hpi
    exact ⟨d, i, hi, Polynomial.mem_support_iff.mp hd⟩
  let m := Nat.find hex
  obtain ⟨j, hjs, hjm⟩ := Nat.find_spec hex
  have hdvd : ∀ i ∈ s, (X : k[X]) ^ m ∣ p i := by
    intro i hi
    rw [X_pow_dvd_iff]
    intro d hd
    by_contra hcoeff
    exact Nat.find_min hex hd ⟨i, hi, hcoeff⟩
  let q : ι → k[X] := fun i ↦ if hi : i ∈ s then Classical.choose (hdvd i hi) else 0
  have hfactor : ∀ i ∈ s, p i = (X : k[X]) ^ m * q i := by
    intro i hi
    simpa [q, hi] using Classical.choose_spec (hdvd i hi)
  refine ⟨m, q, hfactor, j, hjs, ?_⟩
  have hjcoeff : (p j).coeff m ≠ 0 := by simpa using hjm
  have hcoeff := congrArg (fun r : k[X] ↦ r.coeff m) (hfactor j hjs)
  have hcoeff' : (p j).coeff m = (q j).coeff 0 := hcoeff.trans <| by
    simpa using coeff_X_pow_mul (q j) m 0
  exact fun hq ↦ hjcoeff (hcoeff'.trans hq)

end Polynomial

end TauCeti
