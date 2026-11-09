/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Sturm.Sequence
public import Mathlib.RingTheory.Polynomial.Content

/-!
# The last polynomial in a Sturm sequence

For a nonzero first polynomial, the signed Euclidean remainder sequence ends at a greatest common
divisor of its first two polynomials, up to a nonzero scalar. This identifies the common roots
retained by the sequence, including when the second polynomial is zero, without choosing a
normalization for its final remainder. This is the algebraic gcd relation behind counting distinct
roots with Sturm sequences.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The last entry of a nonempty Sturm sequence divides both input polynomials. -/
theorem getLast?_sturmSeq_dvd {p q s : K[X]}
    (hs : (sturmSeq p q).getLast? = some s) : s ∣ p ∧ s ∣ q := by
  induction p, q using sturmSeq.induct with
  | case1 q => simp at hs
  | case2 p q hp ih =>
    rw [sturmSeq_cons hp, List.getLast?_cons] at hs
    cases ht : (sturmSeq q (-p % q)).getLast? with
    | none => simp_all
    | some t =>
      obtain rfl : t = s := by simpa [ht] using hs
      obtain ⟨hq, hr⟩ := ih ht
      exact ⟨by simpa using (EuclideanDomain.dvd_mod_iff hq).mp hr, hq⟩

/-- The final nonzero remainder is associated to the gcd of the input polynomials. -/
theorem getLast?_sturmSeq_associated_gcd {p q s : K[X]}
    (hs : (sturmSeq p q).getLast? = some s) : Associated s (gcd p q) := by
  obtain ⟨hsp, hsq⟩ := getLast?_sturmSeq_dvd hs
  exact gcd_greatest_associated hsp hsq fun _ hdp hdq =>
    dvd_of_mem_sturmSeq hdp hdq (List.mem_of_getLast? hs)

/-- For a nonzero first polynomial, the Sturm sequence has a final entry associated to its gcd
with the second polynomial. -/
theorem exists_getLast?_sturmSeq_associated_gcd {p q : K[X]} (hp : p ≠ 0) :
    ∃ s, (sturmSeq p q).getLast? = some s ∧ Associated s (gcd p q) := by
  have hne : (sturmSeq p q).getLast? ≠ none := by simpa using hp
  obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp hne
  exact ⟨s, hs, getLast?_sturmSeq_associated_gcd hs⟩

end TauCeti

end
