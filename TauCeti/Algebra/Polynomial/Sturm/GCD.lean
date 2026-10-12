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
normalization for its final remainder. It is the algebraic gcd relation used when Sturm sequences
count distinct roots.
-/

public section

namespace TauCeti

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K]

/-- The last entry of a nonempty Sturm sequence divides both input polynomials. -/
theorem getLast?_sturmSeq_dvd {p q s : K[X]}
    (hs : (sturmSeq p q).getLast? = some s) : s ∣ p ∧ s ∣ q := by
  induction p, q using sturmSeq.induct with
  | case1 q =>
      simp at hs
  | case2 p q hp ih =>
      by_cases hq : q = 0
      · subst q
        have hps : p = s := by simpa [sturmSeq_zero_right, hp] using hs
        rw [hps]
        exact ⟨dvd_refl s, dvd_zero s⟩
      · have ht : sturmSeq q (-p % q) ≠ [] := by
          simpa using hq
        obtain ⟨r, rs, hrs⟩ := List.exists_cons_of_ne_nil ht
        have hs' : (sturmSeq q (-p % q)).getLast? = some s := by
          rw [sturmSeq_cons hp, hrs] at hs
          rw [hrs]
          simpa only [List.getLast?_cons_cons] using hs
        obtain ⟨hq', hr⟩ := ih hs'
        exact ⟨by simpa using (EuclideanDomain.dvd_mod_iff hq').mp hr, hq'⟩

/-- The final nonzero remainder is associated to the gcd of the input polynomials. -/
theorem getLast?_sturmSeq_associated_gcd {p q s : K[X]}
    (hs : (sturmSeq p q).getLast? = some s) : Associated s (gcd p q) := by
  obtain ⟨hsp, hsq⟩ := getLast?_sturmSeq_dvd hs
  have hmem : s ∈ sturmSeq p q := by
    exact List.mem_of_mem_getLast? (by rw [hs]; exact Option.mem_some_self s)
  exact gcd_greatest_associated hsp hsq
    (fun _ hep heq => dvd_of_mem_sturmSeq hep heq hmem)

/-- For a nonzero first polynomial, the Sturm sequence has a final entry associated to its gcd
with the second polynomial. -/
theorem exists_getLast?_sturmSeq_associated_gcd {p q : K[X]} (hp : p ≠ 0) :
    ∃ s, (sturmSeq p q).getLast? = some s ∧ Associated s (gcd p q) := by
  have hne : sturmSeq p q ≠ [] := by simpa using hp
  let s := (sturmSeq p q).getLast hne
  have hs : (sturmSeq p q).getLast? = some s :=
    List.getLast?_eq_getLast_of_ne_nil hne
  exact ⟨s, hs, getLast?_sturmSeq_associated_gcd hs⟩

end TauCeti

end
