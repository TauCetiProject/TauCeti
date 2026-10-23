/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Int.Cast.Basic
-- Proof-only: Bézout's identity for `Finset.gcd` over the Euclidean domain `ℤ`.
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Bézout's identity for a finite family of natural numbers

If natural numbers `f i`, `i ∈ s`, have greatest common divisor `1` in `ℕ`, then some integer
combination of them is `1`. Mathlib's `Finset.gcd_eq_sum_mul` gives this for the gcd computed in
`ℤ`; this file transfers the hypothesis from `ℕ`, where it is usually established, for instance
by `Finset.gcd_div_eq_one`.

## Main results

* `Finset.exists_sum_natCast_mul_eq_one_of_gcd_eq_one`: if `s.gcd f = 1` in `ℕ`, then
  `∑ i ∈ s, f i * c i = 1` for some `c : ι → ℤ`.
-/

public section

namespace Finset

/-- Bézout's identity for natural numbers: if `f i`, `i ∈ s`, have greatest common divisor `1`,
then some integer combination `∑ i ∈ s, f i * c i` is `1`. -/
theorem exists_sum_natCast_mul_eq_one_of_gcd_eq_one {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : s.gcd f = 1) : ∃ c : ι → ℤ, ∑ i ∈ s, (f i : ℤ) * c i = 1 := by
  obtain ⟨c, hc⟩ := s.gcd_eq_sum_mul fun i => (f i : ℤ)
  refine ⟨c, ?_⟩
  rw [← hc]
  have hdvd : (s.gcd fun i => (f i : ℤ)).natAbs ∣ 1 := by
    rw [← h]
    refine Finset.dvd_gcd fun i hi => ?_
    rw [← Int.natAbs_natCast (f i)]
    exact Int.natAbs_dvd_natAbs.2 (Finset.gcd_dvd hi)
  rw [← Int.natAbs_of_nonneg Int.finsetGcd_nonneg, Nat.dvd_one.1 hdvd, Nat.cast_one]

end Finset
