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

Natural numbers `f i`, `i ∈ s`, have greatest common divisor `1` in `ℕ` if and only if some
integer combination of them is `1`. Mathlib's `Finset.gcd_eq_sum_mul` gives the forward direction
for the gcd computed in `ℤ`; this file transfers it to the gcd in `ℕ`, where the hypothesis is
usually established, for instance by `Finset.gcd_div_eq_one`.

## Main results

* `Finset.gcd_eq_one_iff_exists_sum_natCast_mul_eq_one`: `s.gcd f = 1` in `ℕ` if and only if
  `∑ i ∈ s, f i * c i = 1` for some `c : ι → ℤ`.
-/

public section

namespace Finset

/-- Bézout's identity for natural numbers: `f i`, `i ∈ s`, have greatest common divisor `1` if
and only if some integer combination `∑ i ∈ s, f i * c i` is `1`. -/
theorem gcd_eq_one_iff_exists_sum_natCast_mul_eq_one {ι : Type*} {s : Finset ι} {f : ι → ℕ} :
    s.gcd f = 1 ↔ ∃ c : ι → ℤ, ∑ i ∈ s, (f i : ℤ) * c i = 1 := by
  refine ⟨fun h => ?_, fun ⟨c, hc⟩ => ?_⟩
  · obtain ⟨c, hc⟩ := s.gcd_eq_sum_mul fun i => (f i : ℤ)
    refine ⟨c, hc ▸ Int.eq_one_of_dvd_one Int.finsetGcd_nonneg ?_⟩
    -- The gcd in `ℤ` divides every `f i`, hence also their gcd `1` in `ℕ`.
    rw [← Nat.cast_one, ← h]
    exact Int.dvd_natCast.2 <| Finset.dvd_gcd fun i hi => Int.dvd_natCast.1 (Finset.gcd_dvd hi)
  · -- The gcd in `ℕ` divides every `f i`, hence also the combination `1`.
    refine Nat.dvd_one.1 <| Int.natCast_dvd_natCast.1 ?_
    rw [Nat.cast_one, ← hc]
    exact Finset.dvd_sum fun i hi => (Int.natCast_dvd_natCast.2 (Finset.gcd_dvd hi)).mul_right _

end Finset
