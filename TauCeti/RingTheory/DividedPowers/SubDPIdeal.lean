/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DividedPowers.SubDPIdeal

/-!
# Sub-dp-ideals

This file supplements `Mathlib.RingTheory.DividedPowers.SubDPIdeal` with stability of positive
ordinary powers of a divided power ideal and a span-induction criterion for divided powers in
multiplicative ideal families.

## Main results

* `DividedPowers.isSubDPIdeal_pow`: every positive power `I ^ e` (`e ≠ 0`) of a divided power
  ideal `(I, hI)` is a sub-dp-ideal of `(I, hI)`.
* `DividedPowers.dpow_mem_of_mem_span_of_mul_le`: if `A : ℕ → Ideal R` satisfies `A 0 = ⊤` and
  `A i * A j ≤ A (i + j)`, and `hI.dpow k s ∈ A k` on a generating set `S ⊆ I`, then
  `hI.dpow k x ∈ A k` for all `x ∈ Ideal.span S`.
-/

public section

namespace DividedPowers

/-- Every positive power `I ^ e` (`e ≠ 0`) of a divided power ideal `(I, hI)` is a sub-dp-ideal
of `(I, hI)`. -/
theorem isSubDPIdeal_pow {A : Type*} [CommSemiring A] {I : Ideal A} (hI : DividedPowers I)
    {e : ℕ} (he : e ≠ 0) : hI.IsSubDPIdeal (I ^ e) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  simpa [SubDPIdeal.prod, smul_eq_mul, ← pow_succ'] using
    (SubDPIdeal.prod (hI := hI) (I ^ k)).toIsSubDPIdeal

/-- If `A : ℕ → Ideal R` satisfies `A 0 = ⊤` and `A i * A j ≤ A (i + j)`, and
`hI.dpow k s ∈ A k` for all `k` and all generators `s ∈ S ⊆ I`, then `hI.dpow k x ∈ A k`
for all `x ∈ Ideal.span S`. -/
theorem dpow_mem_of_mem_span_of_mul_le {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : DividedPowers I) {A : ℕ → Ideal R} (hA0 : A 0 = ⊤)
    (hAmul : ∀ i j, A i * A j ≤ A (i + j)) {S : Set R} (hSI : S ⊆ (I : Set R))
    (hgen : ∀ s ∈ S, ∀ k : ℕ, hI.dpow k s ∈ A k) {x : R} (hx : x ∈ Ideal.span S) (k : ℕ) :
    hI.dpow k x ∈ A k := by
  have hspanI : Ideal.span S ≤ I := Ideal.span_le.mpr hSI
  revert k
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
  · exact fun s hs k ↦ hgen s hs k
  · intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [hI.dpow_zero I.zero_mem, hA0]
      exact Submodule.mem_top
    · rw [hI.dpow_eval_zero hk]
      exact Ideal.zero_mem _
  · intro a b ha hb iha ihb k
    rw [hI.dpow_add (hspanI ha) (hspanI hb)]
    refine Submodule.sum_mem _ fun p hp ↦ ?_
    rw [← Finset.mem_antidiagonal.mp hp]
    exact hAmul p.1 p.2 (Ideal.mul_mem_mul (iha p.1) (ihb p.2))
  · intro c a ha iha k
    rw [smul_eq_mul, hI.dpow_mul (hspanI ha)]
    exact (A k).mul_mem_left (c ^ k) (iha k)

end DividedPowers
