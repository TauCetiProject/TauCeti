/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Complete orthogonal idempotents spanning a quotient

Let `A` be a `k`-algebra, `J` a two-sided ideal of `A`, and `e : ι → A` a complete family of
orthogonal idempotents whose classes span `A ⧸ J` over `k`, so that `A ⧸ J` is a quotient of a
finite product of copies of `k` (a finite product of copies of `k` itself when `k` is a field).
Then every element `a` of `A` acts on the `j`-th idempotent through a scalar: both
`e j * a` and `a * e j` are congruent to `c • e j` modulo `J` for a single `c : k`.

## Main results

* `CompleteOrthogonalIdempotents.exists_mul_sub_smul_mem`: for every `a` and `j` there is a
  scalar `c` with `e j * a ≡ c • e j ≡ a * e j` modulo `J`.
-/

public section

namespace CompleteOrthogonalIdempotents

variable {k : Type*} {A : Type*} [CommRing k] [Ring A] [Algebra k A]
  {ι : Type*} [Fintype ι] {e : ι → A} {J : Ideal A} [J.IsTwoSided]

/-- If the classes of the `e i` span `A ⧸ J` over `k`, then for every `a` and `j` there is a
scalar `c` with `e j * a ≡ c • e j ≡ a * e j` modulo `J`. -/
theorem exists_mul_sub_smul_mem (he : CompleteOrthogonalIdempotents e)
    (hquot : Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) = ⊤) (a : A)
    (j : ι) : ∃ c : k, e j * a - c • e j ∈ J ∧ a * e j - c • e j ∈ J := by
  classical
  have ha : Ideal.Quotient.mk J a ∈
      Submodule.span k (Set.range fun i ↦ Ideal.Quotient.mk J (e i)) :=
    hquot ▸ Submodule.mem_top
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun k).mp ha
  have hmem : a - ∑ i, c i • e i ∈ J := by
    refine Ideal.Quotient.eq.mp ?_
    rw [← hc, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [← Ideal.Quotient.mkₐ_eq_mk k, map_smul]
  have hl : e j * ∑ i, c i • e i = c j • e j := by
    simp [Finset.mul_sum, he.mul_eq]
  have hr : (∑ i, c i • e i) * e j = c j • e j := by
    simp [Finset.sum_mul, he.mul_eq]
  refine ⟨c j, ?_, ?_⟩
  · rw [← hl, ← mul_sub]
    exact J.mul_mem_left _ hmem
  · rw [← hr, ← sub_mul]
    exact J.mul_mem_right _ hmem

end CompleteOrthogonalIdempotents
