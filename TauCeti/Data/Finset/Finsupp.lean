/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Finsupp
public import Mathlib.Data.PNat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Weighted antidiagonals of finitely supported functions

For a finite set `s : Finset ι`, positive weights `m : ι → ℕ+`, and a target weight `n : ℕ`,
`Finset.weightedFinsuppAntidiag s m n` is the finite set of finitely supported functions
`l : ι →₀ ℕ` supported in `s` with weighted sum `∑ c ∈ s, m c * l c = n`.

This generalizes the unweighted `Finset.finsuppAntidiag` to positive integer weights, enumerating
both weighted monomials in a graded algebra and configurations of weighted power series expansions.

## Main declarations

* `Finset.weightedFinsuppAntidiag`: the finset of `l : ι →₀ ℕ` supported in `s` with
  `∑ c ∈ s, m c * l c = n`.
* `Finset.mem_weightedFinsuppAntidiag`: membership characterization for the weighted antidiagonal.
* `Finset.mul_le_of_mem_weightedFinsuppAntidiag`: each weighted coordinate `m c * l c` is at most
  `n`.
-/

public section

variable {ι : Type*}

namespace Finset

/-- The weighted antidiagonal: the assignments `l : ι →₀ ℕ` supported in `s` with
`∑ c ∈ s, m c * l c = n`. -/
noncomputable def weightedFinsuppAntidiag (s : Finset ι) (m : ι → ℕ+) (n : ℕ) :
    Finset (ι →₀ ℕ) :=
  {l ∈ s.finsupp fun _ ↦ range (n + 1) | ∑ c ∈ s, (m c : ℕ) * l c = n}

/-- A summand of `∑ c ∈ s, m c * l c = n` is at most `n`. -/
private theorem mul_le_of_sum_mul_eq {s : Finset ι} {m : ι → ℕ+} {n : ℕ} {l : ι →₀ ℕ}
    (h : ∑ c ∈ s, (m c : ℕ) * l c = n) {c : ι} (hc : c ∈ s) : (m c : ℕ) * l c ≤ n :=
  h ▸ single_le_sum (f := fun c ↦ (m c : ℕ) * l c) (by simp) hc

/-- An assignment lies in the weighted antidiagonal exactly when it is supported in `s` and has
weighted sum `n`. -/
@[simp]
theorem mem_weightedFinsuppAntidiag {s : Finset ι} {m : ι → ℕ+} {n : ℕ} {l : ι →₀ ℕ} :
    l ∈ s.weightedFinsuppAntidiag m n ↔ l.support ⊆ s ∧ ∑ c ∈ s, (m c : ℕ) * l c = n := by
  simp only [weightedFinsuppAntidiag, mem_filter, mem_finsupp_iff, mem_range]
  refine ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦ ⟨⟨h.1, fun c hc ↦ ?_⟩, h.2⟩⟩
  have hle := mul_le_of_sum_mul_eq h.2 hc
  have := Nat.le_mul_of_pos_left (l c) (m c).pos
  omega

/-- Every summand `m c * l c` of an element `l` of the weighted antidiagonal is at most `n`. -/
theorem mul_le_of_mem_weightedFinsuppAntidiag {s : Finset ι} {m : ι → ℕ+} {n : ℕ}
    {l : ι →₀ ℕ} (hl : l ∈ s.weightedFinsuppAntidiag m n) (c : ι) :
    (m c : ℕ) * l c ≤ n := by
  obtain ⟨hsupp, hsum⟩ := mem_weightedFinsuppAntidiag.1 hl
  by_cases hc : c ∈ s
  · exact mul_le_of_sum_mul_eq hsum hc
  · simp [Finsupp.notMem_support_iff.1 fun h ↦ hc (hsupp h)]

end Finset
