/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Regular.DSequence
public import Mathlib.Algebra.Field.Rat

/-!
# Examples of d-sequences

A d-sequence need not be weakly regular: `[0]` is a d-sequence on `ℚ`, since multiplication by `0`
only has to be injective on `0 · ℚ = 0`. The order of the entries matters: `[2, 0]` is a
d-sequence on `ℤ`, because `2` is injective on `2ℤ` and `(2, 0) · ℤ/2 = 0`, while `[0, 2]` is not,
because multiplication by `0` is not injective on `(0, 2) ℤ = 2ℤ`.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  Definition 3.8.
-/

public section

namespace TauCeti.Examples.DSequence

open RingTheory.Sequence Ideal

open scoped Pointwise

/-- `[0]` is a d-sequence on `ℚ`. -/
theorem isDSequence_zero_rat : IsDSequence ℚ [(0 : ℚ)] := by
  rw [isDSequence_singleton_iff]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ -
  obtain ⟨a, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hx
  obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hy
  simp

/-- `[0]` is not weakly regular on `ℚ`. -/
theorem not_isWeaklyRegular_zero_rat : ¬ IsWeaklyRegular ℚ [(0 : ℚ)] := by
  rw [isWeaklyRegular_cons_iff]
  rintro ⟨h, -⟩
  exact one_ne_zero (h (by simp : (0 : ℚ) • (1 : ℚ) = (0 : ℚ) • 0))

/-- `[2, 0]` is a d-sequence on `ℤ`. -/
theorem isDSequence_two_zero : IsDSequence ℤ [(2 : ℤ), 0] := by
  refine isDSequence_iff_smul_mem.mpr fun i hi x hx hrx => ?_
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i
  · simp_all
  · simpa [ofList_cons, span_singleton_eq_bot.mpr rfl] using hx

/-- `[0, 2]` is not a d-sequence on `ℤ`. -/
theorem not_isDSequence_zero_two : ¬ IsDSequence ℤ [(0 : ℤ), 2] := by
  intro h
  have h2 : (2 : ℤ) ∈ (ofList [(0 : ℤ), 2] • ⊤ : Submodule ℤ ℤ) := by simp
  have := h.mem_of_smul_mem (i := 0) (by simp) h2 (by simp)
  simp at this

end TauCeti.Examples.DSequence
