/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.StableRange.Relative

/-!
# Examples of relative unimodular vectors

At level `2ℤ` in `ℤ³`, the two conditions defining `Ideal.relUnimodular` are independent:

* `(3, 2, 0)` is unimodular and congruent to `e₀ = (1, 0, 0)` modulo `2`;
* `(2, 1, 0)` is unimodular but not congruent to `e₀`, since `2 - 1 ∉ 2ℤ`;
* `(3, 6, 0)` is congruent to `e₀` but not unimodular, since all its entries are divisible by `3`.
-/

namespace TauCeti.RelUnimodular.Examples

example : ![(3 : ℤ), 2, 0] ∈ (Ideal.span {(2 : ℤ)}).relUnimodular 0 := by
  refine Ideal.mem_relUnimodular_iff.mpr
    ⟨TauCeti.Module.isUnimodular_pi_iff.mpr ⟨![1, -1, 0], by simp [Fin.sum_univ_succ]⟩, ?_⟩
  intro i
  fin_cases i <;> simp

example : ![(2 : ℤ), 1, 0] ∉ (Ideal.span {(2 : ℤ)}).relUnimodular 0 := by
  intro h
  have := (Ideal.mem_relUnimodular_iff.mp h).2 0
  simp [Ideal.mem_span_singleton] at this

example : ![(3 : ℤ), 6, 0] ∉ (Ideal.span {(2 : ℤ)}).relUnimodular 0 := by
  intro h
  obtain ⟨h, -⟩ := Ideal.mem_relUnimodular_iff.mp h
  obtain ⟨b, hb⟩ := TauCeti.Module.isUnimodular_pi_iff.mp h
  simp [Fin.sum_univ_succ] at hb
  omega

end TauCeti.RelUnimodular.Examples
