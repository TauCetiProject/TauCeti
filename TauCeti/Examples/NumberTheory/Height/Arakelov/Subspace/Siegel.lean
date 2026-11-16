/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Siegel

/-!
# Worked examples: fixed-field Siegel's lemma in the Euclidean height

This file illustrates `TauCeti.exists_ne_zero_height2_le` and
`Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le` on three concrete rational systems:

* A single linear form `(1, 2)` in `ℚ²` has height `√5`, so Siegel's lemma produces a nonzero
  integer kernel vector of Euclidean height at most `√2 * √5`; in fact the kernel is spanned by
  `(-2, 1)`, which has exact Euclidean height `√5`.
* The repeated linear form `(1, 1, 0)` taken twice in `ℚ³` (`U = 2 < 3 = V`) is linearly dependent,
  yet satisfies all hypotheses of `TauCeti.exists_ne_zero_height2_le`; the theorem yields a
  nonzero kernel vector of height at most `2 * √3` (with `(0, 0, 1)` achieving height `1`).
* A single nonzero linear form in `ℚ¹` (`U = V = 1`) has trivial kernel, showing that the strict
  inequality `Fintype.card m < Fintype.card ι` is necessary.

## References

* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Module NumberField TauCeti
open scoped BigOperators Matrix

/-- Over `ℚ` with the single form `(1, 2)` in two variables, Siegel's lemma gives a nonzero
integer kernel vector of height at most `√2 * √5`, and every nonzero kernel vector has exact
Euclidean height `√5` (attained by `(-2, 1)`). -/
example :
    height2 ![(1 : ℚ), 2] = √5 ∧
      height2 ![(-2 : ℚ), 1] = √5 ∧
      (∃ z : Fin 2 → ℤ, z ≠ 0 ∧ ![(1 : ℚ), 2] ⬝ᵥ (fun i ↦ (z i : ℚ)) = 0 ∧
        height2 (fun i ↦ (z i : ℚ)) ≤ √2 * √5) := by
  have h12 : height2 ![(1 : ℚ), 2] = √5 := by
    have hcast : ![(1 : ℚ), 2] = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  have hm21 : height2 ![(-2 : ℚ), 1] = √5 := by
    have hcast : ![(-2 : ℚ), 1] = ((↑) : ℤ → ℚ) ∘ ![-2, 1] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  refine ⟨h12, hm21, ?_⟩
  let A : Matrix (Fin 1) (Fin 2) ℚ := Matrix.of fun _ ↦ ![(1 : ℚ), 2]
  have hA : ∀ i, A.row i ≠ 0 := by
    intro i h
    have := congrFun h 0
    simp [A] at this
  obtain ⟨z, hz0, hmul, hle⟩ :=
    Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le hA (by decide : Fintype.card (Fin 1) <
      Fintype.card (Fin 2))
  refine ⟨z, hz0, ?_, ?_⟩
  · simpa [A, Matrix.mulVec] using congrFun hmul 0
  · simpa [A, h12] using hle

/-- Over `ℚ` with the repeated form `(1, 1, 0)` (`U = 2`, `V = 3`), no row-independence hypothesis
is needed: Siegel's lemma yields a nonzero kernel vector of height at most `2 * √3`, while
`(0, 0, 1)` lies in the kernel with height `1`. -/
example :
    let L : Fin 2 → Fin 3 → ℚ := fun _ ↦ ![(1 : ℚ), 1, 0]
    (∏ i, height2 (L i)) = 2 ∧
      (∀ i, L i ⬝ᵥ ![(0 : ℚ), 0, 1] = 0) ∧
      height2 ![(0 : ℚ), 0, 1] = 1 ∧
      (∃ x : Fin 3 → ℚ, x ≠ 0 ∧ (∀ i, L i ⬝ᵥ x = 0) ∧ height2 x ≤ 2 * √3) := by
  intro L
  have hL_ht : height2 ![(1 : ℚ), 1, 0] = √2 := by
    have hcast : ![(1 : ℚ), 1, 0] = ((↑) : ℤ → ℚ) ∘ ![1, 1, 0] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_three]
  have hprod : (∏ i : Fin 2, height2 (L i)) = 2 := by
    simp [L, hL_ht]
  have h001_ker : ∀ i, L i ⬝ᵥ ![(0 : ℚ), 0, 1] = 0 := by
    intro i; simp [L, dotProduct, Fin.sum_univ_three]
  have h001_ht : height2 ![(0 : ℚ), 0, 1] = 1 := by
    have hcast : ![(0 : ℚ), 0, 1] = ((↑) : ℤ → ℚ) ∘ ![0, 0, 1] := by
      ext i; fin_cases i <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_three]
  have hL_ne : ∀ i, L i ≠ 0 := by
    intro i h
    have := congrFun h 0
    simp [L] at this
  obtain ⟨x, hx0, hxker, hle⟩ :=
    TauCeti.exists_ne_zero_height2_le hL_ne
      (by decide : Fintype.card (Fin 2) < Fintype.card (Fin 3))
  refine ⟨hprod, h001_ker, h001_ht, x, hx0, hxker, ?_⟩
  have hbound :
      √(Fintype.card (Fin 3) : ℝ) * |(discr ℚ : ℝ)| ^ (1 / (2 * (finrank ℚ ℚ : ℝ))) *
          (∏ i, height2 (L i)) ^ ((Fintype.card (Fin 3) - Fintype.card (Fin 2) : ℕ) : ℝ)⁻¹ =
        2 * √3 := by
    rw [hprod, discr_rat, finrank_self]
    norm_num
    ring
  exact hle.trans_eq hbound

/-- A single nonzero linear form in one variable has trivial kernel, confirming that the strict
inequality `Fintype.card m < Fintype.card ι` cannot be weakened to `≤`. -/
example : ¬ ∃ x : Fin 1 → ℚ, x ≠ 0 ∧ ![(1 : ℚ)] ⬝ᵥ x = 0 := by
  rintro ⟨x, hx0, hdot⟩
  apply hx0
  ext i
  fin_cases i
  simpa [dotProduct] using hdot

end
