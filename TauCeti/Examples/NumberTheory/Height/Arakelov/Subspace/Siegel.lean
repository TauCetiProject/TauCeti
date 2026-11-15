/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Siegel

/-!
# Worked examples: bounded-height kernel bases and Siegel's lemma over `ℚ`

This file checks the subspace and matrix kernel bounds of
`TauCeti.NumberTheory.Height.Arakelov.Subspace.Siegel` on three rational linear systems:

* **Single rational form `(1, 2)` (`U = 1`, `V = 2`).** `TauCeti.exists_ne_zero_height2_le` yields a
  nonzero integral solution of `x₀ + 2 x₁ = 0` of Euclidean height at most `√2 * √5 = √10` (attained
  by `(-2, 1)` of Euclidean height `√5`).
* **Repeated rational form (`U = 2`, `V = 3`, linearly dependent rows).** For the two-form system
  with both rows equal to `(1, 1, 0)`, `TauCeti.exists_ne_zero_height2_le` applies without assuming
  linear independence of the forms and bounds a nonzero integral solution by `√3 * (√2)² = 2 * √3`,
  while `Matrix.exists_linearIndependent_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le` uses
  the true matrix rank `1` to produce a `2`-element (`3 - 1 = 2`) integral `ℚ`-basis of the kernel
  whose product of sup heights is at most the row-space height `√2`.
* **Full-rank `1 × 1` matrix (`k = 0` boundary case).** For the identity matrix on `Fin 1`,
  `Matrix.exists_linearIndependent_ker_mulVecLin_prod_height2_le_sqrt_pow` applies at kernel
  dimension `0` and produces an empty family spanning `⊥` with empty height product `1 ≤ 1`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Matrix Module NumberField NumberField.InfinitePlace Set Submodule

/-! ### Single rational form `(1, 2)` -/

example :
    ∃ x : Fin 2 → 𝓞 ℚ, x ≠ 0 ∧ (x 0 : ℚ) + 2 * (x 1 : ℚ) = 0 ∧
      TauCeti.height2 (fun j ↦ (x j : ℚ)) ≤ √10 := by
  let L : Fin 1 → Fin 2 → ℚ := fun _ ↦ ![1, 2]
  have hL (i : Fin 1) : L i ≠ 0 := by simp [L]
  obtain ⟨x, hx0, hsum, hle⟩ :=
    TauCeti.exists_ne_zero_height2_le (by decide : Fintype.card (Fin 1) < Fintype.card (Fin 2)) hL
  refine ⟨x, hx0, ?_, hle.trans_eq ?_⟩
  · simpa [L, Fin.sum_univ_two] using hsum 0
  · have hcast : L 0 = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
      ext j
      fin_cases j <;> simp [L]
    have hh : TauCeti.height2 (L 0) = √5 := by
      rw [hcast, TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
      norm_num [Fin.sum_univ_two]
    rw [Rat.numberField_discr, finrank_self, Fin.prod_univ_one, hh]
    simp only [Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one, Int.cast_one, abs_one,
      Real.one_rpow, mul_one]
    have hsub : ((2 : ℝ) - 1)⁻¹ = 1 := by norm_num
    rw [hsub, Real.rpow_one, ← Real.sqrt_mul zero_le_two]
    norm_num

/-! ### Repeated rational form (`U = 2`, `V = 3`, rank `1`) -/

open scoped Classical in
example :
    let L : Fin 2 → Fin 3 → ℚ := fun _ ↦ ![1, 1, 0]
    (∃ x : Fin 3 → 𝓞 ℚ, x ≠ 0 ∧ (∀ i, ∑ j, L i j * (x j : ℚ) = 0) ∧
      TauCeti.height2 (fun j ↦ (x j : ℚ)) ≤ 2 * √3) ∧
    ((Matrix.of L).rank = 1 ∧
      ∃ b : Fin (Fintype.card (Fin 3) - (Matrix.of L).rank) → Fin 3 → 𝓞 ℚ,
        (∀ j, Matrix.of L *ᵥ (fun k ↦ (b j k : ℚ)) = 0) ∧
        LinearIndependent ℚ (fun j k ↦ (b j k : ℚ)) ∧
        span ℚ (range fun j k ↦ (b j k : ℚ)) = LinearMap.ker (Matrix.of L).mulVecLin ∧
        ∏ j, TauCeti.absoluteProjectiveTupleHeight (fun k ↦ (b j k : ℚ)) ≤ √2) := by
  intro L
  have hv : ![(1 : ℚ), 1, 0] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hcast : ![(1 : ℚ), 1, 0] = ((↑) : ℤ → ℚ) ∘ ![1, 1, 0] := by
    ext j
    fin_cases j <;> simp
  have hh : TauCeti.height2 ![(1 : ℚ), 1, 0] = √2 := by
    rw [hcast, TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_three]
  obtain ⟨x, hx0, hsum, hle⟩ :=
    TauCeti.exists_ne_zero_height2_le
      (by decide : Fintype.card (Fin 2) < Fintype.card (Fin 3)) (L := L) (fun _ ↦ hv)
  set A : Matrix (Fin 2) (Fin 3) ℚ := Matrix.of L
  have hrange : range A.row = {![(1 : ℚ), 1, 0]} := Set.range_const
  have hspan : span ℚ (range A.row) = ℚ ∙ ![(1 : ℚ), 1, 0] := by rw [hrange]
  have hrank : A.rank = 1 := by
    rw [A.rank_eq_finrank_span_row]
    change finrank ℚ (span ℚ (range A.row)) = 1
    rw [hspan, finrank_span_singleton hv]
  have hH : (span ℚ (range A.row)).subspaceHeight = √2 := by
    rw [hspan, subspaceHeight_span_singleton hv, hh]
  obtain ⟨b, hb0, hbli, hbspan, hbprod⟩ :=
    A.exists_linearIndependent_ker_mulVecLin_prod_absoluteProjectiveTupleHeight_le
  refine ⟨⟨x, hx0, hsum, hle.trans_eq ?_⟩, hrank, b, hb0, hbli, hbspan, hbprod.trans_eq ?_⟩
  · rw [Rat.numberField_discr, finrank_self, Fin.prod_univ_two]
    simp only [L, hh, Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one, Int.cast_one, abs_one,
      Real.one_rpow, mul_one]
    have hsub : ((3 : ℝ) - 2)⁻¹ = 1 := by norm_num
    rw [hsub, Real.rpow_one, Real.mul_self_sqrt zero_le_two, mul_comm]
  · rw [nrComplexPlaces_eq_zero_of_finrank_eq_one (finrank_self ℚ), Rat.numberField_discr, hH]
    simp only [Nat.cast_zero, zero_mul, zero_div, Real.rpow_zero, Int.cast_one, abs_one,
      Real.one_rpow, one_mul]

/-! ### Full-rank `1 × 1` matrix (`k = 0`) -/

example :
    let A : Matrix (Fin 1) (Fin 1) ℚ := 1
    A.rank = 1 ∧
      ∃ b : Fin (Fintype.card (Fin 1) - A.rank) → Fin 1 → 𝓞 ℚ,
        (∀ j, A *ᵥ (fun k ↦ (b j k : ℚ)) = 0) ∧
        LinearIndependent ℚ (fun j k ↦ (b j k : ℚ)) ∧
        span ℚ (range fun j k ↦ (b j k : ℚ)) = LinearMap.ker A.mulVecLin ∧
        ∏ j, TauCeti.height2 (fun k ↦ (b j k : ℚ)) ≤ 1 := by
  intro A
  have hrank : A.rank = 1 := by simp [A]
  obtain ⟨b, hb0, hbli, hbspan, hbprod⟩ :=
    A.exists_linearIndependent_ker_mulVecLin_prod_height2_le_sqrt_pow
  refine ⟨hrank, b, hb0, hbli, hbspan, hbprod.trans_eq ?_⟩
  have hrow0 : A.row 0 = ![(1 : ℚ)] := by ext j; fin_cases j; rfl
  have hrow : range A.row = {![(1 : ℚ)]} := by
    ext v
    simp [Fin.exists_fin_one, hrow0, eq_comm]
  have hv : ![(1 : ℚ)] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hcast : ![(1 : ℚ)] = ((↑) : ℤ → ℚ) ∘ ![1] := by ext j; fin_cases j; simp
  have hH : (span ℚ (range A.row)).subspaceHeight = 1 := by
    rw [hrow, subspaceHeight_span_singleton hv, hcast,
      TauCeti.height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num
  rw [hrank, Fintype.card_fin, Nat.sub_self, Rat.numberField_discr, hH]
  norm_num

end
