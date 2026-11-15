/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Siegel
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants

/-!
# Worked example: Bombieri–Vaaler basis bound and Siegel's lemma over `ℚ(i)`

For `K = ℚ(i)` (presented by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`), this file
exercises `Submodule.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le`
and `TauCeti.exists_ne_zero_height2_le` on the line `W = K ∙ ![1, θ]` and the linear form
`x₀ + θ x₁`:

* `r₂ = 1`, `discr K = -4`, `[K : ℚ] = 2`, and `W.subspaceHeight = height2 ![1, θ] = √2`;
* `W` admits an integral `K`-basis in `W.integerPoints` of absolute sup height at most
  `√(2 / π) * |-4| ^ (1 / 4) * √2 = 2 * √(2 / π)` (attained by `![1, θ]` of height `1`);
* the form `x₀ + θ x₁ = 0` admits a nonzero solution in `(𝓞 K)²` of Euclidean height at most
  `√2 * |-4| ^ (1 / 4) * √2 = 2 * √2` (attained by `![-θ, 1]` of height `√2`).

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Module NumberField NumberField.InfinitePlace Set Submodule TauCeti TauCeti.NumberField

/-! ### Gaussian-rational line and linear form -/

open scoped Classical in
example (K : Type*) [Field K] [NumberField K] {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = Polynomial.X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    let W : Submodule K (Fin 2 → K) := K ∙ ![(1 : K), (θ : K)]
    (∃ b : Fin (finrank K W) → Fin 2 → 𝓞 K,
      (∀ j, b j ∈ W.integerPoints) ∧
      LinearIndependent K (fun j i ↦ (b j i : K)) ∧
      span K (range fun j i ↦ (b j i : K)) = W ∧
      ∏ j, absoluteProjectiveTupleHeight (fun i ↦ (b j i : K)) ≤ 2 * √(2 / Real.pi)) ∧
    (∃ z : Fin 2 → 𝓞 K, z ≠ 0 ∧ (z 0 : K) + (θ : K) * (z 1 : K) = 0 ∧
      height2 (fun j ↦ (z j : K)) ≤ 2 * √2) := by
  intro W
  let y : Fin 2 → 𝓞 K := ![1, θ]
  have hv0 : ![(1 : K), (θ : K)] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hy_cast : (fun i ↦ (y i : K)) = ![(1 : K), (θ : K)] := by
    ext i
    fin_cases i <;> simp [y]
  have hspan_top : Ideal.span (range y) = ⊤ :=
    top_unique fun x _ ↦ by
      simpa [y] using Ideal.mul_mem_left _ x (Ideal.subset_span (s := range y) ⟨0, rfl⟩)
  have : IsTotallyComplex K := GaussianRationals.isTotallyComplex hmin
  have hr₂ : nrComplexPlaces K = 1 := GaussianRationals.nrComplexPlaces_eq_one hmin hgen
  have hdeg : finrank ℚ K = 2 := GaussianRationals.finrank_eq_two hmin hgen
  have hdiscr : discr K = -4 := GaussianRationals.discr_eq_neg_four hmin hgen
  have hθ_sq : (θ : K) ^ 2 = -1 := by
    exact_mod_cast GaussianRationals.sq_eq_neg_one hmin
  have hcard_inf : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, hr₂,
      zero_add]
  have hrel : W.relativeSubspaceArakelovHeight = 2 := by
    rw [relativeSubspaceArakelovHeight_span_singleton, ← hy_cast]
    have hprod : arakelovMulHeight (fun i ↦ (y i : K)) * (Ideal.span (range y)).absNorm =
        ∏ w : InfinitePlace K, (∑ i : Fin 2, ‖w.embedding (y i : K)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
      rw [arakelovMulHeight_mul_absNorm_span_range y]; congr!
    rw [hspan_top, Ideal.absNorm_top, Nat.cast_one, mul_one] at hprod
    rw [hprod]
    have hfac (w : InfinitePlace K) :
        (∑ i : Fin 2, ‖w.embedding (y i : K)‖ ^ 2) ^ ((w.mult : ℝ) / 2) = 2 := by
      have hθ_norm : ‖w.embedding (θ : K)‖ ^ 2 = 1 := by
        rw [← norm_pow, ← map_pow, hθ_sq, map_neg, map_one, norm_neg, norm_one]
      rw [Fin.sum_univ_two, IsTotallyComplex.mult_eq]
      simp only [y, Matrix.cons_val_zero, Matrix.cons_val_one, map_one, norm_one, one_pow, hθ_norm]
      norm_num
    simp_rw [hfac]
    rw [Finset.prod_const, Finset.card_univ, hcard_inf, pow_one]
  have habs : W.subspaceHeight = √2 := by
    have hp := W.subspaceHeight_pow_finrank
    rw [hdeg, hrel] at hp
    have hsq : W.subspaceHeight ^ 2 = √2 ^ 2 := by rw [hp, Real.sq_sqrt zero_le_two]
    exact (pow_left_inj₀ (subspaceHeight_pos W).le (Real.sqrt_nonneg _) two_ne_zero).mp hsq
  have hh2 : height2 ![(1 : K), (θ : K)] = √2 := by
    rw [← subspaceHeight_span_singleton hv0]
    exact habs
  have hdimW : finrank K W = 1 := finrank_span_singleton hv0
  have h4 : (|(-4 : ℤ)| : ℝ) ^ ((1 : ℝ) / (2 * 2)) = √2 := by
    have h4' : (|(-4 : ℤ)| : ℝ) = (2 : ℝ) ^ (2 : ℕ) := by norm_num
    rw [h4', ← Real.rpow_natCast, ← Real.rpow_mul zero_le_two, Real.sqrt_eq_rpow]
    congr 1
    norm_num
  obtain ⟨b, hbW, hbli, hbspan, hbprod⟩ :=
    W.exists_linearIndependent_integerPoints_prod_absoluteProjectiveTupleHeight_le
  let L : Fin 1 → Fin 2 → K := fun _ ↦ ![(1 : K), (θ : K)]
  obtain ⟨z, hz0, hzsum, hzle⟩ :=
    exists_ne_zero_height2_le (by decide : Fintype.card (Fin 1) < Fintype.card (Fin 2))
      (L := L) (fun _ ↦ hv0)
  refine ⟨⟨b, hbW, hbli, hbspan, hbprod.trans_eq ?_⟩, z, hz0, ?_, hzle.trans_eq ?_⟩
  · have h2pi : (2 / Real.pi : ℝ) ^ ((1 * 1 : ℝ) / 2) = √(2 / Real.pi) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [hr₂, hdimW, hdeg, hdiscr, habs]
    simp only [Nat.cast_one, Nat.cast_ofNat, Int.cast_neg, Int.cast_ofNat] at h4 ⊢
    rw [h2pi, h4, mul_assoc, Real.mul_self_sqrt zero_le_two, mul_comm]
  · simpa [L, Fin.sum_univ_two] using hzsum 0
  · rw [hdeg, hdiscr, Fin.prod_univ_one]
    simp only [L, hh2, Fintype.card_fin, Nat.cast_ofNat, Nat.cast_one, Int.cast_neg,
      Int.cast_ofNat] at h4 ⊢
    have hsub : ((2 : ℝ) - 1)⁻¹ = 1 := by norm_num
    rw [hsub, Real.rpow_one, h4, Real.mul_self_sqrt zero_le_two]

end
