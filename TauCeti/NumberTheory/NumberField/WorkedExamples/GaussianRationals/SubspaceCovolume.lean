/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.Height.Arakelov.Subspace.Covolume
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants

/-!
# Worked example: subspace height and integral-lattice covolume over `ℚ(i)`

This file exercises Schmidt's covolume identity (`Submodule.covolume_integerLattice` and
`Submodule.covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight`) over
`K = ℚ(i)` (presented by an algebraic integer `θ` with `minpoly ℤ θ = X² + 1`): the line
`W = K ∙ ![1, θ]` has absolute height `√2`, relative Arakelov height `2`, and integral-lattice
covolume `2`. Here `r₂ = 1`, `|discr K| = 4`, and `[K : ℚ] = 2`, so both the complex-place factor
`2⁻¹ ^ r₂ = 1 / 2` (cancelling `√|discr K| = 2`) and the degree exponent `[K : ℚ] = 2` on
`W.subspaceHeight` are exercised simultaneously.

## References

* W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Ann. of Math.
  **85** (1967), 430–472, §3, Theorem 1.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §6.1.
-/

noncomputable section

open MeasureTheory Module NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Set
  Submodule TauCeti TauCeti.NumberField

/-! ### Gaussian-rational line `ℚ(i) ∙ ![1, i]` -/

open scoped Classical in
example (K : Type*) [Field K] [NumberField K] {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = Polynomial.X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    (K ∙ ![(1 : K), (θ : K)]).subspaceHeight = √2 ∧
      (K ∙ ![(1 : K), (θ : K)]).relativeSubspaceArakelovHeight = 2 ∧
      ZLattice.covolume (K ∙ ![(1 : K), (θ : K)]).integerLattice = 2 := by
  set W : Submodule K (Fin 2 → K) := K ∙ ![(1 : K), (θ : K)]
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
  have hcov : ZLattice.covolume W.integerLattice = 2 := by
    rw [W.covolume_integerLattice_eq_covolume_pow_mul_relativeSubspaceArakelovHeight,
      mixedEmbedding.covolume_integerLattice, finrank_span_singleton hv0, pow_one, hr₂, hdiscr,
      hrel]
    have h4 : √(|(-4 : ℤ)| : ℝ) = 2 := by
      have h4' : (|(-4 : ℤ)| : ℝ) = 2 ^ 2 := by norm_num
      rw [h4', Real.sqrt_sq zero_le_two]
    rw [h4]
    norm_num
  exact ⟨habs, hrel, hcov⟩

end
