/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.MeasureTheory.Measure.Haar.InnerProductSpace
import TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants

/-!
# Worked examples: Siegel's lemma and kernel bases over `ℚ` and `ℚ(i)`

This file exercises the archimedean slice volumes, kernel-basis theorems, and fixed-field Siegel
lemma of `TauCeti.NumberTheory.NumberField.CanonicalEmbedding.PlaceDecomposition`,
`TauCeti.NumberTheory.Height.Arakelov.KernelBasis`, and
`TauCeti.NumberTheory.Height.Arakelov.SiegelsLemma`:

0. **Archimedean slice volumes at `k = 0` and `k = n`.** For `⊥ : Submodule K (Fin n → K)`
   `euclideanBallSlice` has volume `1`, while for `⊤ : Submodule K (Fin n → K)` `supSlice` has
   volume at least `2 ^ (r₁ * n) * π ^ (r₂ * n)`.
1. **Single rational linear form `(1, 2)` (`U = 1, V = 2`).** `TauCeti.exists_ne_zero_height2_le`
   produces a nonzero rational solution of `x 0 + 2 * x 1 = 0` with `H₂(x) ≤ √2 * √5`, and
   `Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le` produces a nonzero integer solution with
   the same bound, while `(-2, 1)` attains `H₂(-2, 1) = √5 ≤ √2 * √5`.
2. **Repeated rational rows `(1, 1, 0)` (`U = 2, V = 3`, rank `1`).** Without row independence,
   `TauCeti.exists_ne_zero_height2_le` gives a nonzero solution of Euclidean height at most `2 * √3`
   (attained with slack by `(0, 0, 1)` of height `1`), while
   `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le` uses `A.rank = 1` to produce a
   `2`-element integral basis of `ker A`.
3. **Full-rank `1 × 1` matrix `!![1]` (`U = V = 1`, `k = 0`).** The kernel is `⊥`, confirming that
   `#m < #ι` is necessary for a nonzero solution, while the basis theorem still applies at `k = 0`.
4. **Gaussian-rational system `A = !![θ, -1]` over `K = ℚ(i)`.** Here `ker A = K ∙ ![1, θ]` has
   dimension `1`, `[K : ℚ] = 2`, `nrComplexPlaces K = 1`, `discr K = -4`, and `H₂(rowSpace A) = √2`
   by Hodge duality. The sup-height kernel-basis theorem gives an integral generator of height at
   most `2 * √(2 / π)`, while `![1, θ]` has absolute projective sup height `1 ≤ 2 * √(2 / π)`.

## References

* E. Bombieri and J. Vaaler, *On Siegel's lemma*, Invent. Math. **73** (1983), 11–32.
* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §2.9.
* J.-H. Evertse and R. G. Ferretti, *A further improvement of the quantitative Subspace Theorem*,
  Ann. of Math. **177** (2013), 513–590, §13, Lemma 13.1.
-/

noncomputable section

open Matrix MeasureTheory Metric Module NumberField NumberField.InfinitePlace Set Submodule TauCeti
  TauCeti.NumberField
open scoped BigOperators

/-! ### 0. Archimedean slice volumes at `k = 0` and `k = n` -/

open scoped Classical in
example (K : Type*) [Field K] [NumberField K] (n : ℕ) :
    volume.real (((⊥ : Submodule K (Fin n → K)).euclideanBallSlice :
        Set (⊥ : Submodule K (Fin n → K)).euclideanSpan)) = 1 ∧
      (2 : ℝ) ^ (nrRealPlaces K * n) * Real.pi ^ (nrComplexPlaces K * n) ≤
        volume.real (((⊤ : Submodule K (Fin n → K)).supSlice :
          Set (⊤ : Submodule K (Fin n → K)).euclideanSpan)) := by
  have hball0 : volume.real (ball (0 : EuclideanSpace ℝ (Fin 0)) 1) = 1 := by
    simp [measureReal_def, volume_eq_one_of_subsingleton
      (Metric.nonempty_ball.2 one_pos : (ball (0 : EuclideanSpace ℝ (Fin 0)) 1).Nonempty)]
  refine ⟨?_, ?_⟩
  · rw [(⊥ : Submodule K (Fin n → K)).volume_real_euclideanBallSlice, finrank_bot, mul_zero,
      hball0, one_pow, one_pow, mul_one]
  · simpa [finrank_top, Module.finrank_fintype_fun_eq_card] using
      (⊤ : Submodule K (Fin n → K)).two_pow_mul_pi_pow_le_volume_real_supSlice

/-! ### 1. Single rational linear form `(1, 2)` -/

example :
    (∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 + 2 * x 1 = 0 ∧ height2 x ≤ √2 * √5) ∧
      (∃ z : Fin 2 → ℤ, z ≠ 0 ∧ (z 0 : ℚ) + 2 * (z 1 : ℚ) = 0 ∧
        height2 (fun i ↦ (z i : ℚ)) ≤ √2 * √5) ∧
      height2 ![-2, (1 : ℚ)] = √5 ∧ √5 ≤ √2 * √5 := by
  let L : Fin 1 → Fin 2 → ℚ := ![![1, 2]]
  have hL : ∀ i, L i ≠ 0 := fun i ↦ by fin_cases i; exact fun h ↦ one_ne_zero (congrFun h 0)
  have hH : height2 (L 0) = √5 := by
    have : L 0 = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by ext j; fin_cases j <;> simp [L]
    rw [this, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]; norm_num [Fin.sum_univ_two]
  obtain ⟨x, hx0, hLx, hxle⟩ := exists_ne_zero_height2_le hL (by decide)
  rw [Fintype.card_fin, Fintype.card_fin, NumberField.discr_rat, finrank_self,
    Fin.prod_univ_one, hH] at hxle
  obtain ⟨z, hz0, hLz, hzle⟩ :=
    Matrix.exists_ne_zero_int_mulVec_eq_zero_height2_le (A := Matrix.of L) hL (by decide)
  rw [Fintype.card_fin, Fintype.card_fin, Fin.prod_univ_one,
    show (Matrix.of L).row 0 = L 0 from rfl, hH] at hzle
  have hgen : height2 ![-2, (1 : ℚ)] = √5 := by
    have : ![-2, (1 : ℚ)] = ((↑) : ℤ → ℚ) ∘ ![-2, 1] := by ext j; fin_cases j <;> simp
    rw [this, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]; norm_num [Fin.sum_univ_two]
  exact ⟨⟨x, hx0, by simpa [L, Fin.sum_univ_two] using hLx 0, by norm_num at hxle; exact hxle⟩,
    ⟨z, hz0, by simpa [L, Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hLz 0,
      by norm_num at hzle; exact hzle⟩,
    hgen, le_mul_of_one_le_left (Real.sqrt_nonneg 5) (Real.one_le_sqrt.2 one_le_two)⟩

/-! ### 2. Repeated rational rows `(1, 1, 0)`: rank `1` vs `U = 2` -/

open scoped Classical in
example :
    let A : Matrix (Fin 2) (Fin 3) ℚ := !![1, 1, 0; 1, 1, 0]
    (∃ x : Fin 3 → ℚ, x ≠ 0 ∧ A *ᵥ x = 0 ∧ height2 x ≤ 2 * √3) ∧
      height2 ![(0 : ℚ), 0, 1] = 1 ∧
      Fintype.card (Fin 3) - A.rank = 2 ∧
      ∃ b : Fin (Fintype.card (Fin 3) - A.rank) → Fin 3 → 𝓞 ℚ,
        LinearIndependent ℚ (fun j i ↦ (b j i : ℚ)) ∧
        span ℚ (range fun j i ↦ (b j i : ℚ)) = LinearMap.ker A.mulVecLin := by
  intro A
  have hrow : ∀ i, A.row i ≠ 0 := fun i ↦ by
    fin_cases i <;> exact fun h ↦ one_ne_zero (congrFun h 0)
  have hrowH (i : Fin 2) : height2 (A.row i) = √2 := by
    have : A.row i = ((↑) : ℤ → ℚ) ∘ ![1, 1, 0] := by
      fin_cases i <;> (ext j; fin_cases j <;> simp [A])
    rw [this, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]; norm_num [Fin.sum_univ_three]
  obtain ⟨x, hx0, hAx, hxle⟩ := exists_ne_zero_height2_le hrow (by decide)
  rw [Fintype.card_fin, Fintype.card_fin, NumberField.discr_rat, finrank_self,
    Fin.prod_univ_two, hrowH 0, hrowH 1, Real.mul_self_sqrt zero_le_two] at hxle
  have he₃ : height2 ![(0 : ℚ), 0, 1] = 1 := by
    have : ![(0 : ℚ), 0, 1] = ((↑) : ℤ → ℚ) ∘ ![0, 0, 1] := by ext j; fin_cases j <;> simp
    rw [this, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]; norm_num [Fin.sum_univ_three]
  have hrange : LinearMap.range A.mulVecLin = ℚ ∙ ![(1 : ℚ), 1] := by
    ext y; rw [LinearMap.mem_range, mem_span_singleton]
    exact ⟨fun ⟨v, hv⟩ ↦ ⟨v 0 + v 1, hv ▸ by ext i; fin_cases i <;>
        simp [A, mulVec, dotProduct, Fin.sum_univ_three]⟩,
      fun ⟨c, hc⟩ ↦ ⟨![c, 0, 0], hc ▸ by ext i; fin_cases i <;>
        simp [A, mulVec, dotProduct, Fin.sum_univ_three]⟩⟩
  have hrank : A.rank = 1 := by
    rw [← Matrix.finrank_range_mulVecLin, hrange,
      finrank_span_singleton (fun h ↦ one_ne_zero (congrFun h 0))]
  obtain ⟨b, hb_li, hb_span, _, _⟩ := A.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le
  exact ⟨⟨x, hx0, funext fun i ↦ by simpa [mulVec, dotProduct] using hAx i,
    by norm_num at hxle; linarith⟩, he₃, by simp [hrank], ⟨b, hb_li, hb_span⟩⟩

/-! ### 3. Full-rank `1 × 1` matrix (`U = V = 1`, `k = 0`) -/

open scoped Classical in
example :
    let A : Matrix (Fin 1) (Fin 1) ℚ := !![1]
    LinearMap.ker A.mulVecLin = ⊥ ∧ Fintype.card (Fin 1) - A.rank = 0 := by
  intro A
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    ext v; simp only [LinearMap.mem_ker, Submodule.mem_bot]
    exact ⟨fun h ↦ funext fun i ↦ by fin_cases i; simpa [A, mulVec, dotProduct] using congrFun h 0,
      fun h ↦ by simp [h]⟩
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [Matrix.finrank_range_mulVecLin, hker, finrank_bot, add_zero,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
  exact ⟨hker, by simp [h]⟩

/-! ### 4. Gaussian-rational kernel basis over `ℚ(i)` -/

open scoped Classical in
example (K : Type*) [Field K] [NumberField K] {θ : 𝓞 K}
    (hmin : minpoly ℤ θ = Polynomial.X ^ 2 + 1)
    (hgen : Algebra.adjoin ℚ {(θ : K)} = ⊤) :
    let A : Matrix (Fin 1) (Fin 2) K := !![(θ : K), -1]
    LinearMap.ker A.mulVecLin = K ∙ ![(1 : K), (θ : K)] ∧
      Fintype.card (Fin 2) - A.rank = 1 ∧
      absoluteProjectiveTupleHeight ![(1 : K), (θ : K)] = 1 ∧
      1 ≤ 2 * √(2 / Real.pi) ∧
      ∃ x : Fin 2 → 𝓞 K,
        LinearIndependent K (fun _ : Fin 1 ↦ fun j ↦ (x j : K)) ∧
        span K {fun j ↦ (x j : K)} = LinearMap.ker A.mulVecLin ∧
        A *ᵥ (fun j ↦ (x j : K)) = 0 ∧
        absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤ 2 * √(2 / Real.pi) := by
  intro A
  set W : Submodule K (Fin 2 → K) := K ∙ ![(1 : K), (θ : K)]
  let y : Fin 2 → 𝓞 K := ![1, θ]
  have hv0 : ![(1 : K), (θ : K)] ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hy0 : y ≠ 0 := fun h ↦ one_ne_zero (congrFun h 0)
  have hy_cast : (fun j ↦ (y j : K)) = ![(1 : K), (θ : K)] := by ext j; fin_cases j <;> simp [y]
  have : IsTotallyComplex K := GaussianRationals.isTotallyComplex hmin
  have hr₂ : nrComplexPlaces K = 1 := GaussianRationals.nrComplexPlaces_eq_one hmin hgen
  have hdeg : finrank ℚ K = 2 := GaussianRationals.finrank_eq_two hmin hgen
  have hdiscr : discr K = -4 := GaussianRationals.discr_eq_neg_four hmin hgen
  have hθ_sq : (θ : K) ^ 2 = -1 := by exact_mod_cast GaussianRationals.sq_eq_neg_one hmin
  have hcard_inf : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, hr₂,
      zero_add]
  have hker : LinearMap.ker A.mulVecLin = W := by
    ext v; rw [LinearMap.mem_ker, mulVecLin_apply, mem_span_singleton]
    refine ⟨fun hv ↦ ⟨v 0, ?_⟩, fun ⟨c, hc⟩ ↦ hc ▸ funext fun i ↦ ?_⟩
    · have hv' : (θ : K) * v 0 + -1 * v 1 = 0 := by
        simpa [A, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
      ext j; fin_cases j
      · simp
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, cons_val_one, cons_val_zero]
        linear_combination hv'
    · fin_cases i; simp [A, mulVec, dotProduct, Fin.sum_univ_two]; ring
  have hnull : Fintype.card (Fin 2) - A.rank = 1 := by
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    rw [Matrix.finrank_range_mulVecLin, hker, finrank_span_singleton hv0,
      Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    rw [Fintype.card_fin]; omega
  have hθ_place (w : InfinitePlace K) : w (θ : K) = 1 := by
    have hsq : w (θ : K) ^ 2 = 1 := by
      rw [← w.norm_embedding_eq, ← norm_pow, ← map_pow, hθ_sq, map_neg, map_one, norm_neg, norm_one]
    nlinarith [apply_nonneg w (θ : K)]
  have hH_sup : absoluteProjectiveTupleHeight ![(1 : K), (θ : K)] = 1 := by
    refine le_antisymm ?_ (one_le_absoluteProjectiveTupleHeight _)
    rw [← hy_cast]
    exact absoluteProjectiveTupleHeight_le_of_forall_le hy0 fun j w ↦ by
      fin_cases j <;> simp [y, hθ_place w]
  have h1_le : 1 ≤ 2 * √(2 / Real.pi) := by
    have hhalf : (2⁻¹ : ℝ) ≤ √(2 / Real.pi) :=
      Real.le_sqrt_of_sq_le ((le_div_iff₀ Real.pi_pos).2 (by linarith [Real.pi_lt_four]))
    linarith
  have hspan_top : Ideal.span (range y) = ⊤ := top_unique fun x _ ↦ by
    simpa [y] using Ideal.mul_mem_left _ x (Ideal.subset_span (s := range y) ⟨0, rfl⟩)
  have hrel : W.relativeSubspaceArakelovHeight = 2 := by
    rw [relativeSubspaceArakelovHeight_span_singleton, ← hy_cast]
    have hprod := arakelovMulHeight_mul_absNorm_span_range y
    rw [hspan_top, Ideal.absNorm_top, Nat.cast_one, mul_one] at hprod
    rw [hprod]
    refine (Finset.prod_congr rfl (g := fun _ ↦ (2 : ℝ)) fun w _ ↦ ?_).trans (by simp [hcard_inf])
    rw [IsTotallyComplex.mult_eq,
      Finset.sum_congr (s₂ := Finset.univ) (by ext; simp) fun _ _ ↦ rfl, Fin.sum_univ_two]
    simp only [y, cons_val_zero, cons_val_one, map_one, norm_one, one_pow,
      w.norm_embedding_eq, hθ_place w]
    norm_num
  have hH_row : (span K (range A.row)).subspaceHeight = √2 := by
    rw [← A.subspaceHeight_ker_mulVecLin, hker]
    have hp := W.subspaceHeight_pow_finrank
    rw [hdeg, hrel] at hp
    exact (pow_left_inj₀ (Submodule.subspaceHeight_pos W).le (Real.sqrt_nonneg _) two_ne_zero).mp
      (hp.trans (Real.sq_sqrt zero_le_two).symm)
  obtain ⟨z, hz_li, hz_span, hz_ker, hz_le⟩ :=
    A.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le
  let e : Fin 1 ≃ Fin (Fintype.card (Fin 2) - A.rank) := finCongr hnull.symm
  let x : Fin 2 → 𝓞 K := z (e 0)
  have hx_span : span K {fun j ↦ (x j : K)} = LinearMap.ker A.mulVecLin := by
    have hset : ({fun j ↦ (x j : K)} : Set (Fin 2 → K)) = range fun l j ↦ (z l j : K) := by
      ext v
      simp only [mem_singleton_iff, mem_range, x]
      exact ⟨fun hv ↦ ⟨e 0, hv.symm⟩, fun ⟨l, hl⟩ ↦ by
        obtain ⟨i, rfl⟩ := e.surjective l; fin_cases i; exact hl.symm⟩
    rw [hset, hz_span]
  have hx_le : absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤ 2 * √(2 / Real.pi) := by
    have hprod_eq : absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) =
        ∏ l, absoluteProjectiveTupleHeight (fun j ↦ (z l j : K)) := by
      rw [← e.prod_comp (fun l ↦ absoluteProjectiveTupleHeight fun j ↦ (z l j : K)),
        Fin.prod_univ_one]
    rw [hprod_eq]
    refine hz_le.trans_eq ?_
    rw [hnull, hr₂, hdeg, hdiscr, hH_row]
    have h4 : |((-4 : ℤ) : ℝ)| ^ (((1 : ℕ) : ℝ) / (2 * (2 : ℕ))) = √2 := by
      have h4_eq : |((-4 : ℤ) : ℝ)| = (2 : ℝ) ^ 2 := by norm_num
      rw [h4_eq, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul zero_le_two, Real.sqrt_eq_rpow]
      congr 1; norm_num
    have hpi : (2 / Real.pi) ^ (((1 : ℕ) * (1 : ℕ) : ℝ) / (2 : ℕ)) = √(2 / Real.pi) := by
      rw [Real.sqrt_eq_rpow]; congr 1; norm_num
    rw [h4, hpi, mul_assoc, Real.mul_self_sqrt zero_le_two, mul_comm]
  exact ⟨hker, hnull, hH_sup, h1_le,
    ⟨x, by simpa [x] using hz_li.comp e e.injective, hx_span, hz_ker (e 0), hx_le⟩⟩

end
