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

0. **Archimedean slice volumes at `k = 0` and `k = n`.** For `⊥ : Submodule K (Fin n → K)` both
   `supSlice` and `euclideanBallSlice` have volume `1`, while for `⊤ : Submodule K (Fin n → K)`
   (`finrank = n`) `supSlice` has volume at least `2 ^ (r₁ * n) * π ^ (r₂ * n)`.
1. **Single rational linear form `(1, 2)` (`U = 1, V = 2`).** `TauCeti.exists_ne_zero_height2_le`
   produces a nonzero solution of `x 0 + 2 * x 1 = 0` with `H₂(x) ≤ √2 * √5`, while the primitive
   generator `(-2, 1)` attains `H₂(-2, 1) = √5 ≤ √2 * √5`.
2. **Repeated rational rows `(1, 1, 0)` (`U = 2, V = 3`, rank `1`).** Without row independence,
   `TauCeti.exists_ne_zero_height2_le` applies with `V - U = 1` and `H₂(1, 1, 0)² = 2` to give a
   nonzero solution of Euclidean height at most `2 * √3` (attained with slack by `(0, 0, 1)` of
   height `1`), while `Matrix.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le` uses the
   true rank `A.rank = 1` to produce a `2`-element integral basis of `ker A`.
3. **Full-rank `1 × 1` matrix `!![1]` (`U = V = 1`, `k = 0`).** The kernel is `⊥`, confirming that
   `#m < #ι` is necessary for a nonzero solution, while the basis theorem still applies at `k = 0`
   with empty product `1 ≤ 1`.
4. **Gaussian-rational system `A = !![θ, -1]` over `K = ℚ(i)`.** Here `ker A = K ∙ ![1, θ]` has
   dimension `1`, `[K : ℚ] = 2`, `nrComplexPlaces K = 1`, `discr K = -4`, and by Hodge duality
   `H₂(rowSpace A) = H₂(K ∙ ![1, θ]) = √2`. The sup-height kernel-basis theorem gives an integral
   generator of height at most `(2 / π) ^ (1 / 2) * 4 ^ (1 / 4) * √2 = 2 * √(2 / π)`, while the
   explicit generator `![1, θ]` has absolute projective sup height `1 ≤ 2 * √(2 / π)`.

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
    simp [measureReal_def,
      volume_eq_one_of_subsingleton
        (Metric.nonempty_ball.2 one_pos : (ball (0 : EuclideanSpace ℝ (Fin 0)) 1).Nonempty)]
  have hbot :
      volume.real (((⊥ : Submodule K (Fin n → K)).euclideanBallSlice :
          Set (⊥ : Submodule K (Fin n → K)).euclideanSpan)) = 1 := by
    rw [(⊥ : Submodule K (Fin n → K)).volume_real_euclideanBallSlice, finrank_bot, mul_zero,
      hball0, one_pow, one_pow, mul_one]
  have htop := (⊤ : Submodule K (Fin n → K)).two_pow_mul_pi_pow_le_volume_real_supSlice
  rw [finrank_top, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at htop
  exact ⟨hbot, htop⟩

/-! ### 1. Single rational linear form `(1, 2)` -/

example :
    (∃ x : Fin 2 → ℚ, x ≠ 0 ∧ x 0 + 2 * x 1 = 0 ∧ height2 x ≤ √2 * √5) ∧
      height2 ![-2, (1 : ℚ)] = √5 ∧ √5 ≤ √2 * √5 := by
  let L : Fin 1 → Fin 2 → ℚ := ![![1, 2]]
  have hL : ∀ i, L i ≠ 0 := fun i ↦ by
    fin_cases i
    intro h
    exact one_ne_zero (congrFun h 0)
  have hH : height2 (L 0) = √5 := by
    have hcast : L 0 = ((↑) : ℤ → ℚ) ∘ ![1, 2] := by
      ext j
      fin_cases j <;> simp [L]
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  obtain ⟨x, hx0, hLx, hxle⟩ := exists_ne_zero_height2_le hL (by decide)
  have heq : x 0 + 2 * x 1 = 0 := by
    simpa [L, Fin.sum_univ_two] using hLx 0
  have hbound : height2 x ≤ √2 * √5 := by
    rw [Fintype.card_fin, Fintype.card_fin, NumberField.discr_rat, finrank_self,
      Fin.prod_univ_one, hH] at hxle
    norm_num at hxle
    exact hxle
  have hgen : height2 ![-2, (1 : ℚ)] = √5 := by
    have hcast : ![-2, (1 : ℚ)] = ((↑) : ℤ → ℚ) ∘ ![-2, 1] := by
      ext j
      fin_cases j <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_two]
  have hslack : √5 ≤ √2 * √5 :=
    le_mul_of_one_le_left (Real.sqrt_nonneg 5) (Real.one_le_sqrt.2 one_le_two)
  exact ⟨⟨x, hx0, heq, hbound⟩, hgen, hslack⟩

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
    fin_cases i <;> intro h <;> exact one_ne_zero (congrFun h 0)
  have hrowH (i : Fin 2) : height2 (A.row i) = √2 := by
    have hcast : A.row i = ((↑) : ℤ → ℚ) ∘ ![1, 1, 0] := by
      fin_cases i <;> (ext j; fin_cases j <;> simp [A])
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_three]
  obtain ⟨x, hx0, hAx, hxle⟩ := exists_ne_zero_height2_le hrow (by decide)
  have hmul : A *ᵥ x = 0 := by
    ext i
    simpa [mulVec, dotProduct] using hAx i
  have hbound : height2 x ≤ 2 * √3 := by
    rw [Fintype.card_fin, Fintype.card_fin, NumberField.discr_rat, finrank_self,
      Fin.prod_univ_two, hrowH 0, hrowH 1, Real.mul_self_sqrt zero_le_two] at hxle
    norm_num at hxle
    linarith
  have he₃ : height2 ![(0 : ℚ), 0, 1] = 1 := by
    have hcast : ![(0 : ℚ), 0, 1] = ((↑) : ℤ → ℚ) ∘ ![0, 0, 1] := by
      ext j
      fin_cases j <;> simp
    rw [hcast, height2_intCast_eq_sqrt_of_gcd_eq_one (by decide)]
    norm_num [Fin.sum_univ_three]
  have hrange : LinearMap.range A.mulVecLin = ℚ ∙ ![(1 : ℚ), 1] := by
    ext y
    rw [LinearMap.mem_range, mem_span_singleton]
    constructor
    · rintro ⟨v, rfl⟩
      refine ⟨v 0 + v 1, ?_⟩
      ext i
      fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_three]
    · rintro ⟨c, rfl⟩
      refine ⟨![c, 0, 0], ?_⟩
      ext i
      fin_cases i <;> simp [A, mulVec, dotProduct, Fin.sum_univ_three]
  have hrank : A.rank = 1 := by
    rw [Matrix.rank, hrange, finrank_span_singleton (fun h ↦ one_ne_zero (congrFun h 0))]
  have hnull : Fintype.card (Fin 3) - A.rank = 2 := by simp [hrank]
  obtain ⟨b, hb_li, hb_span, _, _⟩ := A.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le
  exact ⟨⟨x, hx0, hmul, hbound⟩, he₃, hnull, ⟨b, hb_li, hb_span⟩⟩

/-! ### 3. Full-rank `1 × 1` matrix (`U = V = 1`, `k = 0`) -/

open scoped Classical in
example :
    let A : Matrix (Fin 1) (Fin 1) ℚ := !![1]
    LinearMap.ker A.mulVecLin = ⊥ ∧ Fintype.card (Fin 1) - A.rank = 0 := by
  intro A
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    ext v
    simp only [LinearMap.mem_ker, Submodule.mem_bot]
    constructor
    · intro h
      ext i
      fin_cases i
      simpa [A, mulVec, dotProduct] using congrFun h 0
    · rintro rfl
      simp
  have h := A.mulVecLin.finrank_range_add_finrank_ker
  rw [← Matrix.rank, hker, finrank_bot, add_zero, Module.finrank_fintype_fun_eq_card,
    Fintype.card_fin] at h
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
  have hy_cast : (fun j ↦ (y j : K)) = ![(1 : K), (θ : K)] := by
    ext j
    fin_cases j <;> simp [y]
  have : IsTotallyComplex K := GaussianRationals.isTotallyComplex hmin
  have hr₂ : nrComplexPlaces K = 1 := GaussianRationals.nrComplexPlaces_eq_one hmin hgen
  have hdeg : finrank ℚ K = 2 := GaussianRationals.finrank_eq_two hmin hgen
  have hdiscr : discr K = -4 := GaussianRationals.discr_eq_neg_four hmin hgen
  have hθ_sq : (θ : K) ^ 2 = -1 := by
    exact_mod_cast GaussianRationals.sq_eq_neg_one hmin
  have hcard_inf : Fintype.card (InfinitePlace K) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, hr₂,
      zero_add]
  have hker : LinearMap.ker A.mulVecLin = W := by
    ext v
    rw [LinearMap.mem_ker, mulVecLin_apply, mem_span_singleton]
    constructor
    · intro hv
      have hv' : (θ : K) * v 0 + -1 * v 1 = 0 := by
        simpa [A, mulVec, dotProduct, Fin.sum_univ_two] using congrFun hv 0
      refine ⟨v 0, ?_⟩
      ext j
      fin_cases j
      · simp
      · simp only [Fin.mk_one, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        linear_combination hv'
    · rintro ⟨c, rfl⟩
      ext i
      fin_cases i
      simp only [A, mulVec, dotProduct, Fin.sum_univ_two, Fin.isValue, of_apply, cons_val',
        cons_val_zero, cons_val_one, empty_val', cons_val_fin_one, Pi.smul_apply, smul_eq_mul,
        Pi.zero_apply]
      ring
  have hnull : Fintype.card (Fin 2) - A.rank = 1 := by
    have h := A.mulVecLin.finrank_range_add_finrank_ker
    rw [← Matrix.rank, hker, finrank_span_singleton hv0, Module.finrank_fintype_fun_eq_card,
      Fintype.card_fin] at h
    rw [Fintype.card_fin]
    omega
  have hθ_place (w : InfinitePlace K) : w (θ : K) = 1 := by
    have hsq : w (θ : K) ^ 2 = 1 := by
      rw [← w.norm_embedding_eq, ← norm_pow, ← map_pow, hθ_sq, map_neg, map_one, norm_neg, norm_one]
    nlinarith [apply_nonneg w (θ : K)]
  have hH_sup : absoluteProjectiveTupleHeight ![(1 : K), (θ : K)] = 1 := by
    refine le_antisymm ?_ (one_le_absoluteProjectiveTupleHeight _)
    rw [← hy_cast]
    refine absoluteProjectiveTupleHeight_le_of_forall_le hy0 fun j w ↦ ?_
    fin_cases j
    · simp [y]
    · simp [y, hθ_place w]
  have h1_le : 1 ≤ 2 * √(2 / Real.pi) := by
    have hsq : (2⁻¹ : ℝ) ^ 2 ≤ 2 / Real.pi := by
      rw [le_div_iff₀ Real.pi_pos]
      linarith [Real.pi_lt_four]
    have hhalf : (2⁻¹ : ℝ) ≤ √(2 / Real.pi) := Real.le_sqrt_of_sq_le hsq
    linarith
  have hspan_top : Ideal.span (range y) = ⊤ :=
    top_unique fun x _ ↦ by
      simpa [y] using Ideal.mul_mem_left _ x (Ideal.subset_span (s := range y) ⟨0, rfl⟩)
  have hrel : W.relativeSubspaceArakelovHeight = 2 := by
    rw [relativeSubspaceArakelovHeight_span_singleton, ← hy_cast]
    have hprod : arakelovMulHeight (fun j ↦ (y j : K)) * (Ideal.span (range y)).absNorm =
        ∏ w : InfinitePlace K, (∑ j : Fin 2, ‖w.embedding (y j : K)‖ ^ 2) ^ ((w.mult : ℝ) / 2) := by
      rw [arakelovMulHeight_mul_absNorm_span_range y]
      congr!
    rw [hspan_top, Ideal.absNorm_top, Nat.cast_one, mul_one] at hprod
    rw [hprod]
    have hfac (w : InfinitePlace K) :
        (∑ j : Fin 2, ‖w.embedding (y j : K)‖ ^ 2) ^ ((w.mult : ℝ) / 2) = 2 := by
      have hθ_norm : ‖w.embedding (θ : K)‖ ^ 2 = 1 := by
        rw [w.norm_embedding_eq, hθ_place w, one_pow]
      rw [Fin.sum_univ_two, IsTotallyComplex.mult_eq]
      simp only [y, cons_val_zero, cons_val_one, map_one, norm_one, one_pow, hθ_norm]
      norm_num
    simp_rw [hfac]
    rw [Finset.prod_const, Finset.card_univ, hcard_inf, pow_one]
  have hH_W : W.subspaceHeight = √2 := by
    have hp := W.subspaceHeight_pow_finrank
    rw [hdeg, hrel] at hp
    have hsq : W.subspaceHeight ^ 2 = √2 ^ 2 := by rw [hp, Real.sq_sqrt zero_le_two]
    exact (pow_left_inj₀ (Submodule.subspaceHeight_pos W).le (Real.sqrt_nonneg _) two_ne_zero).mp
      hsq
  have hH_row : (span K (range A.row)).subspaceHeight = √2 := by
    rw [← A.subspaceHeight_ker_mulVecLin, hker, hH_W]
  obtain ⟨z, hz_li, hz_span, hz_ker, hz_le⟩ :=
    A.exists_linearIndependent_mulVec_eq_zero_prod_absHeight_le
  let e : Fin 1 ≃ Fin (Fintype.card (Fin 2) - A.rank) := finCongr hnull.symm
  let x : Fin 2 → 𝓞 K := z (e 0)
  have hx_li : LinearIndependent K (fun _ : Fin 1 ↦ fun j ↦ (x j : K)) := by
    simpa [x] using hz_li.comp e e.injective
  have hx_span : span K {fun j ↦ (x j : K)} = LinearMap.ker A.mulVecLin := by
    have hrange : range (fun i : Fin 1 ↦ fun j ↦ (z (e i) j : K)) =
        range (fun l ↦ fun j ↦ (z l j : K)) := by
      ext v
      simp [e.surjective.exists]
    have hsing : ({fun j ↦ (x j : K)} : Set (Fin 2 → K)) =
        range (fun i : Fin 1 ↦ fun j ↦ (z (e i) j : K)) := by
      ext v
      simp [x, eq_comm]
    rw [hsing, hrange, hz_span]
  have hx_le : absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) ≤ 2 * √(2 / Real.pi) := by
    have hprod : absoluteProjectiveTupleHeight (fun j ↦ (x j : K)) =
        ∏ l, absoluteProjectiveTupleHeight (fun j ↦ (z l j : K)) := by
      rw [← e.prod_comp (fun l ↦ absoluteProjectiveTupleHeight fun j ↦ (z l j : K)),
        Fin.prod_univ_one]
    rw [hprod]
    refine hz_le.trans_eq ?_
    rw [hnull, hr₂, hdeg, hdiscr, hH_row]
    have h4 : |((-4 : ℤ) : ℝ)| ^ (((1 : ℕ) : ℝ) / (2 * (2 : ℕ))) = √2 := by
      have habs : |((-4 : ℤ) : ℝ)| = (2 : ℝ) ^ 2 := by norm_num
      rw [habs, ← Real.rpow_natCast (2 : ℝ) 2, ← Real.rpow_mul zero_le_two, Real.sqrt_eq_rpow]
      congr 1
      norm_num
    have hpi : (2 / Real.pi) ^ (((1 : ℕ) * (1 : ℕ) : ℝ) / (2 : ℕ)) = √(2 / Real.pi) := by
      rw [Real.sqrt_eq_rpow]
      congr 1
      norm_num
    rw [h4, hpi]
    calc √(2 / Real.pi) * √2 * √2
        = √(2 / Real.pi) * (√2 * √2) := by ring
      _ = 2 * √(2 / Real.pi) := by rw [Real.mul_self_sqrt zero_le_two, mul_comm]
  exact ⟨hker, hnull, hH_sup, h1_le, ⟨x, hx_li, hx_span, hz_ker (e 0), hx_le⟩⟩

end
