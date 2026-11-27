/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.BlockSubst
import TauCeti.Algebra.MvPolynomial.Support
import TauCeti.Combinatorics.Enumerative.AntidiagLargeDeviation
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.NumberTheory.NumberField.House
import TauCeti.NumberTheory.NumberField.SiegelsLemma

/-!
# The multihomogeneous auxiliary polynomial for the Subspace Theorem

Let `K` be a number field, let `F` be a finite set of linear forms in `n = card ι ≥ 2` variables
over `K`, and let `m = card κ` blocks of variables be indexed by `κ × ι`. When `η` and `m` satisfy
`4 log (2 #F) < n (n + 1) η² m`, there exist constants `C₂, C₃ ≥ 0` and a degree threshold `D₀ > 0`
such that for every multidegree `d : κ → ℕ` with `D₀ ≤ d h` in every block `h`, there is a nonzero
multihomogeneous polynomial `P` of multidegree `d` over `K` with:

1. `P.logHeight ≤ C₂ * ∑ h, d h`;
2. for every invertible matrix `A` whose rows belong to `F` and every derivative order `I` of
   weighted order `∑ h, (∑ j, I (h, j)) / d h ≤ m η`, the coefficients of
   `blockSubst A⁻¹ (hasseDeriv I P)` vanish at every exponent vector `J` for which some variable
   position `i : ι` has weighted degree `∑ h, J (h, i) / d h` outside the open interval
   `(m / n - 2 m η, m / n + 2 m (n - 1) η)`;
3. `(blockSubst A⁻¹ (hasseDeriv I P)).logHeight ≤ C₃ * ∑ h, d h` for every matrix `A` with rows in
   `F` and every derivative order `I`.

## Proof overview

Three reductions collapse the system solved by Siegel's lemma to at most `#F` blocks of equations
at derivative order zero:

* Fix one coordinate `i₀ : ι` and extend each nonzero form `f ∈ F` to a single invertible matrix
  `A_f` with row `i₀` equal to `f`. By `MvPolynomial.coeff_blockSubst_inv_eq_zero_of_row_eq`,
  lower-tail vanishing of `blockSubst A_f⁻¹ P` along row `i₀` automatically transfers to every row
  `i` of every invertible matrix `A` with `A i = f`.
* By `MvPolynomial.coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo`, lower-tail vanishing at
  order `0` below `m / n - m η` along every row of `A` propagates to all Hasse derivatives of
  weighted order at most `m η` and upgrades by multihomogeneity (`card ι ≥ 2`) to two-sided
  concentration in `(m / n - 2 m η, m / n + 2 m (n - 1) η)`.
* By `Finset.exists_bound_mul_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_lt`,
  once every `d h` is large enough to absorb the `O(1 / d h)` Chernoff error, `2 #F` copies of the
  lower-tail monomials number strictly less than `#(multiMons ι d)`. Clearing the denominators of
  each `A_f⁻¹` and applying `NumberField.exists_siegelConstant_linear` over `𝓞 K` produces
  algebraic integer coefficients of house `O(1) ^ ∑ h, d h`, bounded in projective height via
  `MvPolynomial.logHeight_le_finrank_mul_log_of_house_le` and
  `MvPolynomial.logHeight_blockSubst_hasseDeriv_le`.

## Main results

* `MvPolynomial.exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero`:
  existence of the multihomogeneous auxiliary polynomial with two-sided concentration and linear
  logarithmic height bounds on all Hasse derivatives.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
  §7.5.14 and Lemma 7.5.15.
* J.-H. Evertse and H. P. Schlickewei, *A quantitative version of the Absolute Subspace Theorem*,
  J. Reine Angew. Math. 548 (2002), 21–127.
* W. M. Schmidt, *Diophantine Approximation*, Lecture Notes in Mathematics 785, Springer (1980),
  Chapter VI.
-/

public section

namespace MvPolynomial

open Finset Height AdmissibleAbsValues Matrix NumberField

section Helpers

/-- Choosing `D₀` from `AntidiagLargeDeviation` so that `2 * k` copies of the lower-tail monomials
fit inside `multiMons ι d` whenever `k ≤ nForms` and
`4 log (2 nForms) < card ι (card ι + 1) η² card κ`. -/
private lemma exists_D0_two_mul_card_filter_multiMons_le {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] (i₀ : ι) {nForms k : ℕ} (hk : k ≤ nForms) {η : ℝ}
    (hm : 4 * Real.log (2 * nForms) <
      Fintype.card ι * (Fintype.card ι + 1) * η ^ 2 * Fintype.card κ) :
    ∃ D₀ : ℕ, 0 < D₀ ∧ Nonempty κ ∧ ∀ d : κ → ℕ, (∀ h, D₀ ≤ d h) →
      2 * (k * #{N ∈ multiMons ι d |
        ∑ h, (N (h, i₀) : ℝ) / d h ≤
          Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|}) ≤ #(multiMons ι d) := by
  have hlog_nn : 0 ≤ Real.log (2 * nForms) := by
    rcases eq_or_ne nForms 0 with rfl | hn0
    · simp
    · have hn1 : (1 : ℝ) ≤ nForms := by exact_mod_cast Nat.pos_of_ne_zero hn0
      exact Real.log_nonneg (by linarith)
  have hm_pos : 0 < (Fintype.card κ : ℝ) := by
    by_contra! hκ
    have hκ0 : (Fintype.card κ : ℝ) = 0 := hκ.antisymm (Nat.cast_nonneg _)
    rw [hκ0, mul_zero] at hm
    linarith
  rw [← sq_abs, ← card_univ (α := ι)] at hm
  obtain ⟨D₀, hD₀, htail⟩ :=
    exists_bound_mul_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_lt
      (univ : Finset ι) (c := (2 * nForms : ℝ)) (by positivity) (abs_nonneg η) hm
  refine ⟨D₀, hD₀, Fintype.card_pos_iff.mp (by exact_mod_cast hm_pos), fun d hd ↦ ?_⟩
  have htail' := htail d hd (mem_univ i₀)
  have hk_le : (2 * k : ℝ) ≤ 2 * nForms := by exact_mod_cast Nat.mul_le_mul_left 2 hk
  have hreal : (2 * (k * #{N ∈ multiMons ι d | ∑ h, (N (h, i₀) : ℝ) / d h ≤
      Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|}) : ℝ) < #(multiMons ι d) := by
    rw [card_filter_multiMons_eq d (fun g ↦
      ∑ h, (g (h, i₀) : ℝ) / d h ≤ Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|),
      card_multiMons_eq_card_piFinset]
    push_cast
    rw [← mul_assoc]
    rw [card_univ] at htail'
    have h1 : (2 * k : ℝ) *
        (#{f ∈ Fintype.piFinset fun h ↦ (univ : Finset ι).finsuppAntidiag (d h) |
          ∑ h, (f h i₀ : ℝ) / d h ≤
            Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|} : ℝ) ≤
        (2 * nForms : ℝ) *
        (#{f ∈ Fintype.piFinset fun h ↦ (univ : Finset ι).finsuppAntidiag (d h) |
          ∑ h, (f h i₀ : ℝ) / d h ≤
            Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|} : ℝ) :=
      mul_le_mul_of_nonneg_right hk_le (Nat.cast_nonneg _)
    linarith [h1, htail']
  exact le_of_lt (by exact_mod_cast hreal)

/-- Extending each nonzero linear form `f ∈ F'` to an invertible matrix `A_f` with row `i₀` equal to
`f`, clearing denominators of `A_f⁻¹` to `M_f` over `𝓞 K`, and bounding the house of every
`blockSubst (M_f f)` monomial coefficient by `(card ι * B_sys) ^ ∑ h, d h`. -/
private lemma exists_matrix_blockSubst_house_le {K ι : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] (i₀ : ι) (F' : Finset (ι → K)) (hF' : ∀ f ∈ F', f ≠ 0) :
    ∃ (A_f : F' → Matrix ι ι K) (c_f : F' → ℕ) (M_f : F' → Matrix ι ι (𝓞 K)) (B_sys : ℝ),
      1 ≤ B_sys ∧
      (∀ f, IsUnit (A_f f).det ∧ A_f f i₀ = f.val ∧ c_f f ≠ 0) ∧
      ∀ {κ : Type*} [Fintype κ] [DecidableEq κ] (d : κ → ℕ) (f : F') (u : multiMons ι d)
        (N : κ × ι →₀ ℕ),
        (((blockSubst (M_f f) (monomial u.val (1 : 𝓞 K))).coeff N : 𝓞 K) : K) =
          (c_f f : K) ^ (∑ h, d h) * (blockSubst (A_f f)⁻¹ (monomial u.val (1 : K))).coeff N ∧
        house (((blockSubst (M_f f) (monomial u.val (1 : 𝓞 K))).coeff N : 𝓞 K) : K) ≤
          (Fintype.card ι * B_sys) ^ ∑ h, d h := by
  classical
  have hA_ex (f : F') : ∃ A : Matrix ι ι K, IsUnit A.det ∧ A i₀ = f.val :=
    let ⟨_, hj₀⟩ := Function.ne_iff.mp (hF' f.val f.property)
    Matrix.exists_isUnit_det_row_eq i₀ (isUnit_iff_ne_zero.mpr hj₀)
  choose A_f hA_det hA_row using hA_ex
  obtain ⟨δ, hδ, G, hG, hx⟩ := NumberField.exists_natCast_mul_isIntegral_house_le
    fun p : F' × ι × ι ↦ (A_f p.1)⁻¹ p.2.1 p.2.2
  let c_f : F' → ℕ := fun _ ↦ δ
  let M_f (f : F') : Matrix ι ι (𝓞 K) := fun i j ↦ ⟨(δ : K) * (A_f f)⁻¹ i j, (hx (f, i, j)).1⟩
  have hG1 : 1 ≤ G := (by exact_mod_cast hδ : (1 : ℝ) ≤ δ).trans hG
  have hM_house (f : F') (i j : ι) : house (M_f f i j : K) ≤ G := (hx (f, i, j)).2
  refine ⟨A_f, c_f, M_f, G, hG1, fun f ↦ ⟨hA_det f, hA_row f, Nat.ne_of_gt hδ⟩,
    fun {κ} _ _ d f u N ↦ ?_⟩
  have hmap : (M_f f).map (algebraMap (𝓞 K) K) = (c_f f : K) • (A_f f)⁻¹ := by
    ext i j
    rw [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
    exact RingOfIntegers.map_mk _ _
  have hcoe : (((blockSubst (M_f f) (monomial u.val (1 : 𝓞 K))).coeff N : 𝓞 K) : K) =
      (blockSubst ((M_f f).map (algebraMap (𝓞 K) K)) (monomial u.val (1 : K))).coeff N := by
    rw [RingOfIntegers.coe_eq_algebraMap, ← coeff_map, map_blockSubst, map_monomial, map_one]
  have hu_hom : IsMultiHomogeneous d (monomial u.val (1 : K)) :=
    isMultiHomogeneous_monomial (mem_multiMons.mp u.property) 1
  have hu_deg : u.val.degree = ∑ h, d h := by
    rw [Finsupp.degree_eq_weight_one (R := ℕ)]
    exact hu_hom.isHomogeneous (by simp)
  refine ⟨by rw [hcoe, hmap, hu_hom.isHomogeneous.blockSubst_smul,
    AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul], ?_⟩
  refine house_le_of_forall_norm_embedding_le (by positivity) fun φ ↦ ?_
  rw [hcoe, ← InfinitePlace.apply, InfinitePlace.coe_apply, ← hu_deg]
  simpa only [map_one, mul_one] using
    abv_coeff_blockSubst_monomial_le (v := (InfinitePlace.mk φ).val)
      (A := (M_f f).map (algebraMap (𝓞 K) K))
      (fun i j ↦ by
        rw [← InfinitePlace.coe_apply, InfinitePlace.apply, Matrix.map_apply]
        exact (norm_embedding_le_house (M_f f i j : K) φ).trans (hM_house f i j)) u.val 1 N

/-- Assembling a nonzero coefficient vector `ξ : multiMons ι d → 𝓞 K` of bounded house into a
nonzero multihomogeneous polynomial `P` and bounding its projective logarithmic height. -/
private lemma logHeight_sum_multiMons_le_of_house_le {K ι κ : Type*} [Field K] [NumberField K]
    [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {d : κ → ℕ}
    (hD_pos : 0 < ∑ h, d h) {C_siegel B_sys : ℝ} (hCs1 : 1 ≤ C_siegel) (hB1 : 1 ≤ B_sys)
    {ξ : multiMons ι d → 𝓞 K} (hξ0 : ξ ≠ 0)
    (hξ_house : ∀ u,
      house (ξ u : K) ≤ C_siegel * Fintype.card (multiMons ι d) *
        (Fintype.card ι * B_sys) ^ ∑ h, d h) :
    let P : MvPolynomial (κ × ι) K := ∑ u : multiMons ι d, monomial u.val (ξ u : K)
    P ≠ 0 ∧ IsMultiHomogeneous d P ∧
      P.logHeight ≤
        (Module.finrank ℚ K * Real.log (C_siegel * Fintype.card ι ^ 2 * B_sys)) *
          ∑ h, (d h : ℝ) := by
  intro P
  have hP_hom : IsMultiHomogeneous d P :=
    IsMultiHomogeneous.sum univ _ fun u _ ↦
      isMultiHomogeneous_monomial (mem_multiMons.mp u.property) _
  have hP_coeff (u : multiMons ι d) : P.coeff u.val = (ξ u : K) :=
    coeff_sum_monomial_of_injOn Subtype.val_injective.injOn (mem_univ u)
  obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hξ0
  have hP0 : P ≠ 0 := fun h0 ↦
    RingOfIntegers.coe_ne_zero_iff.mpr hu₀ (by simpa [h0] using (hP_coeff u₀).symm)
  let K_base : ℝ := C_siegel * Fintype.card ι ^ 2 * B_sys
  have hK1 : 1 ≤ K_base := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCs1 (by exact_mod_cast Nat.pow_le_pow_left Fintype.card_pos 2))
    hB1
  have _ : 0 ≤ B_sys := zero_le_one.trans hB1
  have hP_int : ∀ m ∈ P.support, IsIntegral ℤ (P.coeff m) := fun m hm ↦ by
    let u : multiMons ι d := ⟨m, isMultiHomogeneous_iff_support_subset.mp hP_hom hm⟩
    have hcu : P.coeff m = algebraMap (𝓞 K) K (ξ u) :=
      (hP_coeff u).trans (RingOfIntegers.coe_eq_algebraMap _)
    rw [hcu]
    exact RingOfIntegers.isIntegral_coe (ξ u)
  have hP_house : ∀ m ∈ P.support, house (P.coeff m) ≤ K_base ^ ∑ h, d h := fun m hm ↦ by
    let u : multiMons ι d := ⟨m, isMultiHomogeneous_iff_support_subset.mp hP_hom hm⟩
    have hcu : P.coeff m = (ξ u : K) := hP_coeff u
    rw [hcu]
    refine (hξ_house u).trans ?_
    rw [Fintype.card_coe]
    calc C_siegel * #(multiMons ι d) * (Fintype.card ι * B_sys) ^ ∑ h, d h
        ≤ C_siegel ^ (∑ h, d h) * (Fintype.card ι ^ ∑ h, d h) *
            (Fintype.card ι * B_sys) ^ ∑ h, d h := by
          gcongr
          · exact le_self_pow₀ hCs1 hD_pos.ne'
          · exact_mod_cast card_multiMons_le_pow d
      _ = K_base ^ ∑ h, d h := by dsimp only [K_base]; rw [mul_pow, mul_pow, mul_pow]; ring
  have hlog : P.logHeight ≤ Module.finrank ℚ K * Real.log (K_base ^ ∑ h, d h) :=
    logHeight_le_finrank_mul_log_of_house_le (one_le_pow₀ hK1) hP_int hP_house
  rw [Real.log_pow, Nat.cast_sum] at hlog
  exact ⟨hP0, hP_hom, hlog.trans_eq (by ring)⟩

/-- Solving the cleared-denominator linear system via Siegel's lemma over `𝓞 K` and bounding the
projective logarithmic height of the resulting multihomogeneous polynomial `P`. -/
private lemma exists_isMultiHomogeneous_coeff_blockSubst_eq_zero {K ι κ : Type*} [Field K]
    [NumberField K] [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (i₀ : ι)
    {F' : Finset (ι → K)} {A_f : F' → Matrix ι ι K} {c_f : F' → ℕ} {M_f : F' → Matrix ι ι (𝓞 K)}
    {B_sys : ℝ} (hB1 : 1 ≤ B_sys) (hc_ne : ∀ f, c_f f ≠ 0)
    (hM_sys : ∀ (d : κ → ℕ) (f : F') (u : multiMons ι d) (N : κ × ι →₀ ℕ),
      (((blockSubst (M_f f) (monomial u.val (1 : 𝓞 K))).coeff N : 𝓞 K) : K) =
        (c_f f : K) ^ (∑ h, d h) * (blockSubst (A_f f)⁻¹ (monomial u.val (1 : K))).coeff N ∧
      house (((blockSubst (M_f f) (monomial u.val (1 : 𝓞 K))).coeff N : 𝓞 K) : K) ≤
        (Fintype.card ι * B_sys) ^ ∑ h, d h) :
    ∃ C₂ : ℝ, 0 ≤ C₂ ∧ ∀ {d : κ → ℕ} {θ : ℝ}, 0 < ∑ h, d h →
      2 * (#F' * #{N ∈ multiMons ι d | ∑ h, (N (h, i₀) : ℝ) / d h ≤ θ}) ≤ #(multiMons ι d) →
      ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
        P.logHeight ≤ C₂ * ∑ h, (d h : ℝ) ∧
        ∀ (f : F') (N : κ × ι →₀ ℕ),
          ∑ h, (N (h, i₀) : ℝ) / d h ≤ θ → (blockSubst (A_f f)⁻¹ P).coeff N = 0 := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  obtain ⟨C_siegel, hCs1, hsiegel⟩ := NumberField.exists_siegelConstant_linear K
  let K_base : ℝ := C_siegel * Fintype.card ι ^ 2 * B_sys
  have hK1 : 1 ≤ K_base := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hCs1 (by exact_mod_cast Nat.pow_le_pow_left Fintype.card_pos 2))
    hB1
  let C₂ : ℝ := Module.finrank ℚ K * Real.log K_base
  refine ⟨C₂, mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hK1),
    fun {d θ} hD_pos hcount ↦ ?_⟩
  have hcard_pos : 0 < #(multiMons ι d) :=
    card_pos.mpr ⟨Finsupp.equivFunOnFinite.symm fun p ↦ if p.2 = i₀ then d p.1 else 0,
      mem_multiMons.mpr fun h ↦ by simp⟩
  let bad : Finset (κ × ι →₀ ℕ) := {N ∈ multiMons ι d | ∑ h, (N (h, i₀) : ℝ) / d h ≤ θ}
  let sys : Matrix (F' × bad) (multiMons ι d) (𝓞 K) :=
    fun r u ↦ (blockSubst (M_f r.1) (monomial u.val (1 : 𝓞 K))).coeff r.2.val
  obtain ⟨ξ, hξ0, hsys_eq, hξ_house⟩ := hsiegel sys
    (one_le_pow₀ (one_le_mul_of_one_le_of_one_le (by exact_mod_cast Fintype.card_pos) hB1))
    (by simpa using hcard_pos)
    (by simpa [Fintype.card_prod] using hcount)
    fun r u ↦ (hM_sys d r.1 u r.2.val).2
  let P : MvPolynomial (κ × ι) K := ∑ u : multiMons ι d, monomial u.val (ξ u : K)
  obtain ⟨hP0, hP_hom, hP_log⟩ :=
    logHeight_sum_multiMons_le_of_house_le hD_pos hCs1 hB1 hξ0 hξ_house
  refine ⟨P, hP0, hP_hom, hP_log, fun f N hN ↦ ?_⟩
  by_cases hNm : N ∈ multiMons ι d
  · have hrow0 : ∑ u : multiMons ι d, (sys (f, ⟨N, mem_filter.mpr ⟨hNm, hN⟩⟩) u : K) *
        (ξ u : K) = 0 := by
      simpa [mulVec, dotProduct] using
        congrArg (algebraMap (𝓞 K) K) (congrFun hsys_eq (f, ⟨N, mem_filter.mpr ⟨hNm, hN⟩⟩))
    have hexp : ∑ u : multiMons ι d, (sys (f, ⟨N, mem_filter.mpr ⟨hNm, hN⟩⟩) u : K) *
        (ξ u : K) = (c_f f : K) ^ (∑ h, d h) * (blockSubst (A_f f)⁻¹ P).coeff N := by
      simp only [P, map_sum, coeff_sum, mul_sum]
      refine sum_congr rfl fun u _ ↦ ?_
      have hmon : monomial u.val (ξ u : K) = (ξ u : K) • monomial u.val (1 : K) := by
        rw [smul_monomial, smul_eq_mul, mul_one]
      dsimp only [sys]
      rw [(hM_sys d f u N).1, hmon, map_smul, AddMonoidAlgebra.coeff_smul_apply, smul_eq_mul]; ring
    exact (mul_eq_zero.mp (hexp ▸ hrow0)).resolve_left
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr (hc_ne f)))
  · exact notMem_support_iff.mp fun hs ↦
      hNm (isMultiHomogeneous_iff_support_subset.mp (hP_hom.blockSubst _) hs)

end Helpers

/-- **The multihomogeneous auxiliary polynomial** (Bombieri–Gubler, §7.5.14 and Lemma 7.5.15).
Let `K` be a number field, `F` a finite set of linear forms on `ι` (`card ι ≥ 2`), and `κ` a finite
block index type. If `4 log (2 #F) < card ι (card ι + 1) η² card κ`, there exist `C₂, C₃ ≥ 0` and
`D₀ > 0` such that for every multidegree `d : κ → ℕ` with `D₀ ≤ d h` for all `h`, there is a nonzero
multihomogeneous polynomial `P` of multidegree `d` over `K` whose logarithmic height is at most
`C₂ ∑ h, d h`, whose Hasse derivatives `∂^I P` of weighted order at most `card κ · η` have
coefficients in `blockSubst A⁻¹ (∂^I P)` concentrated inside
`(card κ / card ι - 2 card κ η, card κ / card ι + 2 card κ (card ι - 1) η)` for every invertible
matrix `A` with rows in `F`, and whose transformed derivatives all have logarithmic height at most
`C₃ ∑ h, d h`. -/
theorem exists_ne_zero_isMultiHomogeneous_forall_coeff_blockSubst_hasseDeriv_eq_zero
    {K ι κ : Type*} [Field K] [NumberField K] [Fintype ι] [DecidableEq ι] [Nontrivial ι]
    [Fintype κ] [DecidableEq κ] (F : Finset (ι → K)) {η : ℝ}
    (hm : 4 * Real.log (2 * #F) <
      Fintype.card ι * (Fintype.card ι + 1) * η ^ 2 * Fintype.card κ) :
    ∃ C₂ C₃ : ℝ, ∃ D₀ : ℕ, 0 ≤ C₂ ∧ 0 ≤ C₃ ∧ 0 < D₀ ∧
      ∀ d : κ → ℕ, (∀ h, D₀ ≤ d h) →
        ∃ P : MvPolynomial (κ × ι) K, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
          P.logHeight ≤ C₂ * ∑ h, (d h : ℝ) ∧
          (∀ A : Matrix ι ι K, IsUnit A.det → (∀ i, A i ∈ F) →
            ∀ I : κ × ι →₀ ℕ,
              ∑ h, (∑ j, I (h, j) : ℝ) / d h ≤ Fintype.card κ * η →
              ∀ J : κ × ι →₀ ℕ,
                (∃ i, ∑ h, (J (h, i) : ℝ) / d h ∉
                  Set.Ioo
                    ((Fintype.card κ : ℝ) / Fintype.card ι - 2 * Fintype.card κ * η)
                    ((Fintype.card κ : ℝ) / Fintype.card ι +
                      2 * Fintype.card κ * (Fintype.card ι - 1) * η)) →
                (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0) ∧
          ∀ A : Matrix ι ι K, (∀ i, A i ∈ F) →
            ∀ I : κ × ι →₀ ℕ,
              (blockSubst A⁻¹ (hasseDeriv I P)).logHeight ≤ C₃ * ∑ h, (d h : ℝ) := by
  classical
  obtain ⟨i₀⟩ : Nonempty ι := inferInstance
  let F' : Finset (ι → K) := F.erase 0
  obtain ⟨D₀, hD₀, ⟨h₀⟩, hcount⟩ :=
    exists_D0_two_mul_card_filter_multiMons_le (κ := κ) i₀ (card_erase_le (s := F) (a := 0)) hm
  obtain ⟨A_f, c_f, M_f, B_sys, hB1, hAf_props, hM_sys⟩ :=
    exists_matrix_blockSubst_house_le i₀ F' (fun _ hf ↦ (mem_erase.mp hf).1)
  obtain ⟨C₂, hC₂0, hP_ex⟩ := exists_isMultiHomogeneous_coeff_blockSubst_eq_zero (κ := κ) i₀ hB1
    (fun f ↦ (hAf_props f).2.2) hM_sys
  let S_mat : Finset (Matrix ι ι K) := (Fintype.piFinset fun _ : ι ↦ F).image Matrix.of
  let M_inv : ℝ := ∑ B ∈ S_mat, B⁻¹.logHeight
  let C₃ : ℝ := C₂ + M_inv + totalWeight K * Real.log (2 * Fintype.card ι ^ 2)
  have hcard1 : (1 : ℝ) ≤ Fintype.card ι ^ 2 := by exact_mod_cast Nat.pow_pos Fintype.card_pos
  have hC₃0 : 0 ≤ C₃ := add_nonneg (add_nonneg hC₂0 (sum_nonneg fun B _ ↦ B⁻¹.logHeight_nonneg))
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by linarith)))
  refine ⟨C₂, C₃, D₀, hC₂0, hC₃0, hD₀, fun d hd ↦ ?_⟩
  have hD_pos : 0 < ∑ h, d h := lt_of_lt_of_le (hD₀.trans_le (hd h₀))
    (single_le_sum (fun _ _ ↦ Nat.zero_le _) (mem_univ h₀))
  obtain ⟨P, hP0, hP_hom, hP_log, hAf_vanish⟩ := hP_ex hD_pos (hcount d hd)
  refine ⟨P, hP0, hP_hom, hP_log, fun A hA hAF I hI J ⟨i, hJ⟩ ↦ ?_, fun A hAF I ↦ ?_⟩
  · have hη0 : 0 ≤ η := nonneg_of_mul_nonneg_right
      ((by positivity : (0 : ℝ) ≤ ∑ h, (∑ j, I (h, j) : ℝ) / d h).trans hI)
      (Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨h₀⟩))
    have hI' : ∑ h, ((∑ j, I (h, j) : ℕ) : ℝ) / d h ≤ Fintype.card κ * η := by
      simpa only [Nat.cast_sum] using hI
    refine coeff_blockSubst_hasseDeriv_eq_zero_of_notMem_Ioo hA hP_hom (fun i' N hN ↦ ?_) hI' hJ
    have hAi0 : A i' ≠ 0 := fun h0 ↦ hA.ne_zero
      (det_eq_zero_of_row_eq_zero i' fun j ↦ congrFun h0 j)
    let fi : F' := ⟨A i', mem_erase.mpr ⟨hAi0, hAF i'⟩⟩
    exact coeff_blockSubst_inv_eq_zero_of_row_eq (hAf_props fi).1 (hAf_props fi).2.1
      (fun M hM ↦ hAf_vanish fi M (by rwa [abs_of_nonneg hη0])) hN
  · have hA_mem : A ∈ S_mat := mem_image.mpr ⟨fun i ↦ A i, Fintype.mem_piFinset.mpr hAF, rfl⟩
    have hA_le : A⁻¹.logHeight ≤ M_inv :=
      single_le_sum (fun (B : Matrix ι ι K) _ ↦ B⁻¹.logHeight_nonneg) hA_mem
    have hbh := logHeight_blockSubst_hasseDeriv_le hP_hom A⁻¹ I
    have hmul_le : ((∑ h, d h : ℕ) : ℝ) * A⁻¹.logHeight ≤ ((∑ h, d h : ℕ) : ℝ) * M_inv :=
      mul_le_mul_of_nonneg_left hA_le (Nat.cast_nonneg _)
    rw [Nat.cast_sum] at hbh hmul_le
    dsimp [C₃]; linarith

/-! ### Sharpness of hypotheses -/

/-- The inequality `4 log (2 #F) < card ι (card ι + 1) η² card κ` cannot be dropped: at `η = 0` over
`ℚ`, `ι = Fin 2`, `κ = Fin 1`, and `F = {![1, 0], ![0, 1]}`, the open interval
`Set.Ioo (1 / 2) (1 / 2)` is empty, forcing every coefficient of `P` to vanish. -/
example :
    let F : Finset (Fin 2 → ℚ) := {![1, 0], ![0, 1]}
    ¬ ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ d : Fin 1 → ℕ, (∀ h, D₀ ≤ d h) →
      ∃ P : MvPolynomial (Fin 1 × Fin 2) ℚ, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
        ∀ A : Matrix (Fin 2) (Fin 2) ℚ, IsUnit A.det → (∀ i, A i ∈ F) →
          ∀ I : Fin 1 × Fin 2 →₀ ℕ,
            ∑ h, (∑ j, I (h, j) : ℝ) / d h ≤ Fintype.card (Fin 1) * (0 : ℝ) →
            ∀ J : Fin 1 × Fin 2 →₀ ℕ,
              (∃ i, ∑ h, (J (h, i) : ℝ) / d h ∉
                Set.Ioo ((Fintype.card (Fin 1) : ℝ) / Fintype.card (Fin 2) - 0)
                  ((Fintype.card (Fin 1) : ℝ) / Fintype.card (Fin 2) + 0)) →
              (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  intro F
  rintro ⟨D₀, -, H⟩
  obtain ⟨P, hP0, -, hvan⟩ := H (fun _ ↦ D₀) (fun _ ↦ le_rfl)
  apply hP0
  ext J
  have h1 : ∀ i : Fin 2, (1 : Matrix (Fin 2) (Fin 2) ℚ) i ∈ F := by
    intro i; fin_cases i <;> decide
  simpa using hvan 1 (by simp) h1 0 (by simp) J ⟨0, by simp⟩

/-- `[Nontrivial ι]` cannot be dropped: when `ι = Fin 1`, `κ = Fin 3`, `F = {![1]}`, and `η = 1`,
the block-count hypothesis `4 log 2 < 1 * 2 * 1² * 3` holds, yet every nonzero multihomogeneous
polynomial `P` has weighted degree `3` at its support, lying on the boundary of `(-3, 3)`. -/
example :
    let F : Finset (Fin 1 → ℚ) := {![1]}
    4 * Real.log (2 * #F) <
        Fintype.card (Fin 1) * (Fintype.card (Fin 1) + 1) * (1 : ℝ) ^ 2 * Fintype.card (Fin 3) ∧
      ¬ ∃ D₀ : ℕ, 0 < D₀ ∧ ∀ d : Fin 3 → ℕ, (∀ h, D₀ ≤ d h) →
        ∃ P : MvPolynomial (Fin 3 × Fin 1) ℚ, P ≠ 0 ∧ IsMultiHomogeneous d P ∧
          ∀ A : Matrix (Fin 1) (Fin 1) ℚ, IsUnit A.det → (∀ i, A i ∈ F) →
            ∀ I : Fin 3 × Fin 1 →₀ ℕ,
              ∑ h, (∑ j, I (h, j) : ℝ) / d h ≤ Fintype.card (Fin 3) * (1 : ℝ) →
              ∀ J : Fin 3 × Fin 1 →₀ ℕ,
                (∃ i, ∑ h, (J (h, i) : ℝ) / d h ∉
                  Set.Ioo
                    ((Fintype.card (Fin 3) : ℝ) / Fintype.card (Fin 1) -
                      2 * Fintype.card (Fin 3) * 1)
                    ((Fintype.card (Fin 3) : ℝ) / Fintype.card (Fin 1) +
                      2 * Fintype.card (Fin 3) * (Fintype.card (Fin 1) - 1) * 1)) →
                (blockSubst A⁻¹ (hasseDeriv I P)).coeff J = 0 := by
  intro F
  refine ⟨?_, ?_⟩
  · have hlog : Real.log 2 < 3 / 2 := by
      rw [Real.log_lt_iff_lt_exp zero_lt_two]
      have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      exact h2.trans_lt (Real.exp_lt_exp.mpr (by norm_num))
    simp only [F, card_singleton, Nat.cast_one, mul_one, Fintype.card_fin]
    norm_num
    linarith
  · rintro ⟨D₀, hD₀, H⟩
    obtain ⟨P, hP0, hP, hvan⟩ := H (fun _ ↦ D₀) (fun _ ↦ le_rfl)
    obtain ⟨J, hJ⟩ := support_nonempty.mpr hP0
    have hrow : ∀ i : Fin 1, (1 : Matrix (Fin 1) (Fin 1) ℚ) i ∈ F := by
      intro i; fin_cases i; decide
    have hJsum : ∑ h : Fin 3, (J (h, 0) : ℝ) / D₀ = 3 := by
      have hd0 : (D₀ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hD₀.ne'
      have hJh (h : Fin 3) : J (h, 0) = D₀ := by
        simpa using isMultiHomogeneous_iff.mp hP J (mem_support_iff.mp hJ) h
      simp [hJh, div_self hd0]
    have h0 := hvan 1 (by simp) hrow 0 (by simp) J ⟨0, by simp [hJsum]⟩
    exact mem_support_iff.mp hJ (by simpa using h0)

end MvPolynomial
