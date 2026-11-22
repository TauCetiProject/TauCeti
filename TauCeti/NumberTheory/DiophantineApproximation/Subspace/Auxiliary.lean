/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.BlockSubst
import TauCeti.Combinatorics.Enumerative.AntidiagLargeDeviation
import TauCeti.LinearAlgebra.Matrix.Determinant.Basic
import TauCeti.NumberTheory.Height.NumberField
import TauCeti.NumberTheory.NumberField.SiegelsLemma
import TauCeti.RingTheory.Algebraic.Denominator

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
* By `Finset.exists_bound_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le`,
  once every `d h` is large enough to absorb the `O(1 / d h)` Chernoff error, the lower-tail
  monomials for a single form number strictly less than `#(multiMons ι d) / (2 #F)`. Clearing the
  denominators of each `A_f⁻¹` and applying `NumberField.exists_ne_zero_mulVec_eq_zero_house_le`
  over `𝓞 K` produces algebraic integer coefficients of house `O(1) ^ ∑ h, d h`, bounded in
  projective height via `NumberField.mulHeight_le_pow_finrank_of_forall_le` and
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

/-- Real-exponential slack bound: if `0 < k ≤ nForms`, `0 < m`, and `4 log (2 nForms) < a * m`,
halving the gap into `ε = (a * m - 4 log (2 nForms)) / (8 * m)` gives
`(2 * k) * exp ((-a / 4 + ε) * m) < 1`. -/
private lemma mul_exp_neg_div_four_add_lt_one {nForms k : ℕ} {a m : ℝ} (hk0 : k ≠ 0)
    (hk : k ≤ nForms) (hm_pos : 0 < m) (hm : 4 * Real.log (2 * nForms) < a * m) :
    (2 * k : ℝ) * Real.exp ((-a / 4 + (a * m - 4 * Real.log (2 * nForms)) / (8 * m)) * m) < 1 := by
  have hk_pos : (0 : ℝ) < 2 * k := by positivity
  have hk_le : (2 * k : ℝ) ≤ 2 * nForms := by exact_mod_cast Nat.mul_le_mul_left 2 hk
  refine (mul_le_mul_of_nonneg_right
    ((Real.exp_log hk_pos).symm.trans_le (Real.exp_le_exp.mpr (Real.log_le_log hk_pos hk_le)))
    (Real.exp_pos _).le).trans_lt ?_
  rw [← Real.exp_add, Real.exp_lt_one_iff]
  have hsum : Real.log (2 * nForms) + ((-a / 4 + (a * m - 4 * Real.log (2 * nForms)) / (8 * m)) *
      m) = -(a * m - 4 * Real.log (2 * nForms)) / 8 := by field_simp [hm_pos.ne']; ring
  linarith

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
    linarith [hm, hlog_nn, show Fintype.card ι * (Fintype.card ι + 1) * η ^ 2 *
      (Fintype.card κ : ℝ) = 0 by rw [hκ0, mul_zero]]
  rw [← sq_abs] at hm
  let ε : ℝ := (Fintype.card ι * (Fintype.card ι + 1) * |η| ^ 2 * Fintype.card κ -
    4 * Real.log (2 * nForms)) / (8 * Fintype.card κ)
  obtain ⟨D₀, hD₀, htail⟩ :=
    exists_bound_card_filter_piFinset_finsuppAntidiag_sum_apply_div_le_div_sub_mul_le
      (univ : Finset ι) (abs_nonneg η) (div_pos (by linarith) (by positivity) : 0 < ε)
  refine ⟨D₀, hD₀, Fintype.card_pos_iff.mp (by exact_mod_cast hm_pos), fun d hd ↦ ?_⟩
  rcases eq_or_ne k 0 with rfl | hk0
  · simp
  let S := Fintype.piFinset fun h ↦ (univ : Finset ι).finsuppAntidiag (d h)
  have hS_pos : 0 < #S := card_pos.mpr ⟨fun h ↦ Finsupp.single i₀ (d h),
    Fintype.mem_piFinset.mpr fun h ↦ mem_finsuppAntidiag.mpr ⟨by simp, subset_univ _⟩⟩
  have hSm_card : #(multiMons ι d) = #S := by
    rw [multiMons_def, card_map]
  have hbad_eq := card_filter_multiMons_eq d fun g ↦
    ∑ h, (g (h, i₀) : ℝ) / d h ≤ Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|
  have hexp_lt : (2 * k : ℝ) * Real.exp ((-#(univ : Finset ι) * (#(univ : Finset ι) + 1) *
      |η| ^ 2 / 4 + ε) * Fintype.card κ) < 1 := by
    rw [card_univ]
    simpa only [ε, neg_mul] using mul_exp_neg_div_four_add_lt_one hk0 hk hm_pos hm
  have htail' : (#{f ∈ S | ∑ h, (f h i₀ : ℝ) / d h ≤
      Fintype.card κ / #(univ : Finset ι) - Fintype.card κ * |η|} : ℝ) ≤
      (#S : ℝ) * Real.exp ((-#(univ : Finset ι) * (#(univ : Finset ι) + 1) * |η| ^ 2 / 4 + ε) *
        Fintype.card κ) := by
    simpa only [S, Fintype.card_piFinset, Nat.cast_prod] using htail d hd (mem_univ i₀)
  have hreal : (2 * (k * #{N ∈ multiMons ι d | ∑ h, (N (h, i₀) : ℝ) / d h ≤
      Fintype.card κ / Fintype.card ι - Fintype.card κ * |η|}) : ℝ) < #(multiMons ι d) := by
    rw [hbad_eq, hSm_card, ← mul_assoc, ← card_univ (α := ι)]
    exact (mul_le_mul_of_nonneg_left htail' (by positivity)).trans_lt
      ((by ring : (2 * k : ℝ) * ((#S : ℝ) * _) = (#S : ℝ) * ((2 * k : ℝ) * _)).trans_lt
        ((mul_lt_mul_of_pos_left hexp_lt (by exact_mod_cast hS_pos)).trans_eq (mul_one _)))
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
  have hc_ex (f : F') : ∃ c : ℕ, c ≠ 0 ∧ ∀ i j : ι, IsIntegral ℤ ((c : K) * (A_f f)⁻¹ i j) := by
    obtain ⟨c, hc0, hint⟩ := Algebra.exists_ne_zero_nsmul_isIntegral_of_isAlgebraic_rat
      (univ : Finset (ι × ι)) (fun q ↦ (A_f f)⁻¹ q.1 q.2)
      fun _ _ ↦ Algebra.IsAlgebraic.isAlgebraic _
    exact ⟨c, hc0, fun i j ↦ by simpa [nsmul_eq_mul] using hint (i, j) (mem_univ _)⟩
  choose c_f hc_ne hint using hc_ex
  let M_f (f : F') : Matrix ι ι (𝓞 K) := fun i j ↦ ⟨(c_f f : K) * (A_f f)⁻¹ i j, hint f i j⟩
  let B_sys : ℝ := 1 + ∑ p : F' × ι × ι, house (M_f p.1 p.2.1 p.2.2 : K)
  have hB1 : 1 ≤ B_sys := le_add_of_nonneg_right (sum_nonneg fun _ _ ↦ house_nonneg _)
  have hM_house (f : F') (i j : ι) : house (M_f f i j : K) ≤ B_sys :=
    (single_le_sum (fun p _ ↦ house_nonneg (M_f p.1 p.2.1 p.2.2 : K))
      (mem_univ (f, i, j))).trans (le_add_of_nonneg_left zero_le_one)
  refine ⟨A_f, c_f, M_f, B_sys, hB1, fun f ↦ ⟨hA_det f, hA_row f, hc_ne f⟩,
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
  rw [house_eq_sup', ← NNReal.coe_mk ((Fintype.card ι * B_sys) ^ ∑ h, d h) (by positivity),
    NNReal.coe_le_coe]
  refine sup'_le univ_nonempty _ fun φ _ ↦ NNReal.coe_le_coe.mp ?_
  rw [NNReal.coe_mk, coe_nnNorm, hcoe, ← hu_deg, ← InfinitePlace.apply, InfinitePlace.coe_apply]
  simpa only [map_one, mul_one] using
    abv_coeff_blockSubst_monomial_le (v := (InfinitePlace.mk φ).val)
      (A := (M_f f).map (algebraMap (𝓞 K) K))
      (fun i j ↦ by
        rw [← InfinitePlace.coe_apply, InfinitePlace.apply, Matrix.map_apply]
        exact (norm_embedding_le_house (M_f f i j : K) φ).trans (hM_house f i j)) u.val 1 N

/-- Assembling a nonzero coefficient vector `ξ : multiMons ι d → 𝓞 K` of bounded house into a
nonzero multihomogeneous polynomial `P` and bounding its projective logarithmic height. -/
private lemma logHeight_sum_multiMons_le_of_house_le {K ι κ : Type*} [Field K] [NumberField K]
    [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] {d : κ → ℕ}
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
  have hP_coeff (u : multiMons ι d) : P.coeff u.val = (ξ u : K) := by
    simp only [P, coeff_sum, coeff_monomial]
    rw [sum_eq_single u (fun v _ hvu ↦ ite_eq_right fun h ↦ hvu (Subtype.ext h)) (by simp)]
    simp
  obtain ⟨u₀, hu₀⟩ := Function.ne_iff.mp hξ0
  have hP0 : P ≠ 0 := fun h0 ↦
    RingOfIntegers.coe_ne_zero_iff.mpr hu₀ (by simpa [h0] using (hP_coeff u₀).symm)
  let K_base : ℝ := C_siegel * Fintype.card ι ^ 2 * B_sys
  have _ : 0 ≤ B_sys := zero_le_one.trans hB1
  have hξK (u : multiMons ι d) (w : InfinitePlace K) : w (ξ u) ≤ K_base ^ ∑ h, d h := by
    rw [← InfinitePlace.norm_embedding_eq]
    refine (norm_embedding_le_house _ _).trans ((hξ_house u).trans ?_)
    rw [Fintype.card_coe]
    calc C_siegel * #(multiMons ι d) * (Fintype.card ι * B_sys) ^ ∑ h, d h
        ≤ C_siegel ^ (∑ h, d h) * (Fintype.card ι ^ ∑ h, d h) *
            (Fintype.card ι * B_sys) ^ ∑ h, d h := by
          gcongr
          · exact le_self_pow₀ hCs1 hD_pos.ne'
          · exact_mod_cast card_multiMons_le_pow d
      _ = K_base ^ ∑ h, d h := by dsimp only [K_base]; rw [mul_pow, mul_pow, mul_pow]; ring
  have hmul : P.mulHeight ≤ (K_base ^ ∑ h, d h) ^ Module.finrank ℚ K := by
    rw [mulHeight_eq_coeff P (multiMons ι d) (isMultiHomogeneous_iff_support_subset.mp hP_hom)]
    simpa only [hP_coeff] using mulHeight_le_pow_finrank_of_forall_le hξ0 hξK
  have hlog := Real.log_le_log (mulHeight_pos P) hmul
  rw [Real.log_pow, Real.log_pow, Nat.cast_sum, ← logHeight_eq_log_mulHeight] at hlog
  exact ⟨hP0, hP_hom, by linarith⟩

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
