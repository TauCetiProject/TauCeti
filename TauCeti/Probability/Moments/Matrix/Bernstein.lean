/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Matrix.Laplace
import TauCeti.Analysis.Matrix.Frobenius

/-!
# Matrix Bernstein inequalities

Let `X₁, …, Xₘ` be independent random Hermitian matrices over `ℝ` or `ℂ` (`[RCLike 𝕜]`) with
entrywise mean zero, and write `V = ∑ₖ E[Xₖ²]` and `v = ‖V‖` (under the Euclidean operator norm
`Matrix.Norms.L2Operator`). Combining Tropp's matrix Laplace transform method from
`TauCeti.Probability.Moments.Matrix.Laplace` with the scalar-to-operator Bernstein exponential bound
`Matrix.IsHermitian.exp_smul_le_one_add_smul_add_sq` yields the matrix Bernstein inequalities:

* Under a one-sided spectral bound `∀ x ∈ spectrum ℝ (Xₖ ω), x ≤ L` a.e. and `MemLp (X k) 2 P`,
  the upper spectral tail satisfies
  `P(∃ x ∈ spectrum ℝ (∑ₖ Xₖ ω), t ≤ x) ≤ card n * exp (-(t ^ 2 / 2) / (v + L * t / 3))`.
* Under a two-sided operator-norm bound `‖Xₖ ω‖ ≤ L` a.e., applying the one-sided bound to `±Xₖ`
  gives `P(t ≤ ‖∑ₖ Xₖ ω‖) ≤ 2 * card n * exp (-(t ^ 2 / 2) / (v + L * t / 3))`.
* For general rectangular `m × n` random matrices `Zₖ` with `‖Zₖ ω‖ ≤ L` a.e., applying the
  Hermitian bound to the Hermitian dilation `fromBlocks 0 Zₖ Zₖᴴ 0` gives
  `P(t ≤ ‖∑ₖ Zₖ ω‖) ≤ 2 * (card m + card n) * exp (-(t ^ 2 / 2) / (v_rect + L * t / 3))`,
  where `v_rect = max ‖∑ₖ E[Zₖ Zₖᴴ]‖ ‖∑ₖ E[Zₖᴴ Zₖ]‖`.

## Main results

* `MeasureTheory.AEMeasurable.integrable_exp_smul_of_spectrum_le`: integrability of `exp (θ • X)`
  on a finite measure space from an almost-everywhere upper bound on the real spectrum of `X`.
* `MeasureTheory.MemLp.integral_exp_smul_le_of_spectrum_le`: Tropp's one-sided Bernstein matrix
  moment-generating-function bound `E[exp (θ • X)] ≤ exp ((θ ^ 2 / (2 * (1 - θ * L / 3))) • E[X²])`.
* `ProbabilityTheory.iIndepFun.measureReal_exists_spectrum_sum_ge_le_of_spectrum_le`: one-sided
  Hermitian matrix Bernstein inequality for the largest eigenvalue.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le_of_isHermitian`: two-sided Hermitian
  matrix Bernstein inequality over `ℝ` or `ℂ`.
* `TauCeti.matrix_bernstein`: complex `d × d` Hermitian matrix Bernstein inequality.
* `ProbabilityTheory.iIndepFun.measureReal_norm_sum_ge_le_of_norm_le`: rectangular matrix Bernstein
  inequality over `ℝ` or `ℂ` via Hermitian dilation.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Foundations of
  Computational Mathematics **12** (2012), 389–434, Theorems 1.4 and 1.6 and §6.1.
* J. A. Tropp, *An Introduction to Matrix Concentration Inequalities*, Foundations and Trends in
  Machine Learning **8** (2015), §6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator

/-! ### Private spectral and Hermitian-dilation helpers -/

section Helpers

variable {m n 𝕜 : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem continuous_exp_matrix_local :
    Continuous (NormedSpace.exp : Matrix n n 𝕜 → Matrix n n 𝕜) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := .restrictScalars ℚ ℝ _
  exact NormedSpace.exp_continuous

private theorem abs_le_norm_of_mem_spectrum {A : Matrix n n 𝕜} (hA : A.IsHermitian) {x : ℝ}
    (hx : x ∈ spectrum ℝ A) : |x| ≤ ‖A‖ := by
  obtain ⟨i, rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  exact (norm_le_pi_norm hA.eigenvalues i).trans_eq hA.l2_opNorm_eq_norm_eigenvalues.symm

private theorem norm_le_of_forall_spectrum_abs_le {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) (h : ∀ x ∈ spectrum ℝ A, |x| ≤ c) : ‖A‖ ≤ c := by
  rw [hA.l2_opNorm_eq_norm_eigenvalues]
  exact (pi_norm_le_iff_of_nonneg hc).2 fun i ↦
    h _ (hA.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)

private theorem le_norm_iff_exists_spectrum_ge {S : Matrix n n 𝕜} (hS : S.IsHermitian) {t : ℝ}
    (ht : 0 < t) :
    t ≤ ‖S‖ ↔ (∃ x ∈ spectrum ℝ S, t ≤ x) ∨ (∃ x ∈ spectrum ℝ (-S), t ≤ x) := by
  refine ⟨fun hnorm ↦ ?_, ?_⟩
  · by_contra! hlt
    by_cases hn : Nonempty n
    · obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty
        (fun j : n ↦ ‖hS.eigenvalues j‖)
      have hmem : hS.eigenvalues i ∈ spectrum ℝ S :=
        hS.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩
      have hmem_neg : -hS.eigenvalues i ∈ spectrum ℝ (-S) := by
        rwa [← spectrum.neg_eq, Set.neg_mem_neg]
      have habs : ‖hS.eigenvalues i‖ < t :=
        abs_lt.2 ⟨by linarith [hlt.2 _ hmem_neg], hlt.1 _ hmem⟩
      have hle : ‖S‖ ≤ ‖hS.eigenvalues i‖ := by
        rw [hS.l2_opNorm_eq_norm_eigenvalues]
        refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun j ↦ ?_
        rw [← hi]
        exact Finset.le_sup' (fun k : n ↦ ‖hS.eigenvalues k‖) (Finset.mem_univ j)
      linarith
    · have : IsEmpty n := not_nonempty_iff.1 hn
      simp [Subsingleton.elim S 0, ht.not_ge] at hnorm
  · rintro (⟨x, hx, htx⟩ | ⟨x, hx, htx⟩)
    · exact htx.trans ((le_abs_self x).trans (abs_le_norm_of_mem_spectrum hS hx))
    · exact htx.trans ((le_abs_self x).trans
        ((abs_le_norm_of_mem_spectrum hS.neg hx).trans_eq (norm_neg S)))

private theorem spectrum_real_fromBlocks_zero (P : Matrix m m 𝕜) (Q : Matrix n n 𝕜) :
    spectrum ℝ (fromBlocks P 0 0 Q) = spectrum ℝ P ∪ spectrum ℝ Q := by
  ext x
  simp only [spectrum.mem_iff, Set.mem_union, isUnit_iff_isUnit_det, isUnit_iff_ne_zero, not_ne_iff]
  have hsub : algebraMap ℝ (Matrix (m ⊕ n) (m ⊕ n) 𝕜) x - fromBlocks P 0 0 Q =
      fromBlocks (algebraMap ℝ _ x - P) 0 0 (algebraMap ℝ _ x - Q) := by
    ext (i | i) (j | j) <;> simp [Algebra.algebraMap_eq_smul_one, Matrix.one_apply]
  rw [hsub, det_fromBlocks_zero₂₁, mul_eq_zero]

private theorem l2_opNorm_fromBlocks_zero {P : Matrix m m 𝕜} {Q : Matrix n n 𝕜}
    (hP : P.IsHermitian) (hQ : Q.IsHermitian) :
    ‖fromBlocks P 0 0 Q‖ = max ‖P‖ ‖Q‖ := by
  set H := fromBlocks P 0 0 Q
  have hH : H.IsHermitian := hP.fromBlocks conjTranspose_zero hQ
  apply le_antisymm
  · refine norm_le_of_forall_spectrum_abs_le hH (by positivity) fun x hx ↦ ?_
    rcases (spectrum_real_fromBlocks_zero P Q ▸ hx : x ∈ spectrum ℝ P ∪ spectrum ℝ Q) with h | h
    · exact (abs_le_norm_of_mem_spectrum hP h).trans (le_max_left _ _)
    · exact (abs_le_norm_of_mem_spectrum hQ h).trans (le_max_right _ _)
  · refine max_le ?_ ?_
    · exact norm_le_of_forall_spectrum_abs_le hP (norm_nonneg H) fun x hx ↦
        abs_le_norm_of_mem_spectrum hH (spectrum_real_fromBlocks_zero P Q ▸ Or.inl hx)
    · exact norm_le_of_forall_spectrum_abs_le hQ (norm_nonneg H) fun x hx ↦
        abs_le_norm_of_mem_spectrum hH (spectrum_real_fromBlocks_zero P Q ▸ Or.inr hx)

private theorem l2_opNorm_fromBlocks_zero_conjTranspose (M : Matrix m n 𝕜) :
    ‖fromBlocks (0 : Matrix m m 𝕜) M Mᴴ (0 : Matrix n n 𝕜)‖ = ‖M‖ := by
  set D := fromBlocks (0 : Matrix m m 𝕜) M Mᴴ (0 : Matrix n n 𝕜)
  have hD : D.IsHermitian := isHermitian_zero.fromBlocks rfl isHermitian_zero
  have hsq : ‖D‖ * ‖D‖ = ‖M‖ * ‖M‖ := by
    calc ‖D‖ * ‖D‖
        = ‖Dᴴ * D‖ := (l2_opNorm_conjTranspose_mul_self D).symm
      _ = ‖fromBlocks (M * Mᴴ) 0 0 (Mᴴ * M)‖ := by
          rw [hD.eq]
          simp [D, fromBlocks_multiply]
      _ = max ‖M * Mᴴ‖ ‖Mᴴ * M‖ :=
          l2_opNorm_fromBlocks_zero (isHermitian_mul_conjTranspose_self M)
            (isHermitian_conjTranspose_mul_self M)
      _ = ‖M‖ * ‖M‖ := by
          have h1 : ‖M * Mᴴ‖ = ‖M‖ * ‖M‖ := by
            simpa [conjTranspose_conjTranspose, l2_opNorm_conjTranspose] using
              l2_opNorm_conjTranspose_mul_self Mᴴ
          rw [h1, l2_opNorm_conjTranspose_mul_self M, max_self]
  nlinarith [norm_nonneg D, norm_nonneg M]

end Helpers

/-! ### Bernstein MGF bound for a single random Hermitian matrix -/

section SingleMatrix

variable {Ω n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [Fintype n] [DecidableEq n]
  [RCLike 𝕜]

/-- If an almost everywhere measurable and almost everywhere Hermitian random matrix `X` on a finite
measure space has real spectrum bounded above by `L` almost surely, then `exp (θ • X)` is Bochner
integrable for every `θ ≥ 0`. -/
theorem MeasureTheory.AEMeasurable.integrable_exp_smul_of_spectrum_le [IsFiniteMeasure P]
    {X : Ω → Matrix n n 𝕜} (hX : AEMeasurable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    {L θ : ℝ} (hθ : 0 ≤ θ) (hbound : ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X ω), x ≤ L) :
    Integrable (fun ω ↦ NormedSpace.exp (θ • X ω)) P := by
  have hasm : AEStronglyMeasurable (fun ω ↦ NormedSpace.exp (θ • X ω)) P :=
    (continuous_exp_matrix_local.comp (continuous_const_smul θ)).comp_aestronglyMeasurable
      hX.aestronglyMeasurable
  refine Integrable.of_bound hasm (Real.exp (θ * L)) ?_
  filter_upwards [hherm, hbound] with ω hω hspec
  have hθX : (θ • X ω).IsHermitian := hω.smul (IsSelfAdjoint.all θ)
  refine norm_le_of_forall_spectrum_abs_le hθX.posDef_exp.isHermitian (Real.exp_pos _).le
    fun y hy ↦ ?_
  rw [← hθX.cfc_exp_eq_exp,
    ← cfc_comp_const_mul θ Real.exp (X ω) Real.continuous_exp.continuousOn hω.isSelfAdjoint,
    cfc_map_spectrum (fun x ↦ Real.exp (θ * x)) (X ω) hω.isSelfAdjoint
      (Real.continuous_exp.comp (continuous_const.mul continuous_id)).continuousOn] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (hspec x hx) hθ)

/-- **Matrix Bernstein moment-generating-function bound** (Tropp 2012, Lemma 6.2). If `X` is a
square-integrable almost everywhere Hermitian random matrix on a probability space with entrywise
mean zero and real spectrum bounded above by `L ≥ 0` almost surely, then for `0 ≤ θ` with
`θ * L < 3`,
`E[exp (θ • X)] ≤ exp ((θ ^ 2 / (2 * (1 - θ * L / 3))) • E[X * X])`. -/
theorem MeasureTheory.MemLp.integral_exp_smul_le_of_spectrum_le [IsProbabilityMeasure P]
    {X : Ω → Matrix n n 𝕜} (hX : MemLp X 2 P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0) {L θ : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X ω), x ≤ L) (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    (Matrix.of fun i j ↦ ∫ ω, NormedSpace.exp (θ • X ω) i j ∂P) ≤
      NormedSpace.exp
        ((θ ^ 2 / (2 * (1 - θ * L / 3))) • Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P) := by
  set g := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hg : 0 ≤ g := div_nonneg (sq_nonneg θ) (by linarith)
  have hX1 : Integrable X P := hX.integrable one_le_two
  have hX2 : Integrable (fun ω ↦ X ω * X ω) P := hX.integrable_mul hX
  have hexp_int : Integrable (fun ω ↦ NormedSpace.exp (θ • X ω)) P :=
    hX.aestronglyMeasurable.aemeasurable.integrable_exp_smul_of_spectrum_le hherm hθ hbound
  have hrhs_int : Integrable (fun ω ↦ (1 : Matrix n n 𝕜) + θ • X ω + g • (X ω * X ω)) P :=
    ((integrable_const _).add (Matrix.integrable_iff.2 fun i j ↦
      ((Matrix.integrable_iff.1 hX1) i j).smul θ)).add
      (Matrix.integrable_iff.2 fun i j ↦ ((Matrix.integrable_iff.1 hX2) i j).smul g)
  have hpt : ∀ᵐ ω ∂P,
      NormedSpace.exp (θ • X ω) ≤ (1 : Matrix n n 𝕜) + θ • X ω + g • (X ω * X ω) := by
    filter_upwards [hherm, hbound] with ω hω hspec
    simpa only [sq, g] using hω.exp_smul_le_one_add_smul_add_sq hθ hL hθL fun i ↦
      hspec _ (hω.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)
  have hint_le := Matrix.of_integral_mono_ae hexp_int hrhs_int hpt
  have hrhs_eq : (Matrix.of fun i j ↦
      ∫ ω, ((1 : Matrix n n 𝕜) + θ • X ω + g • (X ω * X ω)) i j ∂P) =
        1 + g • Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P := by
    apply Matrix.ext
    intro i j
    have hi1 : Integrable (fun ω ↦ (θ : 𝕜) * X ω i j) P :=
      ((Matrix.integrable_iff.1 hX1) i j).const_mul (θ : 𝕜)
    have hi2 : Integrable (fun ω ↦ (g : 𝕜) * (X ω * X ω) i j) P :=
      ((Matrix.integrable_iff.1 hX2) i j).const_mul (g : 𝕜)
    have hc : Integrable (fun _ : Ω ↦ (if i = j then (1 : 𝕜) else 0)) P := integrable_const _
    have hc1 : Integrable (fun ω ↦ (if i = j then (1 : 𝕜) else 0) + (θ : 𝕜) * X ω i j) P :=
      hc.add hi1
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul]
    rw [integral_add hc1 hi2, integral_add hc hi1, integral_const, probReal_univ, one_smul,
      integral_const_mul, hmean i j, mul_zero, add_zero, integral_const_mul]
  have hV_psd : (Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P).PosSemidef := by
    refine TauCeti.posSemidef_integral ?_ (Matrix.integrable_iff.1 hX2)
    filter_upwards [hherm] with ω hω
    simpa only [hω.eq] using posSemidef_conjTranspose_mul_self (X ω)
  exact (hrhs_eq ▸ hint_le).trans (hV_psd.smul hg).isHermitian.one_add_le_exp

end SingleMatrix

/-! ### Hermitian and rectangular matrix Bernstein inequalities -/

namespace ProbabilityTheory.iIndepFun

variable {Ω ι m n 𝕜 : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] [RCLike 𝕜]

private theorem integrable_and_integral_re_trace {M : Ω → Matrix n n 𝕜} (hM : Integrable M P) :
    Integrable (fun ω ↦ RCLike.re (M ω).trace) P ∧
      ∫ ω, RCLike.re (M ω).trace ∂P = ∑ i : n, RCLike.re (∫ ω, M ω i i ∂P) := by
  have hent := Matrix.integrable_iff.1 hM
  have hfn : (fun ω ↦ RCLike.re (M ω).trace) = fun ω ↦ ∑ i : n, RCLike.reCLM (M ω i i) := by
    ext ω
    simp [Matrix.trace]
  refine ⟨hfn ▸ integrable_finsetSum Finset.univ fun i _ ↦ RCLike.reCLM.integrable_comp (hent i i),
    ?_⟩
  rw [hfn, integral_finsetSum Finset.univ fun i _ ↦ RCLike.reCLM.integrable_comp (hent i i)]
  exact Finset.sum_congr rfl fun i _ ↦ by
    simpa using RCLike.reCLM.integral_comp_comm (hent i i)

private theorem ae_sum_eq_zero_of_opNorm_sum_integral_mul_self_eq_zero
    {X : ι → Ω → Matrix n n 𝕜} {s : Finset ι} (hX : ∀ k ∈ s, MemLp (X k) 2 P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hv : ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ = 0) :
    ∀ᵐ ω ∂P, ∑ k ∈ s, X k ω = 0 := by
  have hV0 : (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P) = 0 :=
    norm_eq_zero.1 hv
  have htr (k : ι) (hk : k ∈ s) :=
    integrable_and_integral_re_trace ((hX k hk).integrable_mul (hX k hk) :
      Integrable (fun ω ↦ X k ω * X k ω) P)
  have htr_nn (k : ι) (hk : k ∈ s) :
      0 ≤ᵐ[P] fun ω ↦ RCLike.re (X k ω * X k ω).trace := by
    filter_upwards [hherm k hk] with ω hω
    change 0 ≤ RCLike.re (X k ω * X k ω).trace
    nth_rw 2 [← hω.eq]
    rw [re_trace_mul_conjTranspose_self]
    positivity
  have hsum_tr : ∑ k ∈ s, ∫ ω, RCLike.re (X k ω * X k ω).trace ∂P = 0 := by
    have h0 : RCLike.re (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P).trace = 0 := by
      simp [hV0]
    rw [← h0, Matrix.trace]
    simp only [diag_apply, of_apply, map_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k hk ↦ (htr k hk).2
  have hk_zero : ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω = 0 := fun k hk ↦ by
    have hint0 : ∫ ω, RCLike.re (X k ω * X k ω).trace ∂P = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun j hj ↦ integral_nonneg_of_ae (htr_nn j hj)).1
        hsum_tr k hk
    have hae0 := (integral_eq_zero_iff_of_nonneg_ae (htr_nn k hk) (htr k hk).1).1 hint0
    filter_upwards [hherm k hk, hae0] with ω hω hω0
    change RCLike.re (X k ω * X k ω).trace = 0 at hω0
    nth_rw 2 [← hω.eq] at hω0
    rw [re_trace_mul_conjTranspose_self] at hω0
    ext i j
    have hij : ‖X k ω i j‖ ^ 2 = 0 := by
      have hrow := (Finset.sum_eq_zero_iff_of_nonneg fun r _ ↦
        Finset.sum_nonneg fun c _ ↦ sq_nonneg ‖X k ω r c‖).1 hω0 i (Finset.mem_univ i)
      exact (Finset.sum_eq_zero_iff_of_nonneg fun c _ ↦ sq_nonneg _).1 hrow j (Finset.mem_univ j)
    exact norm_eq_zero.1 (sq_eq_zero_iff.1 hij)
  filter_upwards [(Filter.eventually_all_finset s).2 hk_zero] with ω hω
  exact Finset.sum_eq_zero hω

private theorem nonneg_of_mean_zero_of_spectrum_le [IsProbabilityMeasure P] [Nonempty n]
    {X : Ω → Matrix n n 𝕜} (hX : Integrable X P) (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0) {L : ℝ}
    (hbound : ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X ω), x ≤ L) : 0 ≤ L := by
  obtain ⟨hf_int, hf_eq⟩ := integrable_and_integral_re_trace hX
  have hf_mean : ∫ ω, RCLike.re (X ω).trace ∂P = 0 := by simp [hf_eq, hmean]
  have hf_le : ∀ᵐ ω ∂P, RCLike.re (X ω).trace ≤ Fintype.card n * L := by
    filter_upwards [hherm, hbound] with ω hω hspec
    rw [hω.trace_eq_sum_eigenvalues]
    simpa using Finset.sum_le_card_nsmul Finset.univ hω.eigenvalues L fun i _ ↦
      hspec _ (hω.spectrum_real_eq_range_eigenvalues ▸ ⟨i, rfl⟩)
  have hcardL : 0 ≤ (Fintype.card n : ℝ) * L := by
    simpa [hf_mean] using integral_mono_ae hf_int (integrable_const _) hf_le
  exact (mul_nonneg_iff_of_pos_left (Nat.cast_pos.2 Fintype.card_pos)).1 hcardL

private theorem measureReal_exists_spectrum_sum_ge_le_of_pos
    {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P) {s : Finset ι}
    (hX : ∀ k ∈ s, MemLp (X k) 2 P) (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0) {L : ℝ} (hL : 0 ≤ L)
    (hbound : ∀ k ∈ s, ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X k ω), x ≤ L) {t : ℝ} (ht : 0 < t)
    (hv : 0 < ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖) :
    P.real {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  set V := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P
  set v := ‖V‖
  have hD : 0 < v + L * t / 3 := by positivity
  set θ := t / (v + L * t / 3)
  have hθ : 0 ≤ θ := by positivity
  have hθL : θ * L < 3 := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
    nlinarith
  set g := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hg : 0 ≤ g := div_nonneg (sq_nonneg θ) (by linarith)
  set A : ι → Matrix n n 𝕜 := fun k ↦ g • Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P
  have hA_herm : ∀ k ∈ s, (A k).IsHermitian := fun k hk ↦ by
    have hVk : (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P).PosSemidef := by
      refine TauCeti.posSemidef_integral ?_
        (Matrix.integrable_iff.1 ((hX k hk).integrable_mul (hX k hk)))
      filter_upwards [hherm k hk] with ω hω
      simpa only [hω.eq] using posSemidef_conjTranspose_mul_self (X k ω)
    exact (hVk.smul hg).isHermitian
  have hsum_A : ∑ k ∈ s, A k = g • V := by ext i j; simp [A, V, Finset.smul_sum]
  have htail := hindep.measureReal_exists_spectrum_sum_ge_le
    (fun k hk ↦ (hX k hk).aestronglyMeasurable.aemeasurable) hherm hθ hA_herm
    (fun k hk ↦ (hX k hk).aestronglyMeasurable.aemeasurable.integrable_exp_smul_of_spectrum_le
      (hherm k hk) hθ (hbound k hk))
    (fun k hk ↦ (hX k hk).integral_exp_smul_le_of_spectrum_le (hherm k hk) (hmean k hk) hL
      (hbound k hk) hθ hθL) t
  refine htail.trans_eq ?_
  rw [hsum_A, RCLike.real_smul_eq_coe_smul (K := 𝕜), norm_smul, RCLike.norm_ofReal,
    abs_of_nonneg hg]
  congr 2
  have hD3 : t * L + v * 3 ≠ 0 := by linarith
  have hv0 : v ≠ 0 := hv.ne'
  simp only [g, θ, v] at hD3 hv0 ⊢
  field_simp
  ring

/-- **Matrix Bernstein inequality, one-sided eigenvalue form** (Tropp 2012, Theorem 1.4). Let `Xₖ`
(`k ∈ s`) be independent square-integrable almost everywhere Hermitian random matrices with
entrywise mean zero and real spectrum bounded above by `L` almost surely, and set
`v = ‖∑ k ∈ s, E[Xₖ²]‖`. Then for every `t ≥ 0`,
`P(∃ x ∈ spectrum ℝ (∑ k ∈ s, Xₖ ω), t ≤ x) ≤ card n * exp (-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem measureReal_exists_spectrum_sum_ge_le_of_spectrum_le
    {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P) {s : Finset ι}
    (hX : ∀ k ∈ s, MemLp (X k) 2 P) (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0) {L : ℝ}
    (hbound : ∀ k ∈ s, ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X k ω), x ≤ L) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x} ≤
      Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases ht.eq_or_lt with rfl | ht
  · by_cases hn : Nonempty n
    · have h1 : (1 : ℝ) ≤ Fintype.card n := Nat.one_le_cast.2 Fintype.card_pos
      simpa using measureReal_le_one.trans h1
    · have : IsEmpty n := not_nonempty_iff.1 hn
      simp [spectrum.of_subsingleton]
  set V := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P
  rcases (norm_nonneg V).eq_or_lt with hv | hv
  · have hzero := ae_sum_eq_zero_of_opNorm_sum_integral_mul_self_eq_zero hX hherm hv.symm
    have hnull : P.real {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x} = 0 := by
      rw [measureReal_eq_zero_iff]
      refine measure_mono_null (fun ω ⟨x, hx, htx⟩ ↦ ?_) (ae_iff.1 hzero)
      intro hsum0
      rw [hsum0] at hx
      have hx0 := abs_le_norm_of_mem_spectrum (isHermitian_zero : (0 : Matrix n n 𝕜).IsHermitian) hx
      simp only [norm_zero, abs_nonpos_iff] at hx0
      linarith
    rw [hnull]
    positivity
  -- Positive variance forces both `n` and `s` to be nonempty, whence `0 ≤ L`.
  have : Nonempty n := by_contra fun hn ↦ hv.ne' (by
    have := not_nonempty_iff.1 hn
    simp [Subsingleton.elim V 0])
  obtain ⟨k₀, hk₀⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.2 fun hs0 ↦ by
    subst hs0
    refine hv.ne' ?_
    have hV_empty : V = 0 := by ext; simp [V]
    simp [hV_empty]
  have hL : 0 ≤ L := nonneg_of_mean_zero_of_spectrum_le ((hX k₀ hk₀).integrable one_le_two)
    (hherm k₀ hk₀) (hmean k₀ hk₀) (hbound k₀ hk₀)
  exact hindep.measureReal_exists_spectrum_sum_ge_le_of_pos hX hherm hmean hL hbound ht hv

/-- **Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4 applied to `±Xₖ`). Let `Xₖ`
(`k ∈ s`) be independent almost everywhere measurable and almost everywhere Hermitian random
matrices over `ℝ` or `ℂ` with entrywise mean zero and `‖Xₖ ω‖ ≤ L` almost surely. Then for every
`t > 0`,
`P(t ≤ ‖∑ k ∈ s, Xₖ ω‖) ≤ 2 * card n * exp (-(t ^ 2 / 2) / (‖∑ k ∈ s, E[Xₖ²]‖ + L * t / 3))`. -/
theorem measureReal_norm_sum_ge_le_of_isHermitian
    {X : ι → Ω → Matrix n n 𝕜} (hindep : iIndepFun X P) {s : Finset ι}
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P) (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0) {L : ℝ}
    (hbound : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ L) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤
      2 * Fintype.card n * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hL2 : ∀ k ∈ s, MemLp (X k) 2 P := fun k hk ↦
    MemLp.of_bound (hmeas k hk).aestronglyMeasurable L (hbound k hk)
  have hspec_pos : ∀ k ∈ s, ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (X k ω), x ≤ L := fun k hk ↦ by
    filter_upwards [hherm k hk, hbound k hk] with ω hω hωL x hx
    exact (le_abs_self x).trans ((abs_le_norm_of_mem_spectrum hω hx).trans hωL)
  have hspec_neg : ∀ k ∈ s, ∀ᵐ ω ∂P, ∀ x ∈ spectrum ℝ (-X k ω), x ≤ L := fun k hk ↦ by
    filter_upwards [hherm k hk, hbound k hk] with ω hω hωL x hx
    exact (le_abs_self x).trans
      ((abs_le_norm_of_mem_spectrum hω.neg hx).trans ((norm_neg _).trans_le hωL))
  have hneg_indep : iIndepFun (fun k ω ↦ -X k ω) P :=
    hindep.comp (fun _ ↦ Neg.neg) fun _ ↦ measurable_neg
  have hup := hindep.measureReal_exists_spectrum_sum_ge_le_of_spectrum_le hL2 hherm hmean
    hspec_pos ht.le
  have hlow := hneg_indep.measureReal_exists_spectrum_sum_ge_le_of_spectrum_le (s := s)
    (fun k hk ↦ (hL2 k hk).neg) (fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.neg)
    (fun k hk i j ↦ by simpa [integral_neg] using hmean k hk i j) hspec_neg ht.le
  simp only [neg_mul_neg, Finset.sum_neg_distrib] at hlow
  have hsum_herm : ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian := by
    filter_upwards [(Filter.eventually_all_finset s).2 hherm] with ω hω
    rw [IsHermitian, conjTranspose_sum]
    exact Finset.sum_congr rfl fun k hk ↦ (hω k hk).eq
  have hnull : P.real {ω | ¬(∑ k ∈ s, X k ω).IsHermitian} = 0 :=
    (measureReal_eq_zero_iff).2 (ae_iff.1 hsum_herm)
  set Epos := {ω | ∃ x ∈ spectrum ℝ (∑ k ∈ s, X k ω), t ≤ x}
  set Eneg := {ω | ∃ x ∈ spectrum ℝ (-∑ k ∈ s, X k ω), t ≤ x}
  have hincl : {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ⊆
      (Epos ∪ Eneg) ∪ {ω | ¬(∑ k ∈ s, X k ω).IsHermitian} := by
    intro ω hω
    by_cases hh : (∑ k ∈ s, X k ω).IsHermitian
    · exact Or.inl ((le_norm_iff_exists_spectrum_ge hh ht).1 hω)
    · exact Or.inr hh
  calc P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖}
      ≤ P.real ((Epos ∪ Eneg) ∪ {ω | ¬(∑ k ∈ s, X k ω).IsHermitian}) := measureReal_mono hincl
    _ ≤ P.real (Epos ∪ Eneg) + P.real {ω | ¬(∑ k ∈ s, X k ω).IsHermitian} :=
        measureReal_union_le _ _
    _ ≤ P.real Epos + P.real Eneg := by rw [hnull, add_zero]; exact measureReal_union_le _ _
    _ ≤ _ := (add_le_add hup hlow).trans_eq (by ring)

/-- **Rectangular matrix Bernstein inequality** (Tropp 2012, Theorem 1.6). Let `Zₖ` (`k ∈ s`) be
independent almost everywhere measurable `m × n` random matrices over `ℝ` or `ℂ` with entrywise
mean zero and `‖Zₖ ω‖ ≤ L` almost surely. Then for every `t > 0`,
`P(t ≤ ‖∑ k ∈ s, Zₖ ω‖) ≤ 2 * (card m + card n) * exp (-(t ^ 2 / 2) / (v + L * t / 3))`, where
`v = max ‖∑ k ∈ s, E[Zₖ Zₖᴴ]‖ ‖∑ k ∈ s, E[Zₖᴴ Zₖ]‖`. -/
theorem measureReal_norm_sum_ge_le_of_norm_le
    {Z : ι → Ω → Matrix m n 𝕜} (hindep : iIndepFun Z P) {s : Finset ι}
    (hmeas : ∀ k ∈ s, AEMeasurable (Z k) P)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, Z k ω i j ∂P = 0) {L : ℝ}
    (hbound : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ L) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} ≤
      2 * (Fintype.card m + Fintype.card n) * Real.exp (-(t ^ 2 / 2) /
        (max ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (Z k ω * (Z k ω)ᴴ) i j ∂P‖
          ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, ((Z k ω)ᴴ * Z k ω) i j ∂P‖ + L * t / 3)) := by
  let dilate : Matrix m n 𝕜 → Matrix (m ⊕ n) (m ⊕ n) 𝕜 := fun M ↦ fromBlocks 0 M Mᴴ 0
  have hdil_cont : Continuous dilate :=
    Continuous.matrix_fromBlocks continuous_const continuous_id
      continuous_id.matrix_conjTranspose continuous_const
  have hindep_D : iIndepFun (fun k ω ↦ dilate (Z k ω)) P :=
    hindep.comp (fun _ ↦ dilate) fun _ ↦ hdil_cont.measurable
  have hmean_D : ∀ k ∈ s, ∀ p q, ∫ ω, dilate (Z k ω) p q ∂P = 0 := by
    intro k hk p q
    rcases p with i | i <;> rcases q with j | j <;>
      simp [dilate, hmean k hk, RCLike.star_def, integral_conj]
  have hbound_D : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖dilate (Z k ω)‖ ≤ L := fun k hk ↦ by
    simpa only [dilate, l2_opNorm_fromBlocks_zero_conjTranspose] using hbound k hk
  have hD := hindep_D.measureReal_norm_sum_ge_le_of_isHermitian (s := s)
    (fun k hk ↦ hdil_cont.measurable.comp_aemeasurable (hmeas k hk))
    (fun _ _ ↦ .of_forall fun _ ↦ isHermitian_zero.fromBlocks rfl isHermitian_zero)
    hmean_D hbound_D ht
  have hsum_norm : ∀ ω, ‖∑ k ∈ s, dilate (Z k ω)‖ = ‖∑ k ∈ s, Z k ω‖ := fun ω ↦ by
    have hsum_eq : ∑ k ∈ s, dilate (Z k ω) = dilate (∑ k ∈ s, Z k ω) := by
      ext (i | i) (j | j) <;> simp [dilate]
    rw [hsum_eq, l2_opNorm_fromBlocks_zero_conjTranspose]
  set V₁ := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (Z k ω * (Z k ω)ᴴ) i j ∂P
  set V₂ := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, ((Z k ω)ᴴ * Z k ω) i j ∂P
  have hV₁ : V₁.IsHermitian := by
    ext i j
    simp only [V₁, conjTranspose_apply, of_apply, RCLike.star_def, map_sum, ← integral_conj]
    refine Finset.sum_congr rfl fun k _ ↦ integral_congr_ae (.of_forall fun ω ↦ ?_)
    simpa only [conjTranspose_apply, RCLike.star_def] using
      congr_fun₂ (isHermitian_mul_conjTranspose_self (Z k ω)).eq i j
  have hV₂ : V₂.IsHermitian := by
    ext i j
    simp only [V₂, conjTranspose_apply, of_apply, RCLike.star_def, map_sum, ← integral_conj]
    refine Finset.sum_congr rfl fun k _ ↦ integral_congr_ae (.of_forall fun ω ↦ ?_)
    simpa only [conjTranspose_apply, RCLike.star_def] using
      congr_fun₂ (isHermitian_conjTranspose_mul_self (Z k ω)).eq i j
  have hV_eq : (Matrix.of fun p q ↦ ∑ k ∈ s, ∫ ω, (dilate (Z k ω) * dilate (Z k ω)) p q ∂P) =
      fromBlocks V₁ 0 0 V₂ := by
    ext (i | i) (j | j) <;> simp [dilate, V₁, V₂, fromBlocks_multiply]
  simp only [hsum_norm, hV_eq, l2_opNorm_fromBlocks_zero hV₁ hV₂, Fintype.card_sum,
    Nat.cast_add] at hD
  exact hD

end ProbabilityTheory.iIndepFun

namespace TauCeti

/-- **Hermitian matrix Bernstein inequality** (Tropp 2012, Theorem 1.4 applied to `±Xₖ`). For
independent measurable random Hermitian `d × d` complex matrices `Xₖ` on `P` (where `iIndepFun X P`
carries the probability-measure condition on `P`) with entrywise mean zero and `‖Xₖ‖ ≤ L`
everywhere, and `v = ‖∑ₖ E[Xₖ²]‖`, the Euclidean operator norm of `∑ₖ Xₖ` is at least `t > 0` with
probability at most `2 * d * exp (-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem matrix_bernstein {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    {d m : ℕ} (X : Fin m → Ω → Matrix (Fin d) (Fin d) ℂ) (hmeas : ∀ k, Measurable (X k))
    (hindep : iIndepFun X P) (hherm : ∀ k ω, (X k ω).IsHermitian)
    (hmean : ∀ k i j, ∫ ω, X k ω i j ∂P = 0) (L : ℝ) (hbound : ∀ k ω, ‖X k ω‖ ≤ L)
    (t : ℝ) (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k, X k ω‖} ≤
      2 * d * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  simpa using hindep.measureReal_norm_sum_ge_le_of_isHermitian (s := Finset.univ)
    (fun k _ ↦ (hmeas k).aemeasurable) (fun k _ ↦ .of_forall (hherm k))
    (fun k _ ↦ hmean k) (fun k _ ↦ .of_forall (hbound k)) ht

end TauCeti
