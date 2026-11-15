/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import TauCeti.Analysis.Matrix.Realify
public import TauCeti.Probability.Independence.Decoupling
public import TauCeti.Probability.Moments.SubGaussian
import TauCeti.Analysis.Complex.Euclidean.Matrix
import TauCeti.Analysis.Matrix.DotProduct
import TauCeti.Probability.Independence.Integration
import TauCeti.Probability.Moments.SubExponential

/-!
# The Hanson–Wright inequality for sub-Gaussian quadratic forms

For independent `K`-sub-Gaussian real coordinates `(Xᵢ)_{i : ι}` on `(Ω, P)` and `A : Matrix ι ι ℝ`,
the **Hanson–Wright inequality** (Hanson–Wright 1971; Rudelson–Vershynin 2013; Vershynin 2018,
Theorem 6.2.1) bounds `P(|Xᵀ A X - P[Xᵀ A X]| > t)` by
`2 * exp (-c * min (t ^ 2 / (K ^ 2 * ∑ i, ∑ j, A i j ^ 2)) (t / (K * ‖A‖)))` for `t ≥ 0`.
We prove the real inequality with explicit constant `1 / 3200`, conditional versions for an
independent random matrix `A`, complex Hanson–Wright bounds via `Matrix.realify`, and Rademacher
sharpness `c ≤ 2 * Real.log 2`.
-/

public section
noncomputable section
open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace ProbabilityTheory.iIndepFun

private lemma offDiag_split_bounds {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]
    (A : Matrix ι ι 𝕜) {K : ℝ≥0} {θ : ℝ} (hθ : 32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1) :
    (∀ i, (A - Matrix.diagonal A.diag) i i = 0) ∧
      (∑ i, ‖A i i‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2) ∧
      (∑ i, ∑ j, ‖(A - Matrix.diagonal A.diag) i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2) ∧
      (K : ℝ) * |4 * (2 * θ)| * ‖A - Matrix.diagonal A.diag‖ ≤ 1 / 2 ∧
      ∀ a : ℝ, |a| ≤ ‖A‖ → (K : ℝ) * |(2 * θ) * a| ≤ 1 / 16 := by
  have hpyth : (∑ i, ‖A i i‖ ^ 2) + ∑ i, ∑ j, ‖(A - Matrix.diagonal A.diag) i j‖ ^ 2 =
      ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]; refine Finset.sum_congr rfl fun i _ ↦ ?_
    have hite : ∑ j : ι, (if i = j then ‖A i i‖ ^ 2 else 0) = ‖A i i‖ ^ 2 := by simp
    rw [← hite, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_; rcases eq_or_ne i j with rfl | hij <;> simp_all
  have h1 : 0 ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, ‖(A - Matrix.diagonal A.diag) i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  refine ⟨fun i ↦ by simp, by linarith, by linarith, ?_, fun a ha ↦ ?_⟩
  · have h42 : (4 : ℝ) * (2 * θ) = 8 * θ := by ring
    rw [h42, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    exact (mul_le_mul_of_nonneg_left A.l2_opNorm_sub_diagonal_diag_le (by positivity)).trans
      (by linarith)
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hmul : (K : ℝ) * (2 * |θ| * |a|) ≤ (K : ℝ) * (2 * |θ| * ‖A‖) := by gcongr
    exact hmul.trans (by linarith)

private def hwClipped {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℝ≥0) (t : ℝ)
    (M : Matrix ι ι ℝ) : ℝ :=
  min 1 (2 * exp (-(1 / 3200) *
    min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2)) (t / ((K : ℝ) * ‖M‖))))

private lemma measurable_hwClipped {ι : Type*} [Fintype ι] [DecidableEq ι] (K : ℝ≥0) (t : ℝ) :
    Measurable (hwClipped (ι := ι) K t) := by
  have : Measurable (fun M : Matrix ι ι ℝ ↦ ∑ i, ∑ j, M i j ^ 2) :=
    Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
      (Matrix.measurable_apply (i := i) (j := j)).pow_const 2
  have : Measurable (fun M : Matrix ι ι ℝ ↦ ‖M‖) := continuous_norm.measurable
  unfold hwClipped; fun_prop

section RealHansonWright
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {X : ι → Ω → ℝ}
  (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
include hindep hX

/-- Expectation of `Xᵀ A X` for independent `K`-sub-Gaussian real coordinates. -/
theorem integral_dotProduct_mulVec_eq_sum_diag (A : Matrix ι ι ℝ) :
    Integrable (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω)) P ∧
      ∫ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) ∂P = ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  simpa using TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
    (fun _ _ ↦ hindep.indepFun) (fun i ↦ (hX i).integrable)
    (fun i ↦ by simpa using ((hX i).memLp 2).integrable_sq) (fun i ↦ (hX i).integral_eq_zero) A

variable [DecidableEq ι]

/-- **Decoupled bilinear MGF bound (real case).** -/
theorem mgf_decoupled_dotProduct_mulVec_le (B : Matrix ι ι ℝ) {u : ℝ}
    (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) u ≤
      exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, B i j ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hu2 : (K : ℝ) * (K : ℝ) * u ^ 2 * ‖B‖ ^ 2 ≤ 1 / 2 := by
    rw [← sq_abs u]; nlinarith [pow_le_pow_left₀ (by positivity) hu 2]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_dotProduct_mulVec_prod_le
    (fun i ↦ (hX i).aemeasurable) (fun i ↦ (hX i).aemeasurable)
    (hindep.integral_exp_mul_dotProduct_le hX) (hindep.integral_exp_mul_dotProduct_le hX) B hu2
  exact ⟨hint, hle.trans_eq (by congr 1; ring)⟩

/-- **Sub-exponential MGF bound for centred sub-Gaussian quadratic forms.** -/
theorem mgf_dotProduct_mulVec_sub_integral_le (A : Matrix ι ι ℝ) {θ : ℝ}
    (hθ : 32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1) :
    Integrable (fun ω ↦ exp (θ * ((fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P))) P ∧
      mgf (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
          ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P) P θ ≤
        exp (800 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) * θ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let B : Matrix ι ι ℝ := A - Matrix.diagonal A.diag
  obtain ⟨hB_diag, hdiag_frob, hB_frob, hu_off, hentry⟩ := offDiag_split_bounds A hθ
  simp only [Real.norm_eq_abs, sq_abs] at hdiag_frob hB_frob
  obtain ⟨hdec_int, hdec_mgf⟩ := hindep.mgf_decoupled_dotProduct_mulVec_le hX B hu_off
  obtain ⟨hoff_int, hoff_mgf⟩ := hindep.mgf_offDiag_dotProduct_mulVec_le
    (fun i ↦ (hX i).integrable) (fun i ↦ (hX i).integral_eq_zero) hB_diag (t := 2 * θ) hdec_int
  have hoff_bound : mgf (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) P (2 * θ) ≤
      exp (64 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) * θ ^ 2) :=
    (hoff_mgf.trans hdec_mgf).trans (exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left hB_frob (by positivity : 0 ≤ 64 * (K : ℝ) ^ 2 * θ ^ 2)
      have h64 : (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, B i j ^ 2 =
          64 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, B i j ^ 2 := by ring
      linarith [h64]))
  let m (i : ι) : ℝ := ∫ ω', X i ω' ^ 2 ∂P
  let D : ι → Ω → ℝ := fun i ω ↦ A i i * (X i ω ^ 2 - m i)
  have hD_indep : iIndepFun D P :=
    hindep.comp (fun i x ↦ A i i * (x ^ 2 - m i)) fun _ ↦ by fun_prop
  have hD_meas (i : ι) : AEMeasurable (D i) P :=
    (((measurable_id.pow_const 2).comp_aemeasurable (hX i).aemeasurable).sub_const _).const_mul _
  have hD_term (i : ι) : Integrable (fun ω ↦ exp ((2 * θ) * D i ω)) P ∧
      mgf (D i) P (2 * θ) ≤ exp (1536 * (K : ℝ) ^ 2 * θ ^ 2 * A i i ^ 2) := by
    have hθi : (K : ℝ) * |(2 * θ) * A i i| ≤ 1 / 8 :=
      (hentry _ (by simpa using A.norm_apply_le_l2_opNorm i i)).trans (by norm_num)
    obtain ⟨hint_i, hmgf_i⟩ := (hX i).mgf_sq_sub_integral_le hθi
    exact ⟨hint_i.congr (.of_forall fun ω ↦ by dsimp [D, m]; ring_nf),
      (mgf_const_mul (A i i)).trans_le
        ((mul_comm (A i i) (2 * θ) ▸ hmgf_i).trans_eq (by congr 1; ring))⟩
  have hD_sum_int := hD_indep.integrable_exp_mul_sum_of_aemeasurable (s := Finset.univ)
    (fun i _ ↦ hD_meas i) fun i _ ↦ (hD_term i).1
  have hD_bound : mgf (fun ω ↦ ∑ i, D i ω) P (2 * θ) ≤
      exp (1536 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, A i j ^ 2) :=
    (hD_indep.mgf_sum_le_exp_sum (fun i _ ↦ hD_meas i) fun i _ ↦ (hD_term i).2).trans
      (exp_le_exp.2 (by
        rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hdiag_frob (by positivity)))
  have hsplit (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P =
        (∑ i, D i ω) + ((fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) := by
    have hA := A.re_star_dotProduct_mulVec_eq_sum_diag_add (fun i ↦ X i ω)
    simp only [RCLike.re_to_real, star_trivial, Real.norm_eq_abs, sq_abs] at hA
    rw [hA, (hindep.integral_dotProduct_mulVec_eq_sum_diag hX A).2]
    simp only [B, D, m, mul_sub, Finset.sum_sub_distrib]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  exact ⟨hint, hle.trans_eq (by congr 1; ring)⟩

/-- **One-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013) with constant `1 / 3200`. -/
theorem measureReal_dotProduct_mulVec_sub_integral_gt_le (A : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P} ≤
      exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hconst : min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 := by norm_num
  rw [← hconst]
  exact TauCeti.measureReal_gt_le_exp_min_of_mgf_le (by norm_num) (by norm_num) (by positivity)
    (by positivity) (fun _ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

/-- **Two-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013, Theorem 1.1) with constant
`1 / 3200`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_integral_gt_le (A : Matrix ι ι ℝ) {t : ℝ}
    (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hconst : min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 := by norm_num
  rw [← hconst]
  exact TauCeti.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le (by norm_num) (by norm_num)
    (by positivity) (by positivity)
    (fun _ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

open Classical in
private lemma measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral_if
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P)
    (hAX : IndepFun A (fun ω i ↦ X i ω) P) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω ↦ if A ω = 0 then 0 else hwClipped K t (A ω)) P ∧
      P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
          ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
        ∫ ω, (if A ω = 0 then 0 else hwClipped K t (A ω)) ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hX_vec : AEMeasurable (fun ω i ↦ X i ω) P :=
    AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable
  let μA : Measure (Matrix ι ι ℝ) := P.map A; let μX : Measure (ι → ℝ) := P.map (fun ω i ↦ X i ω)
  have : IsProbabilityMeasure μA := by dsimp [μA]; infer_instance
  have : IsProbabilityMeasure μX := by dsimp [μX]; infer_instance
  let E : Set (Matrix ι ι ℝ × (ι → ℝ)) :=
    {p | t < |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|}
  have hE_meas : MeasurableSet E := by
    have hcont : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) ↦
        |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|) := by
      simp only [dotProduct, Matrix.mulVec]; fun_prop
    exact (isOpen_lt continuous_const hcont).measurableSet
  let ψ : Matrix ι ι ℝ → ℝ := fun M ↦ if M = 0 then 0 else hwClipped K t M
  have h0_meas : MeasurableSet {M : Matrix ι ι ℝ | M = 0} := by
    simpa only [norm_le_zero_iff] using measurableSet_le
      (continuous_norm : Continuous fun M : Matrix ι ι ℝ ↦ ‖M‖).measurable
      (measurable_const (a := (0 : ℝ)))
  have hψ_meas : Measurable ψ := Measurable.ite h0_meas measurable_const (measurable_hwClipped K t)
  have hψ_int : Integrable ψ μA :=
    Integrable.of_mem_Icc 0 1 hψ_meas.aemeasurable (.of_forall fun M ↦ by
      dsimp [ψ, hwClipped]; split_ifs <;>
        [exact ⟨le_rfl, zero_le_one⟩; exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩])
  have hslice_le (M : Matrix ι ι ℝ) : μX.real (Prod.mk M ⁻¹' E) ≤ ψ M := by
    by_cases hM0 : M = 0
    · subst hM0
      have hpre : Prod.mk (0 : Matrix ι ι ℝ) ⁻¹' E = ∅ := by ext; simp [E, not_lt.2 ht]
      simp [ψ, hpre]
    · simp only [ψ, hM0, ↓reduceIte, hwClipped]
      rw [map_measureReal_apply_of_aemeasurable hX_vec (hE_meas.preimage measurable_prodMk_left)]
      refine le_min ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ) ?_
      simpa only [E, Set.preimage_ofPred_eq,
        (hindep.integral_dotProduct_mulVec_eq_sum_diag hX M).2] using
        hindep.measureReal_abs_dotProduct_mulVec_sub_integral_gt_le hX M ht
  have hind_int : Integrable (E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ)) (μA.prod μX) :=
    (integrable_const (1 : ℝ)).indicator hE_meas
  have hslice_eq (M : Matrix ι ι ℝ) :
      ∫ x, E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x) ∂μX =
        μX.real (Prod.mk M ⁻¹' E) := by
    have hind_pre : (fun x ↦ E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x)) =
        (Prod.mk M ⁻¹' E).indicator 1 := by ext x; by_cases hx : (M, x) ∈ E <;> simp [hx]
    rw [hind_pre, integral_indicator_one (hE_meas.preimage measurable_prodMk_left)]
  refine ⟨(integrable_map_measure hψ_meas.aestronglyMeasurable hA_meas).mp hψ_int, ?_⟩
  have hprob_prod : P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = (μA.prod μX).real E := by
    rw [← hAX.map_prod_eq_prod_map_map hA_meas hX_vec,
      map_measureReal_apply_of_aemeasurable (hA_meas.prodMk hX_vec) hE_meas]; simp [E]
  rw [hprob_prod, ← integral_indicator_one hE_meas, integral_prod _ hind_int]
  exact ((integral_congr_ae (.of_forall hslice_eq)).trans_le
    (integral_mono_ae (hind_int.integral_prod_left.congr (.of_forall hslice_eq))
      hψ_int (.of_forall hslice_le))).trans_eq (integral_map hA_meas hψ_meas.aestronglyMeasurable)

/-- **Integrated conditional Hanson–Wright inequality** for an independent random matrix `A`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P) (hAX : IndepFun A (fun ω i ↦ X i ω) P)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
      ∫ ω, min 1 (2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A ω i j ^ 2))
        (t / ((K : ℝ) * ‖A ω‖)))) ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  obtain ⟨hψ_int, hle⟩ :=
    hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral_if hX hA_meas hAX ht
  refine hle.trans (integral_mono hψ_int ?_ fun _ ↦ ?_)
  · exact Integrable.of_mem_Icc 0 1 ((measurable_hwClipped K t).comp_aemeasurable hA_meas)
      (.of_forall fun _ ↦ ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩)
  · dsimp [hwClipped]; split_ifs <;> [exact le_min zero_le_one (by positivity); exact le_rfl]

/-- **Conditional Hanson–Wright inequality under a.s. norm bounds.** -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P) (hAX : IndepFun A (fun ω i ↦ X i ω) P)
    {F op : ℝ} (hA_frob : ∀ᵐ ω ∂P, ∑ i, ∑ j, A ω i j ^ 2 ≤ F) (hA_op : ∀ᵐ ω ∂P, ‖A ω‖ ≤ op)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rcases eq_or_ne K 0 with rfl | hK_ne
  · simp only [NNReal.coe_zero, sq, zero_mul, div_zero, min_self, mul_zero, exp_zero, mul_one]
    exact (measureReal_mono (Set.subset_univ _)).trans (by rw [probReal_univ]; norm_num)
  have hK_pos : 0 < (K : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK_ne)
  obtain ⟨hψ_int, hle⟩ :=
    hindep.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral_if hX hA_meas hAX ht
  let Bnd := 2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op)))
  refine hle.trans ((integral_mono_ae hψ_int (integrable_const Bnd) ?_).trans_eq
    (by simp [Bnd, probReal_univ]))
  filter_upwards [hA_frob, hA_op] with ω hMf hMop
  dsimp [hwClipped]; split_ifs with hM0
  · positivity
  · obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j, A ω i j ≠ 0 := by by_contra! h; exact hM0 (Matrix.ext h)
    have hMf_pos : 0 < ∑ i, ∑ j, A ω i j ^ 2 := lt_of_lt_of_le (sq_pos_of_ne_zero hij₀)
      ((Finset.single_le_sum (fun j _ ↦ sq_nonneg (A ω i₀ j)) (Finset.mem_univ j₀)).trans
        (Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
          (Finset.mem_univ i₀)))
    have : 0 < ‖A ω‖ := norm_pos_iff.2 hM0
    refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) zero_le_two)
    have hmin := min_le_min
      (div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
        (mul_le_mul_of_nonneg_left hMf (sq_nonneg (K : ℝ))))
      (div_le_div_of_nonneg_left ht (by positivity) (mul_le_mul_of_nonneg_left hMop hK_pos.le))
    linarith

end RealHansonWright

section ComplexHansonWright
variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω} {Z : ι → Ω → ℂ}
  (hindep : iIndepFun Z P)
include hindep

section SubGaussian
variable {K : ℝ≥0}
  (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
include hZ

/-- Expectation of `star Z ⬝ᵥ A *ᵥ Z` for independent directionally sub-Gaussian complex `Z`. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag (A : Matrix ι ι ℂ) :
    Integrable (fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)) P ∧
      ∫ ω, star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖Z i ω‖ ^ 2] : ℝ) : ℂ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact TauCeti.integral_star_dotProduct_mulVec_eq_sum_diag_of_pairwise_indepFun
    (fun _ _ ↦ hindep.indepFun) (fun i ↦ integrable_of_hasSubgaussianMGF_re_star_mul (hZ i))
    (fun i ↦ ((((hasSubgaussianMGF_re_of_star_mul (hZ i)).memLp 2).integrable_sq).add
      (((hasSubgaussianMGF_im_of_star_mul (hZ i)).memLp 2).integrable_sq)).congr
      (.of_forall fun _ ↦ by
        dsimp only [Pi.add_apply]; rw [Complex.sq_norm, Complex.normSq_apply]; ring))
    (fun i ↦ integral_eq_zero_of_hasSubgaussianMGF_re_star_mul (hZ i)) A

variable [DecidableEq ι]

/-- **Decoupled sesquilinear MGF bound (complex case).** -/
theorem mgf_decoupled_re_star_dotProduct_mulVec_le (B : Matrix ι ι ℂ) {u : ℝ}
    (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re)) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re) (P.prod P) u ≤
      exp (2 * (K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let V : Ω → ι ⊕ ι → ℝ := fun ω ↦ Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im)
  have hZ_meas (i : ι) := (integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)).aemeasurable
  have hV_meas (q : ι ⊕ ι) : AEMeasurable (fun ω ↦ V ω q) P := by
    rcases q with i | i <;>
      [exact Complex.continuous_re.measurable.comp_aemeasurable (hZ_meas i);
       exact Complex.continuous_im.measurable.comp_aemeasurable (hZ_meas i)]
  have hrealify (p : Ω × Ω) :
      (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re =
        V p.1 ⬝ᵥ B.realify *ᵥ V p.2 := by
    have hV (ω : Ω) : (TauCeti.complexToRealEuclidean ι (fun i ↦ Z i ω)).ofLp = V ω :=
      funext (TauCeti.complexToRealEuclidean_apply ι _)
    rw [← TauCeti.inner_complexToRealEuclidean ι, TauCeti.complexToRealEuclidean_mulVec,
      EuclideanSpace.inner_eq_star_dotProduct, star_trivial, Matrix.toLpLin_apply,
      WithLp.ofLp_toLp, hV p.1, hV p.2, dotProduct_comm]
  have hu2 : (K : ℝ) * (K : ℝ) * u ^ 2 * ‖B.realify‖ ^ 2 ≤ 1 / 2 := by
    rw [Matrix.l2_opNorm_realify, ← sq_abs u]
    nlinarith [pow_le_pow_left₀ (by positivity) hu 2]
  simp_rw [hrealify]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_dotProduct_mulVec_prod_le hV_meas hV_meas
    (hindep.integral_exp_mul_sum_elim_re_im_dotProduct_le hZ)
    (hindep.integral_exp_mul_sum_elim_re_im_dotProduct_le hZ) B.realify hu2
  exact ⟨hint, hle.trans_eq (by congr 1; rw [Matrix.sum_sq_realify]; ring)⟩

/-- **Centred MGF bound for the real part of a complex sub-Gaussian sesquilinear form.** -/
theorem mgf_re_star_dotProduct_mulVec_sub_integral_le (A : Matrix ι ι ℂ) {θ : ℝ}
    (hθ : 32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1) :
    Integrable (fun ω ↦ exp (θ * ((star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
        ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P))) P ∧
      mgf (fun ω ↦ (star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
          ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P) P θ ≤
        exp (3136 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let B : Matrix ι ι ℂ := A - Matrix.diagonal A.diag
  obtain ⟨hB_diag, hdiag_frob, hB_frob, hu_off, hentry⟩ := offDiag_split_bounds A hθ
  obtain ⟨hdec_int, hdec_mgf⟩ := hindep.mgf_decoupled_re_star_dotProduct_mulVec_le hZ B hu_off
  have hZ_int (i : ι) : Integrable (Z i) P := integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)
  obtain ⟨hoff_int, hoff_mgf⟩ := hindep.mgf_offDiag_re_star_dotProduct_mulVec_le hZ_int
    (fun i ↦ integral_eq_zero_of_hasSubgaussianMGF_re_star_mul (hZ i)) hB_diag (t := 2 * θ) hdec_int
  simp only [RCLike.re_eq_complex_re] at hoff_int hoff_mgf
  have hoff_bound : mgf (fun ω ↦ (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re) P (2 * θ) ≤
      exp (128 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2) :=
    (hoff_mgf.trans hdec_mgf).trans (exp_le_exp.2 (by
      have := mul_le_mul_of_nonneg_left hB_frob (by positivity : 0 ≤ 128 * (K : ℝ) ^ 2 * θ ^ 2)
      have h128 : 2 * (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 =
          128 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by ring
      linarith [h128]))
  let m (i : ι) : ℝ := ∫ ω', ‖Z i ω'‖ ^ 2 ∂P
  let D : ι → Ω → ℝ := fun i ω ↦ (A i i).re * (‖Z i ω‖ ^ 2 - m i)
  have hD_indep : iIndepFun D P :=
    hindep.comp (fun i z ↦ (A i i).re * (‖z‖ ^ 2 - m i)) fun _ ↦ by fun_prop
  have hD_meas (i : ι) : AEMeasurable (D i) P :=
    ((((continuous_norm.pow 2).measurable.comp_aemeasurable
      (hZ_int i).aemeasurable)).sub_const _).const_mul _
  have hD_term (i : ι) : Integrable (fun ω ↦ exp ((2 * θ) * D i ω)) P ∧
      mgf (D i) P (2 * θ) ≤ exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * ‖A i i‖ ^ 2) := by
    have hθi := hentry _ ((Complex.abs_re_le_norm _).trans (A.norm_apply_le_l2_opNorm i i))
    obtain ⟨hint_i, hmgf_i⟩ :=
      mgf_norm_sq_sub_integral_le_of_hasSubgaussianMGF_re_star_mul (hZ i) hθi
    have hre_sq : (A i i).re ^ 2 ≤ ‖A i i‖ ^ 2 :=
      sq_le_sq.2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact Complex.abs_re_le_norm _)
    exact ⟨hint_i.congr (.of_forall fun ω ↦ by dsimp [D, m]; ring_nf),
      (mgf_const_mul (A i i).re).trans_le (((mul_comm (A i i).re (2 * θ) ▸ hmgf_i).trans_eq
        (by congr 1; ring)).trans
        (exp_le_exp.2 (mul_le_mul_of_nonneg_left hre_sq (by positivity))))⟩
  have hD_sum_int := hD_indep.integrable_exp_mul_sum_of_aemeasurable (s := Finset.univ)
    (fun i _ ↦ hD_meas i) fun i _ ↦ (hD_term i).1
  have hD_bound : mgf (fun ω ↦ ∑ i, D i ω) P (2 * θ) ≤
      exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) :=
    (hD_indep.mgf_sum_le_exp_sum (fun i _ ↦ hD_meas i) fun i _ ↦ (hD_term i).2).trans
      (exp_le_exp.2 (by
        rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hdiag_frob (by positivity)))
  obtain ⟨hquad_int, hquad_mean⟩ := hindep.integral_star_dotProduct_mulVec_eq_sum_diag hZ A
  have hre_mean : ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
      ∑ i, (A i i).re * m i :=
    (Complex.reCLM.integral_comp_comm hquad_int).trans <| by
      rw [hquad_mean, map_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ by simp [m, Complex.mul_re]
  have hsplit (ω : Ω) : (star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
      ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
        (∑ i, D i ω) + (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re := by
    have hA := A.re_star_dotProduct_mulVec_eq_sum_diag_add (fun i ↦ Z i ω)
    simp only [RCLike.re_eq_complex_re] at hA
    rw [hA, hre_mean]; simp only [B, D, mul_sub, Finset.sum_sub_distrib]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := TauCeti.mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  exact ⟨hint, hle.trans_eq (by congr 1; ring)⟩

/-- **Complex Hanson–Wright inequality (real part)** with constant `1 / 12544`. -/
theorem measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
        ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P|} ≤
      2 * exp (-(1 / 12544) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hconst : min (1 / (4 * (3136 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 12544 := by norm_num
  rw [← hconst]
  exact TauCeti.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le (by norm_num) (by norm_num)
    (by positivity) (by positivity)
    (fun _ hθ ↦ hindep.mgf_re_star_dotProduct_mulVec_sub_integral_le hZ A hθ) ht

/-- **Complex Hanson–Wright inequality (full complex norm)** with constant `1 / 150528`. -/
theorem measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < ‖star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) -
        ∫ ω', star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω') ∂P‖} ≤
      2 * exp (-(1 / 150528) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  set Q : Ω → ℂ := fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)
  have hQ_int : Integrable Q P := (hindep.integral_star_dotProduct_mulVec_eq_sum_diag hZ A).1
  let AI : Matrix ι ι ℂ := (-Complex.I) • A
  have hAI_re (ω : Ω) : (star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re = (Q ω).im := by
    have hAI_eq : star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω) = (-Complex.I) * Q ω := by
      simp only [AI, Q, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
    rw [hAI_eq]; simp [Complex.mul_re]
  have hsub : {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ⊆
      {ω | t / 2 < |(Q ω).re - ∫ ω', (Q ω').re ∂P|} ∪
        {ω | t / 2 < |(star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re -
          ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω')).re ∂P|} := fun ω hω ↦ by
    have hre_q : (∫ ω', Q ω' ∂P).re = ∫ ω', (Q ω').re ∂P :=
      (Complex.reCLM.integral_comp_comm hQ_int).symm
    have him_q : (∫ ω', Q ω' ∂P).im = ∫ ω', (Q ω').im ∂P :=
      (Complex.imCLM.integral_comp_comm hQ_int).symm
    simp only [Set.mem_union, Set.mem_ofPred_eq, hAI_re]; by_contra! h
    have hre : ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_re, hre_q, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.1 2
    have him : ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_im, him_q, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.2 2
    have hns : ‖Q ω - ∫ ω', Q ω' ∂P‖ ^ 2 =
        ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 + ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have hω_lt : t < ‖Q ω - ∫ ω', Q ω' ∂P‖ := hω
    nlinarith [pow_lt_pow_left₀ hω_lt ht (by norm_num : 2 ≠ 0)]
  set F := (K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2; set op := (K : ℝ) * ‖A‖
  set m : ℝ := min (t ^ 2 / F) (t / op)
  have hsq_div : (t / 2) ^ 2 / F = (t ^ 2 / F) / 4 := by ring
  have hlin_div : (t / 2) / op = (t / op) / 2 := by ring
  have hm_half : m / 4 ≤ min ((t / 2) ^ 2 / F) ((t / 2) / op) :=
    le_min (by linarith [min_le_left (t ^ 2 / F) (t / op), hsq_div])
      (by linarith [min_le_right (t ^ 2 / F) (t / op),
        div_nonneg ht (mul_nonneg K.coe_nonneg (norm_nonneg A)), hlin_div])
  have ht2 : 0 ≤ t / 2 := by positivity
  have h1 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ A ht2
  have h2 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ AI ht2
  have hAI_op : ‖AI‖ = ‖A‖ := by rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hAI_frob : ∑ i, ∑ j, ‖AI i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by simp [AI]
  rw [hAI_op, hAI_frob] at h2
  have hexp_le : exp (-(1 / 12544) * min ((t / 2) ^ 2 / F) ((t / 2) / op)) ≤
      exp (-(1 / 50176) * m) := exp_le_exp.2 (by linarith)
  have h4 : P.real {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ≤ 4 * exp (-(1 / 50176) * m) :=
    ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
      (by dsimp [Q, F, op] at *; linarith)
  set u : ℝ := exp (-(1 / 150528) * m)
  by_cases hu_half : 1 / 2 ≤ u
  · exact ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ).trans (by linarith)
  · have hu_cube : 4 * exp (-(1 / 50176) * m) = 4 * u ^ 2 * u := by
      dsimp [u]; rw [mul_assoc, ← pow_succ, ← exp_nat_mul]; congr 2; push_cast; ring
    have hu_nonneg : 0 ≤ u := (exp_pos _).le
    exact h4.trans (hu_cube.trans_le
      (mul_le_mul_of_nonneg_right (by nlinarith) (exp_pos _).le))
end SubGaussian

/-- **Complex Hanson–Wright inequality for bounded mean-zero coordinates.** -/
theorem measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le_of_norm_le [DecidableEq ι]
    (hZ_meas : ∀ i, AEMeasurable (Z i) P) {b : ℝ≥0} (hZ_norm : ∀ i, ∀ᵐ ω ∂P, ‖Z i ω‖ ≤ b)
    (hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0) (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < ‖star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) -
        ∫ ω', star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω') ∂P‖} ≤
      2 * exp (-(1 / 150528) * min (t ^ 2 / (((b ^ 2 : ℝ≥0) : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / (((b ^ 2 : ℝ≥0) : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact hindep.measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le
    (fun i u ↦ hasSubgaussianMGF_re_star_mul_of_norm_le (hZ_meas i) (hZ_norm i) (hZ_mean i) u) A ht
end ComplexHansonWright
end ProbabilityTheory.iIndepFun

namespace TauCeti

/-- **Hanson–Wright inequality** (Rudelson–Vershynin 2013, Theorem 1.1). -/
theorem hanson_wright :
    ∃ c : ℝ, 0 < c ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
        (X : Fin n → Ω → ℝ) (K : ℝ≥0), iIndepFun X P → (∀ i, HasSubgaussianMGF (X i) K P) →
        ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 ≤ t →
          P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
              ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
            2 * Real.exp (-c * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
              (t / ((K : ℝ) * ‖A‖))) :=
  ⟨1 / 3200, by norm_num, fun {_} _ _ _ {_} _ _ hindep hX A _ ht ↦
    hindep.measureReal_abs_dotProduct_mulVec_sub_integral_gt_le hX A ht⟩

/-- **Rademacher sharpness of the Hanson–Wright exponent** (`c ≤ 2 * Real.log 2`). -/
theorem le_two_mul_log_two_of_hanson_wright {c : ℝ}
    (hc : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
      (X : Fin n → Ω → ℝ) (K : ℝ≥0), iIndepFun X P → (∀ i, HasSubgaussianMGF (X i) K P) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 ≤ t →
        P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
            ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
          2 * Real.exp (-c * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
            (t / ((K : ℝ) * ‖A‖)))) :
    c ≤ 2 * Real.log 2 := by
  let B := ULift Bool; let _ := @hc (Fin 2 → B)
  let μ₀ : Measure B := (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (.up true) + Measure.dirac (.up false))
  have : IsProbabilityMeasure μ₀ := ⟨by
    simp only [μ₀, smul_apply, FunLike.coe_add, Pi.add_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
      one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)⟩
  let rad : B → ℝ := fun b ↦ if b.down then 1 else -1
  have hrad_meas : Measurable rad := measurable_of_finite rad
  have hrad_mean : ∫ b, rad b ∂μ₀ = 0 := by
    rw [integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_dirac, integral_dirac]; simp [rad]
  have hrad_mem : ∀ b : B, rad b ∈ Set.Icc (-1) 1 := fun ⟨b⟩ ↦ by cases b <;> simp [rad]
  have hrad_subG : HasSubgaussianMGF rad 1 μ₀ :=
    (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hrad_meas.aemeasurable
      (.of_forall hrad_mem) hrad_mean).mono (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  let P : Measure (Fin 2 → B) := Measure.pi fun _ : Fin 2 ↦ μ₀
  let X : Fin 2 → (Fin 2 → B) → ℝ := fun i ↦ rad ∘ Function.eval i
  have hindep : iIndepFun X P := by
    simpa only [X, Function.comp_def, Function.eval] using
      iIndepFun_pi (μ := fun _ : Fin 2 ↦ μ₀) fun _ ↦ hrad_meas.aemeasurable
  have hX_subG (i : Fin 2) : HasSubgaussianMGF (X i) 1 P :=
    HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable
      (by rwa [(measurePreserving_eval (fun _ : Fin 2 ↦ μ₀) i).map_eq])
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![0, 1], ![1, 0]]
  have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P = 0 := by
    rw [(hindep.integral_dotProduct_mulVec_eq_sum_diag hX_subG A).2, Fin.sum_univ_two]; simp [A]
  have hevent : {ω | (1 : ℝ) < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} = Set.univ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; rw [hmean, sub_zero]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, A, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, X, Function.comp_apply,
      Function.eval, rad]
    cases h0 : (ω 0).down <;> cases h1 : (ω 1).down <;> norm_num [h0, h1]
  have hop : ‖A‖ = 1 := le_antisymm (by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (𝕜 := ℝ) A).opNorm_le_bound zero_le_one fun v ↦ ?_
    rw [one_mul]; refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two, Matrix.mulVec, dotProduct, A, add_comm])
    (by simpa [A] using A.norm_apply_le_l2_opNorm 0 1)
  have hfrob : ∑ i : Fin 2, ∑ j : Fin 2, A i j ^ 2 = 2 := by simp [Fin.sum_univ_two, A]; norm_num
  have hmin_half : min ((1 : ℝ) / 2) 1 = 1 / 2 := by norm_num
  have hbound := hc P X 1 hindep hX_subG A 1 zero_le_one
  rw [hevent, probReal_univ, hfrob, hop] at hbound
  simp only [NNReal.coe_one, one_pow, one_mul, div_one, hmin_half] at hbound
  have hlog := Real.log_le_log (by positivity) (by linarith : (2 : ℝ)⁻¹ ≤ Real.exp (-c * (1 / 2)))
  rw [Real.log_inv, Real.log_exp] at hlog; linarith

end TauCeti
