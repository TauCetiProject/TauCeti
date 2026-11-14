/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Moments.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Sub-exponential random variables

A real random variable is sub-exponential with parameter `K` when its centered exponential
moments exist and are bounded by `exp (K ^ 2 * t ^ 2)` for `|t| ≤ 1 / K`. Independent centered
variables with a common parameter satisfy a two-sided Bernstein tail bound.

We also provide centered sub-exponential MGF bounds from an exponential moment `∫ exp (Y / B) ≤ 2`
(`TauCeti.mgf_sub_integral_le_of_nonneg_exp_le_two`) and one- and two-sided sub-exponential Chernoff
tail bounds (`TauCeti.measureReal_gt_le_exp_min_of_mgf_le`,
`TauCeti.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le`) optimizing a quadratic log-MGF bound on a
restricted interval.

## References

* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), §2.7.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Sub-exponential MGF bound for a centered nonnegative variable** with `∫ exp (Y / B) ≤ 2`. -/
theorem mgf_sub_integral_le_of_nonneg_exp_le_two [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY_meas : AEMeasurable Y μ) (hY_nonneg : 0 ≤ᵐ[μ] Y) {B : ℝ} (hB : 0 < B)
    (hY_int_exp : Integrable (fun ω ↦ exp (Y ω / B)) μ) (hY_exp : ∫ ω, exp (Y ω / B) ∂μ ≤ 2)
    {θ : ℝ} (hθ : B * |θ| ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (θ * (Y ω - μ[Y]))) μ ∧
      mgf (fun ω ↦ Y ω - μ[Y]) μ θ ≤ exp (24 * B ^ 2 * θ ^ 2) := by
  have hY_int : Integrable Y μ := (hY_int_exp.const_mul B).mono' hY_meas.aestronglyMeasurable <| by
    filter_upwards [hY_nonneg] with ω hω
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith [add_one_le_exp (Y ω / B)] : Y ω / B ≤ exp (Y ω / B)) hB.le
    rw [Real.norm_of_nonneg hω]; rwa [mul_div_cancel₀ _ hB.ne'] at h2
  let m : ℝ := μ[Y]; have hm_nonneg : 0 ≤ m := integral_nonneg_of_ae hY_nonneg
  have hm_le : m ≤ B := by
    have hf : Integrable (fun ω ↦ 1 + Y ω / B) μ := (integrable_const 1).add (hY_int.div_const B)
    have h1 := integral_mono hf hY_int_exp fun ω ↦ by linarith [add_one_le_exp (Y ω / B)]
    rw [integral_add (integrable_const 1) (hY_int.div_const B), integral_const, probReal_univ,
      one_smul, integral_div] at h1
    exact (div_le_one hB).mp (by linarith)
  let Z : Ω → ℝ := fun ω ↦ Y ω - m; have hZ_int : Integrable Z μ := hY_int.sub (integrable_const m)
  have hZ_mean : ∫ ω, Z ω ∂μ = 0 := by
    rw [integral_sub hY_int (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hexp_half_le : exp (1 / 2 : ℝ) ≤ 3 := by
    have h := mul_le_mul_of_nonneg_right
      (exp_neg (1 / 2 : ℝ) ▸ add_one_le_exp (-(1 / 2 : ℝ))) (exp_pos (1 / 2 : ℝ)).le
    rw [inv_mul_cancel₀ (exp_pos _).ne'] at h; linarith
  have hpt : ∀ᵐ ω ∂μ, exp (θ * Z ω) ≤ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B) := by
    filter_upwards [hY_nonneg] with ω hω
    let u : ℝ := Y ω / B; have hu0 : 0 ≤ u := div_nonneg hω hB.le
    have hY_eq : Y ω = B * u := (mul_div_cancel₀ _ hB.ne').symm
    have hZ_abs : |Z ω| ≤ B * (u + 1) := abs_le.2 ⟨by dsimp [Z]; nlinarith, by dsimp [Z]; nlinarith⟩
    have hθZ : |θ * Z ω| ≤ u / 2 + 1 / 2 := (abs_mul θ (Z ω)) ▸
      (mul_le_mul_of_nonneg_left hZ_abs (abs_nonneg θ)).trans
        (by linarith [mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ u + 1)])
    have hu_quad : (u + 1) ^ 2 ≤ 8 * exp (u / 2) := by
      have hpoly : (u + 1) ^ 2 ≤ 8 * (1 + u / 2 + (u / 2) ^ 2 / 2) := by nlinarith
      linarith [hpoly, Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ u / 2)]
    have hu_exp : (u + 1) ^ 2 * exp (u / 2 + 1 / 2) ≤ 24 * exp u := by
      have hmul := mul_le_mul hu_quad (mul_le_mul_of_nonneg_left hexp_half_le (exp_pos (u / 2)).le)
        (by positivity) (by positivity)
      have hexp_sq : exp (u / 2) * exp (u / 2) = exp u := by rw [← exp_add]; ring_nf
      rw [exp_add]; linarith [hexp_sq]
    have h1 : (θ * Z ω) ^ 2 / 2 * exp |θ * Z ω| ≤
        (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) := by
      have hZ_sq : (θ * Z ω) ^ 2 ≤ B ^ 2 * θ ^ 2 * (u + 1) ^ 2 := by
        have habs_sq : (θ * Z ω) ^ 2 = θ ^ 2 * |Z ω| ^ 2 := by rw [sq_abs]; ring
        rw [habs_sq]; nlinarith [pow_le_pow_left₀ (abs_nonneg _) hZ_abs 2, sq_nonneg θ]
      have hreassoc : (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) =
          (B ^ 2 * θ ^ 2 * (u + 1) ^ 2 / 2) * exp (u / 2 + 1 / 2) := by ring
      rw [hreassoc]
      exact mul_le_mul (by linarith) (exp_le_exp.2 hθZ) (exp_pos _).le (by positivity)
    exact (Real.exp_le_one_add_add_sq_div_two_mul_exp_abs (θ * Z ω)).trans
      (by linarith [mul_le_mul_of_nonneg_left hu_exp (by positivity : 0 ≤ B ^ 2 * θ ^ 2 / 2)])
  have hf1 : Integrable (fun ω ↦ 1 + θ * Z ω) μ := (integrable_const 1).add (hZ_int.const_mul θ)
  have hdom : Integrable (fun ω ↦ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B)) μ :=
    hf1.add (hY_int_exp.const_mul (12 * B ^ 2 * θ ^ 2))
  have hint : Integrable (fun ω ↦ exp (θ * Z ω)) μ :=
    hdom.mono' (Real.measurable_exp.comp_aemeasurable
      ((hY_meas.sub_const m).const_mul θ)).aestronglyMeasurable
      (hpt.mono fun _ hω ↦ by rwa [Real.norm_of_nonneg (exp_pos _).le])
  refine ⟨hint, ?_⟩; rw [mgf]; refine (integral_mono_ae hint hdom hpt).trans ?_
  rw [integral_add hf1 (hY_int_exp.const_mul _),
    integral_add (integrable_const 1) (hZ_int.const_mul θ), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_const_mul, hZ_mean, mul_zero, add_zero]
  have hlin : 1 + 12 * B ^ 2 * θ ^ 2 * ∫ ω, exp (Y ω / B) ∂μ ≤ 1 + 24 * B ^ 2 * θ ^ 2 := by
    nlinarith [sq_nonneg (B * θ)]
  exact hlin.trans (by linarith [add_one_le_exp (24 * B ^ 2 * θ ^ 2)])

/-- **One-sided sub-exponential Chernoff bound.** -/
theorem measureReal_gt_le_exp_min_of_mgf_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {C₁ C₂ F op : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < Y ω} ≤
      exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  let c : ℝ := min (1 / (4 * C₁)) (1 / (2 * C₂))
  rcases hF.eq_or_lt with rfl | hF_pos
  · have hmin0 : min (t ^ 2 / (0 : ℝ)) (t / op) = 0 := by simp [div_nonneg ht hop]
    rw [hmin0, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rcases hop.eq_or_lt with rfl | hop_pos
  · have hmin0 : min (t ^ 2 / F) (t / (0 : ℝ)) = 0 := by simp [div_nonneg (sq_nonneg t) hF_pos.le]
    rw [hmin0, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  let θ : ℝ := min (t / (2 * C₁ * F)) (1 / (C₂ * op))
  have hθ0 : 0 ≤ θ := le_min (by positivity) (by positivity)
  have hpos : 0 < C₂ * op := mul_pos hC₂ hop_pos
  obtain ⟨hint, hle⟩ := hmgf θ (by
    rw [abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le).trans_eq
      (mul_one_div_cancel hpos.ne'))
  have hCF : 0 < 2 * C₁ * F := by positivity
  have hquad : C₁ * F * θ ^ 2 ≤ θ * t / 2 := by
    nlinarith [(mul_le_mul_of_nonneg_left (min_le_left _ _ : θ ≤ _) hCF.le).trans_eq
      (mul_div_cancel₀ t hCF.ne')]
  have hrate : c * min (t ^ 2 / F) (t / op) ≤ θ * t / 2 := by
    rcases le_total (t / (2 * C₁ * F)) (1 / (C₂ * op)) with hcase | hcase
    · have hθ_eq : θ = t / (2 * C₁ * F) := min_eq_left hcase
      rw [hθ_eq]
      exact (mul_le_mul (min_le_left _ _) (min_le_left _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp; ring)
    · have hθ_eq : θ = 1 / (C₂ * op) := min_eq_right hcase
      rw [hθ_eq]
      exact (mul_le_mul (min_le_right _ _) (min_le_right _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp)
  have hsub : {ω | t < Y ω} ⊆ {ω | t ≤ Y ω} := fun _ (hω : t < _) ↦ hω.le
  exact ((measureReal_mono hsub).trans (measure_ge_le_exp_mul_mgf t hθ0 hint)).trans
    ((mul_le_mul_of_nonneg_left hle (exp_pos _).le).trans
      ((exp_add _ _).symm.trans_le (exp_le_exp.2 (by linarith))))

/-- **Two-sided sub-exponential Chernoff bound.** -/
theorem measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {C₁ C₂ F op : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Y ω|} ≤
      2 * exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  have hmgf_neg (θ : ℝ) (hθ : C₂ * op * |θ| ≤ 1) :
      Integrable (fun ω ↦ exp (θ * (-Y) ω)) P ∧ mgf (-Y) P θ ≤ exp (C₁ * F * θ ^ 2) := by
    obtain ⟨hint, hle⟩ := hmgf (-θ) (by simpa only [abs_neg] using hθ)
    exact ⟨hint.congr (.of_forall fun _ ↦ by simp [Pi.neg_apply, mul_neg, neg_mul]),
      by rw [mgf_neg]; exact hle.trans_eq (by ring_nf)⟩
  have hsub : {ω | t < |Y ω|} ⊆ {ω | t < Y ω} ∪ {ω | t < (-Y) ω} := fun _ hω ↦ by
    simpa only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, lt_abs] using hω
  have hpos := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf ht
  have hneg := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf_neg ht
  exact (measureReal_mono hsub).trans <| (measureReal_union_le _ _).trans (by linarith)

end TauCeti

namespace TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A real random variable is sub-exponential with parameter `K` if `K > 0`, it is integrable,
and its centered exponential moments are integrable and bounded by
`exp (K ^ 2 * t ^ 2)` for every `|t| ≤ 1 / K`. -/
structure HasSubexponentialMGF (X : Ω → ℝ) (K : ℝ) (μ : Measure Ω)
    [IsProbabilityMeasure μ] : Prop where
  parameter_pos : 0 < K
  integrable : Integrable X μ
  integrable_exp_mul_centered : ∀ t : ℝ, |t| ≤ K⁻¹ →
    Integrable (fun ω => exp (t * (X ω - μ[X]))) μ
  centered_mgf_le : ∀ t : ℝ, |t| ≤ K⁻¹ →
    mgf (fun ω => X ω - μ[X]) μ t ≤ exp (K ^ 2 * t ^ 2)

namespace HasSubexponentialMGF

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {K t : ℝ}

/-- Centering a sub-exponential random variable preserves its parameter. -/
theorem center (h : HasSubexponentialMGF X K μ) :
    HasSubexponentialMGF (fun ω => X ω - μ[X]) K μ := by
  have hmean : μ[fun ω => X ω - μ[X]] = 0 := by
    rw [integral_sub h.integrable (integrable_const _)]
    simp [integral_const]
  have hcenter : (fun ω => (X ω - μ[X]) - μ[fun ω => X ω - μ[X]]) =
      fun ω => X ω - μ[X] := by
    funext ω
    rw [hmean, sub_zero]
  refine ⟨h.parameter_pos, h.integrable.sub (integrable_const _), ?_, ?_⟩
  · intro t ht
    have hexp :
        (fun ω => exp (t * (X ω - μ[X]))) =
          fun ω => exp (t * ((X ω - μ[X]) - μ[fun ω => X ω - μ[X]])) :=
      congrArg (fun f : Ω → ℝ => fun ω => exp (t * f ω)) hcenter.symm
    exact (h.integrable_exp_mul_centered t ht).congr
      (Filter.Eventually.of_forall fun ω => congrFun hexp ω)
  · intro t ht
    calc
      mgf (fun ω => (X ω - μ[X]) - μ[fun ω => X ω - μ[X]]) μ t =
          mgf (fun ω => X ω - μ[X]) μ t :=
        congrArg (fun f : Ω → ℝ => mgf f μ t) hcenter
      _ ≤ exp (K ^ 2 * t ^ 2) := h.centered_mgf_le t ht

/-- Negating a sub-exponential variable preserves its parameter. -/
theorem neg (h : HasSubexponentialMGF X K μ) : HasSubexponentialMGF (-X) K μ := by
  have hmean : μ[-X] = -μ[X] := by simp [integral_neg]
  have hcenter : (fun ω => -X ω - μ[-X]) = fun ω => -(X ω - μ[X]) := by
    funext ω
    rw [hmean]
    ring
  refine ⟨h.parameter_pos, h.integrable.neg, ?_, ?_⟩
  · intro t ht
    have hexp : (fun ω => exp (t * ((-X) ω - μ[-X]))) =
        fun ω => exp ((-t) * (X ω - μ[X])) := by
      funext ω
      rw [hmean]
      simp only [Pi.neg_apply]
      congr 1
      ring
    rw [hexp]
    exact h.integrable_exp_mul_centered (-t) (by simpa using ht)
  · intro t ht
    calc
      mgf (fun ω => -X ω - μ[-X]) μ t =
          mgf (fun ω => -(X ω - μ[X])) μ t := by
        exact congrArg (fun f : Ω → ℝ => mgf f μ t) hcenter
      _ = mgf (fun ω => X ω - μ[X]) μ (-t) := by
        have hpoint : (fun ω => -(X ω - μ[X])) = -(fun ω => X ω - μ[X]) := by
          rfl
        rw [hpoint]
        exact mgf_neg (X := fun ω => X ω - μ[X]) (μ := μ) (t := t)
      _ ≤ exp (K ^ 2 * (-t) ^ 2) :=
        h.centered_mgf_le (-t) (by simpa using ht)
      _ = exp (K ^ 2 * t ^ 2) := by simp

end HasSubexponentialMGF

end TauCeti.Probability

namespace ProbabilityTheory.iIndepFun

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω]
variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ι : Type*} {X : ι → Ω → ℝ} {t : ℝ}

/-- The MGF of a finite sum of independent, centered sub-exponential variables is bounded by
the product of their individual quadratic MGF bounds. -/
theorem mgf_sum_le_exp_of_hasSubexponentialMGF (h_indep : iIndepFun X μ) {s : Finset ι}
    {K t : ℝ} (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : |t| ≤ K⁻¹) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t ≤
      exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
  have hprod :
      mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t :=
    h_indep.mgf_sum_of_aemeasurable fun i hi =>
      (hX i hi).integrable.aestronglyMeasurable.aemeasurable
  rw [hprod]
  calc
    ∏ i ∈ s, mgf (X i) μ t ≤ ∏ i ∈ s, exp (K ^ 2 * t ^ 2) := by
      apply Finset.prod_le_prod₀ (fun i _ => mgf_nonneg)
      intro i hi
      have hbound := (hX i hi).centered_mgf_le t ht
      simpa [hmean i hi] using hbound
    _ = exp ((s.card : ℝ) * K ^ 2 * t ^ 2) := by
      rw [Finset.prod_const, ← exp_nat_mul]
      congr 1
      ring

/-- **One-sided sub-exponential Bernstein inequality.** For independent centered variables with
common parameter `K`, this bounds the upper tail of a finite sum. -/
theorem measureReal_sum_ge_le_of_hasSubexponentialMGF (h_indep : iIndepFun X μ)
   {s : Finset ι} {K t : ℝ} (hK : 0 < K)
   (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
   (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : 0 < t) :
   μ.real {ω | t ≤ ∑ i ∈ s, X i ω} ≤
     exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
 let V : ℝ := (s.card : ℝ) * K ^ 2
 let D : ℝ := V + K * t
 have hV : 0 ≤ V := by positivity
 have hD : 0 < D := by
   dsimp [D]
   positivity
 let θ : ℝ := t / (2 * D)
 have hθ : 0 < θ := by
   dsimp [θ]
   positivity
 have hθle : θ ≤ K⁻¹ := by
   calc
     θ ≤ (2 * K)⁻¹ := by
       dsimp [θ]
       rw [← one_div]
       have hden : 0 < 2 * D := mul_pos (by norm_num) hD
       have hKden : 0 < 2 * K := mul_pos (by norm_num) hK
       apply (div_le_div_iff₀ hden hKden).2
       nlinarith [hV, mul_pos hK ht]
     _ ≤ K⁻¹ := by
       rw [← one_div, ← one_div]
       rw [div_le_div_iff₀ (mul_pos (by norm_num) hK) hK]
       nlinarith [hK]
 have hθbound : |θ| ≤ K⁻¹ := by
   rw [abs_of_pos hθ]
   exact hθle
 have hupperInt : Integrable (fun ω => exp (θ * (∑ i ∈ s, X i ω))) μ := by
   exact integrable_exp_mul_sum_of_aemeasurable h_indep (s := s)
     (fun i hi => (hX i hi).integrable.aestronglyMeasurable.aemeasurable)
     (fun i hi => by
       simpa [hmean i hi] using (hX i hi).integrable_exp_mul_centered θ hθbound)
 have hexponent : -θ * t + V * θ ^ 2 ≤ -t ^ 2 / (4 * D) := by
   dsimp [θ, D, V]
   field_simp
   have hVle : (s.card : ℝ) * K ^ 2 ≤ (s.card : ℝ) * K ^ 2 + K * t := by
     nlinarith [mul_pos hK ht]
   nlinarith [sq_nonneg t, mul_nonneg (sq_nonneg t) (sub_nonneg.mpr hVle)]
 have hmgf := ProbabilityTheory.iIndepFun.mgf_sum_le_exp_of_hasSubexponentialMGF
   (s := s) h_indep hX hmean hθbound
 calc
   μ.real {ω | t ≤ ∑ i ∈ s, X i ω}
       ≤ exp (-θ * t) * mgf (fun ω => ∑ i ∈ s, X i ω) μ θ :=
         measure_ge_le_exp_mul_mgf t hθ.le hupperInt
   _ ≤ exp (-θ * t) * exp (V * θ ^ 2) := by gcongr
   _ = exp (-θ * t + V * θ ^ 2) := by rw [exp_add]
   _ ≤ exp (-t ^ 2 / (4 * D)) := (exp_le_exp).2 hexponent
   _ = exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by rfl

/-- **Sub-exponential Bernstein inequality.** If the `Xᵢ`, `i ∈ s`, are independent, centered
and sub-exponential with common parameter `K`, then for `t > 0`

`P(|∑ i ∈ s, Xᵢ| ≥ t) ≤ 2 * exp (-t^2 / (4 * (|s| * K^2 + K * t)))`.

The constants follow directly from the centered MGF bound `E exp (λ Xᵢ) ≤ exp (K ^ 2 * λ ^ 2)`
for `|λ| ≤ 1 / K`. -/
theorem measureReal_abs_sum_ge_le_of_hasSubexponentialMGF (h_indep : iIndepFun X μ)
    {s : Finset ι} {K t : ℝ} (hK : 0 < K)
    (hX : ∀ i ∈ s, HasSubexponentialMGF (X i) K μ)
    (hmean : ∀ i ∈ s, μ[X i] = 0) (ht : 0 < t) :
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|} ≤
      2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
  have hupper := measureReal_sum_ge_le_of_hasSubexponentialMGF
    h_indep hK hX hmean ht
  have hneg_indep : iIndepFun (fun i ω => -X i ω) μ :=
    h_indep.comp (fun _ => Neg.neg) (fun _ => measurable_neg)
  have hnegX : ∀ i ∈ s, HasSubexponentialMGF (-X i) K μ := fun i hi => (hX i hi).neg
  have hnegmean : ∀ i ∈ s, μ[-X i] = 0 := fun i hi => by
    simp [integral_neg, hmean i hi]
  have hsum_neg (ω : Ω) : ∑ i ∈ s, -X i ω = -(∑ i ∈ s, X i ω) := by
    rw [Finset.sum_neg_distrib]
  have hlower :
      μ.real {ω | t ≤ -∑ i ∈ s, X i ω} ≤
        exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
    have hset : {ω | t ≤ -∑ i ∈ s, X i ω} =
        {ω | t ≤ ∑ i ∈ s, -X i ω} := by
      ext ω
      simp only [Set.mem_ofPred_eq, hsum_neg ω]
    rw [hset]
    exact measureReal_sum_ge_le_of_hasSubexponentialMGF
      hneg_indep hK hnegX hnegmean ht
  have hboth :
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω}) ≤
        2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
    calc
      μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω})
          ≤ μ.real {ω | t ≤ ∑ i ∈ s, X i ω} +
              μ.real {ω | t ≤ -∑ i ∈ s, X i ω} :=
            measureReal_union_le _ _
      _ ≤ exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) +
          exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by
        exact add_le_add hupper hlower
      _ = 2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := by ring
  have hsubset :
      {ω | t ≤ |∑ i ∈ s, X i ω|} ⊆
        {ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω} := by
    intro ω hω
    simp only [Set.mem_ofPred_eq, Set.mem_union]
    by_cases hsum : 0 ≤ ∑ i ∈ s, X i ω
    · left
      simpa [abs_of_nonneg hsum] using hω
    · right
      have hsum_neg : ∑ i ∈ s, X i ω < 0 := lt_of_not_ge hsum
      simpa [abs_of_neg hsum_neg] using hω
  calc
    μ.real {ω | t ≤ |∑ i ∈ s, X i ω|}
        ≤ μ.real ({ω | t ≤ ∑ i ∈ s, X i ω} ∪ {ω | t ≤ -∑ i ∈ s, X i ω}) :=
          measureReal_mono hsubset
    _ ≤ 2 * exp (-t ^ 2 / (4 * ((s.card : ℝ) * K ^ 2 + K * t))) := hboth

end ProbabilityTheory.iIndepFun
