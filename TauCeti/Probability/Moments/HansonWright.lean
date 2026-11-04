/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Matrix.L2OpNorm
public import TauCeti.Analysis.Matrix.Realify
public import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound
public import TauCeti.Probability.Distributions.Gaussian.QuadraticForm
public import TauCeti.Probability.Independence.Decoupling
public import TauCeti.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Integration

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

private lemma integrable_and_integral_prod_le {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] {μ : Measure α} {ν : Measure β} [SigmaFinite μ] [SigmaFinite ν]
    {G : α × β → ℝ} (hG_meas : AEStronglyMeasurable G (μ.prod ν)) (hG_nn : ∀ p, 0 ≤ G p)
    {H : α → ℝ} (hH_int : Integrable H μ)
    (hslice : ∀ x, Integrable (fun y ↦ G (x, y)) ν ∧ ∫ y, G (x, y) ∂ν ≤ H x) :
    Integrable G (μ.prod ν) ∧ ∫ p, G p ∂(μ.prod ν) ≤ ∫ x, H x ∂μ := by
  have hG_int : Integrable G (μ.prod ν) := by
    rw [integrable_prod_iff hG_meas]
    refine ⟨.of_forall fun x ↦ (hslice x).1,
      hH_int.mono' hG_meas.norm.integral_prod_right' (.of_forall fun x ↦ ?_)⟩
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _),
      integral_congr_ae (.of_forall fun y ↦ Real.norm_of_nonneg (hG_nn (x, y)))]
    exact (hslice x).2
  exact ⟨hG_int, (integral_prod G hG_int).trans_le
    (integral_mono_ae hG_int.integral_prod_left hH_int (.of_forall fun x ↦ (hslice x).2))⟩

namespace TauCeti

section GaussianNormSq

/-- Exponential moment bound for `∑ i, ((M *ᵥ g) i) ^ 2` under standard Gaussian product measure. -/
theorem integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] (M : Matrix ι κ ℝ) {s : ℝ} (hs_nonneg : 0 ≤ s)
    (hs_bound : 2 * s * ‖M‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun g : κ → ℝ ↦ exp (s * ∑ i, ((M *ᵥ g) i) ^ 2))
        (Measure.pi fun _ : κ ↦ gaussianReal 0 1) ∧
      ∫ g : κ → ℝ, exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)
          ∂(Measure.pi fun _ : κ ↦ gaussianReal 0 1) ≤
        exp (2 * s * ∑ i, ∑ j, M i j ^ 2) := by
  let ν : Measure (κ → ℝ) := Measure.pi fun _ : κ ↦ gaussianReal 0 1
  let Θ : Matrix κ κ ℝ := Mᴴ * M
  have hΘ_psd : Θ.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self M
  have hΘ : Θ.IsHermitian := hΘ_psd.isHermitian
  have hM_conj : Mᴴ = Mᵀ := Matrix.conjTranspose_eq_transpose_of_trivial M
  have hquad (g : κ → ℝ) :
      ⟪WithLp.toLp 2 g, Θ.toEuclideanLin (WithLp.toLp 2 g)⟫ = ∑ i, ((M *ᵥ g) i) ^ 2 := by
    simp only [Θ, hM_conj, Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ j, ((Mᵀ * M) *ᵥ g) j * g j = g ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ g)) := by
          rw [← Matrix.mulVec_mulVec, ← dotProduct_comm]; rfl
      _ = ∑ i, ((M *ᵥ g) i) ^ 2 := by
          rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]; simp [dotProduct, sq]
  have h2s_eig (j : κ) : 2 * s * hΘ.eigenvalues j ≤ 1 / 2 := by
    let e : EuclideanSpace ℝ κ := hΘ.eigenvectorBasis j
    have heig : hΘ.eigenvalues j ≤ ‖M‖ ^ 2 := by
      calc hΘ.eigenvalues j = ⟪e, (Matrix.toEuclideanCLM (𝕜 := ℝ) Θ) e⟫ := by
            rw [hΘ.eigenvalues_eq j]
            simp only [e, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
              dotProduct, Pi.star_apply, star_trivial]
            exact Finset.sum_congr rfl fun _ _ ↦ mul_comm _ _
        _ ≤ ‖e‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) Θ) e‖ := real_inner_le_norm _ _
        _ ≤ ‖e‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Θ‖ * ‖e‖) :=
            mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) Θ).le_opNorm e)
              (norm_nonneg e)
        _ = ‖M‖ ^ 2 := by
            rw [hΘ.eigenvectorBasis.orthonormal.1 j, Matrix.l2_opNorm_toEuclideanCLM, sq,
              ← Matrix.l2_opNorm_conjTranspose_mul_self M]
            ring
    exact (mul_le_mul_of_nonneg_left heig (by positivity)).trans hs_bound
  have h2s_lt (j : κ) : 2 * s * hΘ.eigenvalues j < 1 := by linarith [h2s_eig j]
  have htoLp_meas : Measurable (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) := by fun_prop
  have hint_map : Integrable (fun x : EuclideanSpace ℝ κ ↦ exp (s * ⟪x, Θ.toEuclideanLin x⟫))
      (ν.map (WithLp.toLp 2)) := by
    rw [map_pi_eq_stdGaussian]
    exact (Probability.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff hΘ s).2 h2s_lt
  have hint_pi : Integrable (fun g : κ → ℝ ↦ exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)) ν :=
    ((integrable_map_measure hint_map.aestronglyMeasurable htoLp_meas.aemeasurable).mp
      hint_map).congr (.of_forall fun g ↦ by dsimp only [Function.comp_def]; rw [hquad g])
  have htrace : ∑ j, hΘ.eigenvalues j = ∑ i, ∑ j, M i j ^ 2 := by
    calc ∑ j, hΘ.eigenvalues j = Θ.trace := by simpa using hΘ.trace_eq_sum_eigenvalues.symm
      _ = ∑ i, ∑ j, M i j ^ 2 := by
          simp only [Θ, hM_conj, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
            Matrix.transpose_apply, sq]
          exact Finset.sum_comm
  refine ⟨hint_pi, ?_⟩
  calc ∫ g : κ → ℝ, exp (s * ∑ i, ((M *ᵥ g) i) ^ 2) ∂ν
      = mgf (fun x : EuclideanSpace ℝ κ ↦ ⟪x, Θ.toEuclideanLin x⟫)
          (stdGaussian (EuclideanSpace ℝ κ)) s := by
          rw [← map_pi_eq_stdGaussian, mgf_map htoLp_meas.aemeasurable
            hint_map.aestronglyMeasurable, mgf]
          exact integral_congr_ae
            (.of_forall fun g ↦ by dsimp only [Function.comp_def]; rw [hquad g])
    _ = ∏ j, (1 - 2 * s * hΘ.eigenvalues j) ^ (-1 / 2 : ℝ) :=
          Probability.mgf_inner_toEuclideanLin_stdGaussian hΘ h2s_lt
    _ ≤ ∏ j, exp (2 * s * hΘ.eigenvalues j) :=
          Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (by linarith [h2s_lt j]) _) fun j _ ↦
            Real.one_sub_rpow_neg_half_le_exp
              (mul_nonneg (by positivity) (hΘ_psd.eigenvalues_nonneg j)) (h2s_eig j)
    _ = exp (2 * s * ∑ i, ∑ j, M i j ^ 2) := by
          rw [← Real.exp_sum, ← Finset.mul_sum, htrace]

private lemma integral_exp_mul_dotProduct_pi_gaussianReal {γ : Type*} [Fintype γ]
    (r : ℝ) (y : γ → ℝ) :
    Integrable (fun g : γ → ℝ ↦ exp (r * (y ⬝ᵥ g)))
        (Measure.pi fun _ : γ ↦ gaussianReal 0 1) ∧
      ∫ g : γ → ℝ, exp (r * (y ⬝ᵥ g)) ∂(Measure.pi fun _ : γ ↦ gaussianReal 0 1) =
        exp (r ^ 2 / 2 * ∑ l, y l ^ 2) := by
  let ν : Measure (γ → ℝ) := Measure.pi fun _ : γ ↦ gaussianReal 0 1
  have hrew (g : γ → ℝ) : r * (y ⬝ᵥ g) = 1 * ∑ l, (r * y l) * g l := by
    simp only [dotProduct, one_mul, Finset.mul_sum, mul_assoc]
  have hmgf : mgf (fun g : γ → ℝ ↦ ∑ l, (r * y l) * g l) ν 1 = exp (r ^ 2 / 2 * ∑ l, y l ^ 2) := by
    rw [TauCeti.mgf_sum_pi (fun l u ↦ (r * y l) * u) 1]
    have hcoord (l : γ) : mgf (fun u : ℝ ↦ (r * y l) * u) (gaussianReal 0 1) 1 =
        exp (r ^ 2 / 2 * y l ^ 2) := by
      rw [mgf_const_mul, mgf_fun_id_gaussianReal]; dsimp only; congr 1
      simp only [NNReal.coe_one]; ring
    simp_rw [hcoord, ← Real.exp_sum, ← Finset.mul_sum]
  have hint : Integrable (fun g : γ → ℝ ↦ exp (1 * ∑ l, (r * y l) * g l)) ν :=
    mgf_pos_iff.mp (hmgf ▸ exp_pos _)
  exact ⟨hint.congr (.of_forall fun g ↦ by dsimp only; rw [← hrew g]),
    (integral_congr_ae (.of_forall fun g ↦ by dsimp only; rw [hrew g])).trans hmgf⟩

/-- **Gaussianization bound for Euclidean norms of sub-Gaussian linear images** (Vershynin 2018,
Lemma 6.2.3). -/
theorem integral_exp_half_mul_sum_mulVec_sq_le {Ω γ κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype γ] [Fintype κ] [DecidableEq κ]
    {V : Ω → κ → ℝ} (hV_meas : ∀ q, AEMeasurable (fun ω ↦ V ω q) P) {K : ℝ≥0}
    (hV_subG : ∀ (w : κ → ℝ) (r : ℝ), Integrable (fun ω ↦ exp (r * (V ω ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (V ω ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2))
    (M : Matrix γ κ ℝ) {a : ℝ} (ha_nonneg : 0 ≤ a) (ha_bound : (K : ℝ) * a * ‖M‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2)) P ∧
      ∫ ω, exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) ∂P ≤
        exp ((K : ℝ) * a * ∑ l, ∑ q, M l q ^ 2) := by
  classical
  let ν : Measure (γ → ℝ) := Measure.pi fun _ : γ ↦ gaussianReal 0 1
  let r : ℝ := Real.sqrt a; have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
  let F : Ω × (γ → ℝ) → ℝ := fun p ↦ exp (r * ((M *ᵥ V p.1) ⬝ᵥ p.2))
  have hF_meas : AEStronglyMeasurable F (P.prod ν) := by
    have hcont : Continuous (fun q : (κ → ℝ) × (γ → ℝ) ↦ exp (r * ((M *ᵥ q.1) ⬝ᵥ q.2))) := by
      simp only [dotProduct, Matrix.mulVec]; fun_prop
    have hm : AEMeasurable (fun p : Ω × (γ → ℝ) ↦ (V p.1, p.2)) (P.prod ν) :=
      ((AEMeasurable.of_eval hV_meas).comp_quasiMeasurePreserving
        Measure.quasiMeasurePreserving_fst).prodMk measurable_snd.aemeasurable
    exact (hcont.measurable.comp_aemeasurable hm).aestronglyMeasurable
  have hF_adj (ω : Ω) (g : γ → ℝ) : (M *ᵥ V ω) ⬝ᵥ g = V ω ⬝ᵥ (Mᵀ *ᵥ g) := by
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have hs_bound : 2 * ((K : ℝ) * a / 2) * ‖Mᵀ‖ ^ 2 ≤ 1 / 2 := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial M, Matrix.l2_opNorm_conjTranspose]; linarith
  obtain ⟨hg_int, hg_le⟩ :=
    integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le Mᵀ (by positivity) hs_bound
  have hslice_P (g : γ → ℝ) : Integrable (fun ω ↦ F (ω, g)) P ∧
      ∫ ω, F (ω, g) ∂P ≤ exp (((K : ℝ) * a / 2) * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) := by
    obtain ⟨hint, hle⟩ := hV_subG (Mᵀ *ᵥ g) r
    exact ⟨hint.congr (.of_forall fun ω ↦ by dsimp [F]; rw [hF_adj]),
      (integral_congr_ae (.of_forall fun ω ↦ show F (ω, g) = exp (r * (V ω ⬝ᵥ (Mᵀ *ᵥ g))) by
        dsimp [F]; rw [hF_adj])).trans_le (by simpa only [hr_sq] using hle)⟩
  obtain ⟨hFs_int, hFs_le⟩ := integrable_and_integral_prod_le hF_meas.prod_swap
    (fun _ ↦ (exp_pos _).le) hg_int hslice_P
  have hF_int : Integrable F (P.prod ν) := hFs_int.swap
  have hgauss_id (ω : Ω) : ∫ g, F (ω, g) ∂ν = exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) := by
    rw [(integral_exp_mul_dotProduct_pi_gaussianReal r (M *ᵥ V ω)).2, hr_sq]
  refine ⟨hF_int.integral_norm_prod_left.congr (.of_forall fun ω ↦
    (integral_congr_ae (.of_forall fun _ ↦ Real.norm_of_nonneg (exp_pos _).le)).trans
      (hgauss_id ω)), ?_⟩
  refine ((integral_congr_ae (.of_forall fun ω ↦ (hgauss_id ω).symm)).trans
    ((integral_prod F hF_int).symm.trans ((integral_prod_symm F hF_int).trans
      (integral_prod _ hFs_int).symm))).trans_le ?_
  exact (hFs_le.trans hg_le).trans_eq
    (by congr 1; simp only [Matrix.transpose_apply]; rw [Finset.sum_comm]; ring)

end GaussianNormSq

end TauCeti

namespace ProbabilityTheory.iIndepFun

private lemma mgf_decoupled_le_of_adj {Ω κ : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] [Fintype κ] [DecidableEq κ]
    {V : Ω → κ → ℝ} (hV_meas : ∀ q, AEMeasurable (fun ω ↦ V ω q) P) {K : ℝ≥0}
    (hV_subG : ∀ (w : κ → ℝ) (r : ℝ), Integrable (fun ω ↦ exp (r * (V ω ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (V ω ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2))
    (M : Matrix κ κ ℝ) {u : ℝ} (hu : (K : ℝ) * |u| * ‖M‖ ≤ 1 / 2)
    {Φ : Ω × Ω → ℝ} (hadj : ∀ ω₁ ω₂, Φ (ω₁, ω₂) = V ω₂ ⬝ᵥ (M *ᵥ V ω₁)) :
    Integrable (fun p ↦ exp (u * Φ p)) (P.prod P) ∧
      mgf Φ (P.prod P) u ≤ exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ l, ∑ q, M l q ^ 2) := by
  have hV_vec : AEMeasurable V P := AEMeasurable.of_eval hV_meas
  have hcont : Continuous (fun q : (κ → ℝ) × (κ → ℝ) ↦ exp (u * (q.2 ⬝ᵥ (M *ᵥ q.1)))) := by
    simp only [dotProduct, Matrix.mulVec]; fun_prop
  have hG_meas : AEStronglyMeasurable (fun p : Ω × Ω ↦ exp (u * Φ p)) (P.prod P) := by
    rw [show (fun p : Ω × Ω ↦ exp (u * Φ p)) = fun p ↦ exp (u * (V p.2 ⬝ᵥ (M *ᵥ V p.1))) from
      funext fun ⟨ω₁, ω₂⟩ ↦ by dsimp only; rw [hadj ω₁ ω₂]]
    have hm := (hV_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
      (hV_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
    exact (hcont.measurable.comp_aemeasurable hm).aestronglyMeasurable
  have ha_bound : (K : ℝ) * ((K : ℝ) * u ^ 2) * ‖M‖ ^ 2 ≤ 1 / 2 := by
    rw [← sq_abs u]; nlinarith [pow_le_pow_left₀ (by positivity) hu 2]
  obtain ⟨hX1_int, hX1_le⟩ :=
    TauCeti.integral_exp_half_mul_sum_mulVec_sq_le hV_meas hV_subG M (by positivity) ha_bound
  obtain ⟨hG_int, hG_le⟩ := integrable_and_integral_prod_le hG_meas (fun _ ↦ (exp_pos _).le)
    hX1_int fun ω₁ ↦ by
      obtain ⟨hint, hle⟩ := hV_subG (M *ᵥ V ω₁) u
      exact ⟨hint.congr (.of_forall fun ω₂ ↦ by dsimp only; rw [hadj ω₁ ω₂]),
        (integral_congr_ae (.of_forall fun ω₂ ↦
          show exp (u * Φ (ω₁, ω₂)) = exp (u * (V ω₂ ⬝ᵥ (M *ᵥ V ω₁))) by
            rw [hadj ω₁ ω₂])).trans_le hle⟩
  exact ⟨hG_int, (hG_le.trans hX1_le).trans_eq (by congr 1; ring)⟩

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
    rw [← show ∑ j : ι, (if i = j then ‖A i i‖ ^ 2 else 0) = ‖A i i‖ ^ 2 by simp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rcases eq_or_ne i j with rfl | hij <;> simp_all
  have h1 : 0 ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have h2 : 0 ≤ ∑ i, ∑ j, ‖(A - Matrix.diagonal A.diag) i j‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  refine ⟨fun i ↦ by simp, by linarith, by linarith, ?_, fun a ha ↦ ?_⟩
  · rw [show (4 : ℝ) * (2 * θ) = 8 * θ by ring, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    exact (mul_le_mul_of_nonneg_left A.l2_opNorm_sub_diagonal_diag_le (by positivity)).trans
      (by linarith)
  · rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact (show (K : ℝ) * (2 * |θ| * |a|) ≤ (K : ℝ) * (2 * |θ| * ‖A‖) by gcongr).trans (by linarith)

private lemma mgf_sum_le_of_iIndepFun {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}
    {D : ι → Ω → ℝ} (hD_indep : iIndepFun D P) (hD_meas : ∀ i, AEMeasurable (D i) P)
    {s c : ℝ} (hc : 0 ≤ c) {w : ι → ℝ} {W : ℝ} (hw : ∑ i, w i ≤ W)
    (hterm : ∀ i, Integrable (fun ω ↦ exp (s * D i ω)) P ∧ mgf (D i) P s ≤ exp (c * w i)) :
    Integrable (fun ω ↦ exp (s * ∑ i, D i ω)) P ∧
      mgf (fun ω ↦ ∑ i, D i ω) P s ≤ exp (c * W) := by
  have : IsProbabilityMeasure P := hD_indep.isProbabilityMeasure
  have hmgf_eq : mgf (∑ i : ι, D i) P s = ∏ i : ι, mgf (D i) P s :=
    hD_indep.mgf_sum₀ hD_meas Finset.univ
  have hpos : 0 < mgf (∑ i : ι, D i) P s := hmgf_eq ▸ Finset.prod_pos fun i _ ↦ mgf_pos (hterm i).1
  refine ⟨(mgf_pos_iff.mp hpos).congr (.of_forall fun _ ↦ by simp), ?_⟩
  rw [show (fun ω ↦ ∑ i, D i ω) = ∑ i : ι, D i by ext; simp, hmgf_eq]
  exact (Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) fun i _ ↦ (hterm i).2).trans
    ((Real.exp_sum _ _).symm.trans_le
      (exp_le_exp.2 (by rw [← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hw hc)))

private lemma integral_star_dotProduct_mulVec_eq_sum_diag_aux {Ω ι 𝕜 : Type*} [MeasurableSpace Ω]
    [Fintype ι] [RCLike 𝕜] {P : Measure Ω} {W : ι → Ω → 𝕜} (hindep : iIndepFun W P)
    (hW_int : ∀ i, Integrable (W i) P) (hW_sq : ∀ i, Integrable (fun ω ↦ ‖W i ω‖ ^ 2) P)
    (hW_mean : ∀ i, ∫ ω, W i ω ∂P = 0) (A : Matrix ι ι 𝕜) :
    Integrable (fun ω ↦ star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω)) P ∧
      ∫ ω, star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖W i ω‖ ^ 2] : ℝ) : 𝕜) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hW_star (i : ι) : Integrable (fun ω ↦ star (W i ω)) P :=
    (hW_int i).mono (continuous_star.comp_aestronglyMeasurable (hW_int i).1)
      (.of_forall fun _ ↦ by simp)
  have hexpand (ω : Ω) : star (fun i ↦ W i ω) ⬝ᵥ A *ᵥ (fun i ↦ W i ω) =
      ∑ i, ∑ j, A i j * (star (W i ω) * W j ω) := by
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
  have hcast (i : ι) (ω : Ω) :
      A i i * (star (W i ω) * W i ω) = A i i * ((‖W i ω‖ ^ 2 : ℝ) : 𝕜) := by
    rw [RCLike.star_def, RCLike.conj_mul]; norm_cast
  have hterm_int (i j : ι) : Integrable (fun ω ↦ A i j * (star (W i ω) * W j ω)) P := by
    by_cases hij : i = j
    · subst hij
      exact (((RCLike.ofRealCLM (K := 𝕜)).integrable_comp (hW_sq i)).const_mul (A i i)).congr
        (.of_forall fun ω ↦ (hcast i ω).symm)
    · exact (((hindep.indepFun hij).comp continuous_star.measurable measurable_id).integrable_smul
        (hW_star i) (hW_int j)).const_mul (A i j)
  refine ⟨(integrable_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j).congr
    (.of_forall fun ω ↦ (hexpand ω).symm), ?_⟩
  rw [integral_congr_ae (.of_forall hexpand), integral_finsetSum Finset.univ fun i _ ↦
    integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_finsetSum Finset.univ fun j _ ↦ hterm_int i j, Finset.sum_eq_single i]
  · rw [integral_congr_ae (.of_forall (hcast i)), integral_const_mul]
    exact congrArg (A i i * ·) ((RCLike.ofRealCLM (K := 𝕜)).integral_comp_comm (hW_sq i))
  · intro j _ hji
    have hmul := ((hindep.indepFun hji.symm).comp continuous_star.measurable
      measurable_id).integral_fun_mul_eq_mul_integral (hW_star i).1 (hW_int j).1
    dsimp only [Function.comp_def, id_eq] at hmul
    rw [integral_const_mul, hmul, hW_mean j, mul_zero, mul_zero]
  · exact fun hi ↦ absurd (Finset.mem_univ i) hi

section RealHansonWright

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- Expectation of `Xᵀ A X` for independent `K`-sub-Gaussian real coordinates. -/
theorem integral_dotProduct_mulVec_eq_sum_diag {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P) (A : Matrix ι ι ℝ) :
    Integrable (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω)) P ∧
      ∫ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) ∂P =
        ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  simpa using hindep.integral_star_dotProduct_mulVec_eq_sum_diag_aux (fun i ↦ (hX i).integrable)
    (fun i ↦ by simpa using ((hX i).memLp 2).integrable_sq) (fun i ↦ (hX i).integral_eq_zero) A

private lemma subgaussian_dotProduct_of_iIndepFun {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P) (w : ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * ((fun i ↦ X i ω) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * ((fun i ↦ X i ω) ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ i, w i ^ 2) := by
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i : ι, w i * X i ω)
      (∑ i : ι, ⟨w i ^ 2, sq_nonneg (w i)⟩ * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i x ↦ w i * x) fun i ↦ measurable_const_mul (w i))
      fun i _ ↦ (hX i).const_mul (w i)
  have hdot (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ w = ∑ i, w i * X i ω := by simp only [dotProduct, mul_comm]
  refine ⟨(hsum.integrable_exp_mul r).congr (.of_forall fun ω ↦ by dsimp only; rw [hdot ω]), ?_⟩
  refine ((integral_congr_ae (.of_forall fun ω ↦ by dsimp only; rw [hdot ω])).trans_le
    (hsum.mgf_le r)).trans_eq ?_
  congr 1; rw [NNReal.coe_sum]
  change (∑ i : ι, w i ^ 2 * (K : ℝ)) * r ^ 2 / 2 = _
  rw [← Finset.sum_mul]; ring

variable [DecidableEq ι]

/-- **Decoupled bilinear MGF bound (real case).** -/
theorem mgf_decoupled_dotProduct_mulVec_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (B : Matrix ι ι ℝ) {u : ℝ} (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) u ≤
      exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, B i j ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hu' : (K : ℝ) * |u| * ‖Bᵀ‖ ≤ 1 / 2 := by
    rwa [← Matrix.conjTranspose_eq_transpose_of_trivial B, Matrix.l2_opNorm_conjTranspose]
  obtain ⟨hint, hle⟩ := mgf_decoupled_le_of_adj (fun i ↦ (hX i).aemeasurable)
    (hindep.subgaussian_dotProduct_of_iIndepFun hX) Bᵀ hu'
    (Φ := fun p ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) fun _ _ ↦ by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  exact ⟨hint, hle.trans_eq
    (by congr 1; rw [Finset.sum_comm]; simp only [Matrix.transpose_apply])⟩

/-- **Sub-exponential MGF bound for centred sub-Gaussian quadratic forms.** -/
theorem mgf_dotProduct_mulVec_sub_integral_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (A : Matrix ι ι ℝ) {θ : ℝ} (hθ : 32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1) :
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
      linarith [show (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, B i j ^ 2 =
        64 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, B i j ^ 2 by ring]))
  let m (i : ι) : ℝ := ∫ ω', X i ω' ^ 2 ∂P
  let D : ι → Ω → ℝ := fun i ω ↦ A i i * (X i ω ^ 2 - m i)
  have hD_indep : iIndepFun D P :=
    hindep.comp (fun i x ↦ A i i * (x ^ 2 - m i)) fun _ ↦ by fun_prop
  have hD_meas (i : ι) : AEMeasurable (D i) P :=
    (((measurable_id.pow_const 2).comp_aemeasurable (hX i).aemeasurable).sub_const _).const_mul _
  obtain ⟨hD_sum_int, hD_bound⟩ := mgf_sum_le_of_iIndepFun hD_indep hD_meas
    (c := 1536 * (K : ℝ) ^ 2 * θ ^ 2) (by positivity) hdiag_frob fun i ↦ by
      have hθi : (K : ℝ) * |(2 * θ) * A i i| ≤ 1 / 8 :=
        (hentry _ (by simpa using A.norm_entry_le_l2_opNorm i i)).trans (by norm_num)
      obtain ⟨hint_i, hmgf_i⟩ := (hX i).mgf_sq_sub_integral_le hθi
      exact ⟨hint_i.congr (.of_forall fun ω ↦ by dsimp [D, m]; ring_nf),
        (mgf_const_mul (A i i)).trans_le
          ((mul_comm (A i i) (2 * θ) ▸ hmgf_i).trans_eq (by congr 1; ring))⟩
  have hsplit (ω : Ω) : (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P =
        (∑ i, D i ω) + ((fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) := by
    rw [(hindep.integral_dotProduct_mulVec_eq_sum_diag hX A).2]
    nth_rw 1 [show A = Matrix.diagonal A.diag + B by simp [B]]
    rw [Matrix.add_mulVec, dotProduct_add, show (fun i ↦ X i ω) ⬝ᵥ Matrix.diagonal A.diag *ᵥ
      (fun i ↦ X i ω) = ∑ i, A i i * X i ω ^ 2 by
      simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diag_apply]
      exact Finset.sum_congr rfl fun _ _ ↦ by ring]
    simp only [D, m, mul_sub, Finset.sum_sub_distrib]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  exact ⟨hint, hle.trans_eq (by congr 1; ring)⟩

/-- **One-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013) with constant `1 / 3200`. -/
theorem measureReal_dotProduct_mulVec_sub_integral_gt_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P) (A : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P} ≤
      exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [← show min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 by norm_num]
  exact ProbabilityTheory.measureReal_gt_le_exp_min_of_mgf_le (by norm_num) (by norm_num)
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (mul_nonneg K.coe_nonneg (norm_nonneg A))
    (fun θ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

/-- **Two-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013, Theorem 1.1) with constant
`1 / 3200`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_integral_gt_le {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (A : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [← show min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 by norm_num]
  exact ProbabilityTheory.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le (by norm_num)
    (by norm_num)
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (mul_nonneg K.coe_nonneg (norm_nonneg A))
    (fun θ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

private lemma measurable_hwClipped (K : ℝ≥0) (t : ℝ) :
    Measurable fun M : Matrix ι ι ℝ ↦ min (1 : ℝ) (2 * exp (-(1 / 3200) *
      min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2)) (t / ((K : ℝ) * ‖M‖)))) := by
  have h1 : Measurable (fun M : Matrix ι ι ℝ ↦ ∑ i, ∑ j, M i j ^ 2) :=
    Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
      (Matrix.measurable_apply (i := i) (j := j)).pow_const 2
  have h2 : Measurable (fun M : Matrix ι ι ℝ ↦ ‖M‖) := continuous_norm.measurable
  fun_prop

open Classical in
private lemma measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral_if
    {X : ι → Ω → ℝ} (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P)
    (hAX : IndepFun A (fun ω i ↦ X i ω) P) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun ω ↦ if A ω = 0 then (0 : ℝ) else min 1 (2 * exp (-(1 / 3200) *
      min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A ω i j ^ 2)) (t / ((K : ℝ) * ‖A ω‖))))) P ∧
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
      ∫ ω, (if A ω = 0 then 0 else min 1 (2 * exp (-(1 / 3200) *
        min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A ω i j ^ 2)) (t / ((K : ℝ) * ‖A ω‖))))) ∂P := by
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
  let ψ : Matrix ι ι ℝ → ℝ := fun M ↦ if M = 0 then 0 else min 1 (2 * exp (-(1 / 3200) *
    min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2)) (t / ((K : ℝ) * ‖M‖))))
  have h0_meas : MeasurableSet {M : Matrix ι ι ℝ | M = 0} := by
    simpa only [norm_le_zero_iff] using measurableSet_le
      (continuous_norm : Continuous fun M : Matrix ι ι ℝ ↦ ‖M‖).measurable
      (measurable_const (a := (0 : ℝ)))
  have hψ_meas : Measurable ψ := Measurable.ite h0_meas measurable_const (measurable_hwClipped K t)
  have hψ_int : Integrable ψ μA :=
    Integrable.of_mem_Icc 0 1 hψ_meas.aemeasurable (.of_forall fun M ↦ by
      dsimp [ψ]; split_ifs <;>
        [exact ⟨le_rfl, zero_le_one⟩; exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩])
  have hslice_le (M : Matrix ι ι ℝ) : μX.real (Prod.mk M ⁻¹' E) ≤ ψ M := by
    by_cases hM0 : M = 0
    · subst hM0
      have hemp : Prod.mk (0 : Matrix ι ι ℝ) ⁻¹' E = ∅ := by ext x; simp [E, not_lt.2 ht]
      simp [ψ, hemp]
    · simp only [ψ, hM0, ↓reduceIte]
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
    rw [show (fun x ↦ E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x)) =
      (Prod.mk M ⁻¹' E).indicator 1 by ext x; by_cases hx : (M, x) ∈ E <;> simp [hx],
      integral_indicator_one (hE_meas.preimage measurable_prodMk_left)]
  refine ⟨(integrable_map_measure hψ_meas.aestronglyMeasurable hA_meas).mp hψ_int, ?_⟩
  rw [show P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = (μA.prod μX).real E by
    rw [← hAX.map_prod_eq_prod_map_map hA_meas hX_vec,
      map_measureReal_apply_of_aemeasurable (hA_meas.prodMk hX_vec) hE_meas]; rfl,
    ← integral_indicator_one hE_meas, integral_prod _ hind_int]
  exact ((integral_congr_ae (.of_forall hslice_eq)).trans_le
    (integral_mono_ae (hind_int.integral_prod_left.congr (.of_forall hslice_eq))
      hψ_int (.of_forall hslice_le))).trans_eq (integral_map hA_meas hψ_meas.aestronglyMeasurable)

/-- **Integrated conditional Hanson–Wright inequality** for an independent random matrix `A`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
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
  · split_ifs <;> [exact le_min zero_le_one (by positivity); exact le_rfl]

/-- **Conditional Hanson–Wright inequality under a.s. norm bounds.** -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
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
  split_ifs with hM0
  · positivity
  · obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j, A ω i j ≠ 0 := by by_contra! h; exact hM0 (Matrix.ext h)
    have hMf_pos : 0 < ∑ i, ∑ j, A ω i j ^ 2 :=
      lt_of_lt_of_le (sq_pos_of_ne_zero hij₀)
        ((Finset.single_le_sum (fun j _ ↦ sq_nonneg (A ω i₀ j)) (Finset.mem_univ j₀)).trans
          (Finset.single_le_sum (fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
            (Finset.mem_univ i₀)))
    have hMop_pos : 0 < ‖A ω‖ := norm_pos_iff.2 hM0
    refine (min_le_right _ _).trans (mul_le_mul_of_nonneg_left (exp_le_exp.2 ?_) zero_le_two)
    have hmin : min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op)) ≤
        min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A ω i j ^ 2)) (t / ((K : ℝ) * ‖A ω‖)) :=
      min_le_min
        (div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
          (mul_le_mul_of_nonneg_left hMf (sq_nonneg _)))
        (div_le_div_of_nonneg_left ht (by positivity) (mul_le_mul_of_nonneg_left hMop hK_pos.le))
    linarith

end RealHansonWright

section ComplexHansonWright

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- Expectation of `star Z ⬝ᵥ A *ᵥ Z` for independent directionally sub-Gaussian complex `Z`. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0} (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) :
    Integrable (fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)) P ∧
      ∫ ω, star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖Z i ω‖ ^ 2] : ℝ) : ℂ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  exact hindep.integral_star_dotProduct_mulVec_eq_sum_diag_aux
    (fun i ↦ integrable_of_hasSubgaussianMGF_re_star_mul (hZ i))
    (fun i ↦ ((((hasSubgaussianMGF_re_of_star_mul (hZ i)).memLp 2).integrable_sq).add
      (((hasSubgaussianMGF_im_of_star_mul (hZ i)).memLp 2).integrable_sq)).congr
      (.of_forall fun _ ↦ by
        dsimp only [Pi.add_apply]; rw [Complex.sq_norm, Complex.normSq_apply]; ring))
    (fun i ↦ integral_eq_zero_of_hasSubgaussianMGF_re_star_mul (hZ i)) A

private lemma subgaussian_realify_dotProduct_of_iIndepFun {Z : ι → Ω → ℂ}
    (hindep : iIndepFun Z P) {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (w : ι ⊕ ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)) ∂P ≤
        exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2) := by
  let u : ι → ℂ := fun i ↦ ⟨w (.inl i), w (.inr i)⟩
  let W : ι → Ω → ℝ := fun i ω ↦ (star (u i) * Z i ω).re
  have hW_subG : HasSubgaussianMGF (fun ω ↦ ∑ i : ι, W i ω) (∑ i : ι, ‖u i‖₊ ^ 2 * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun
      (hindep.comp (fun i z ↦ (star (u i) * z).re) fun _ ↦ by fun_prop) fun i _ ↦ hZ i (u i)
  have hdot (ω : Ω) : Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w = ∑ i, W i ω := by
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← Finset.sum_add_distrib, W, u, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    exact Finset.sum_congr rfl fun _ _ ↦ by ring
  have hnorm_sum : ∑ i : ι, ‖u i‖ ^ 2 = ∑ q : ι ⊕ ι, w q ^ 2 := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [Complex.sq_norm, Complex.normSq_apply]; simp [u, sq]
  refine ⟨(hW_subG.integrable_exp_mul r).congr (.of_forall fun ω ↦ by dsimp only; rw [hdot ω]), ?_⟩
  refine ((integral_congr_ae (.of_forall fun ω ↦ by dsimp only; rw [hdot ω])).trans_le
    (hW_subG.mgf_le r)).trans_eq ?_
  congr 1; push_cast; rw [← Finset.sum_mul, hnorm_sum]; ring

variable [DecidableEq ι]

/-- **Decoupled sesquilinear MGF bound (complex case).** -/
theorem mgf_decoupled_re_star_dotProduct_mulVec_le {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (B : Matrix ι ι ℂ) {u : ℝ} (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re)) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re) (P.prod P) u ≤
      exp (2 * (K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let V : Ω → ι ⊕ ι → ℝ := fun ω ↦ Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im)
  have hZ_meas (i : ι) := (integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)).aemeasurable
  have hV_meas (q : ι ⊕ ι) : AEMeasurable (fun ω ↦ V ω q) P := by
    rcases q with i | i
    · exact Complex.continuous_re.measurable.comp_aemeasurable (hZ_meas i)
    · exact Complex.continuous_im.measurable.comp_aemeasurable (hZ_meas i)
  have hu' : (K : ℝ) * |u| * ‖(Bᴴ).realify‖ ≤ 1 / 2 := by
    rwa [Matrix.l2_opNorm_realify, Matrix.l2_opNorm_conjTranspose]
  obtain ⟨hint, hle⟩ := mgf_decoupled_le_of_adj hV_meas
    (hindep.subgaussian_realify_dotProduct_of_iIndepFun hZ) (Bᴴ).realify hu'
    (Φ := fun p ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re) fun ω₁ ω₂ ↦ by
      calc (star (fun i ↦ Z i ω₁) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω₂)).re
          = V ω₁ ⬝ᵥ B.realify *ᵥ V ω₂ := by
            simp only [V, dotProduct, Matrix.mulVec, Fintype.sum_sum_type, Complex.mul_re,
              Complex.mul_im, Sum.elim_inl, Sum.elim_inr, Matrix.realify_apply_inl_inl,
              Matrix.realify_apply_inl_inr, Matrix.realify_apply_inr_inl,
              Matrix.realify_apply_inr_inr, RCLike.re_eq_complex_re, RCLike.im_eq_complex_im,
              Pi.star_apply, Complex.re_sum, Complex.star_def, Complex.conj_re, Complex.conj_im,
              Finset.mul_sum, ← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring
        _ = V ω₂ ⬝ᵥ ((Bᴴ).realify *ᵥ V ω₁) := by
            rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
              Matrix.realify_conjTranspose]
  exact ⟨hint, hle.trans_eq (by
    congr 1; rw [Matrix.sum_sq_realify, Finset.sum_comm]
    simp only [Matrix.conjTranspose_apply, norm_star]; ring)⟩

/-- **Centred MGF bound for the real part of a complex sub-Gaussian sesquilinear form.** -/
theorem mgf_re_star_dotProduct_mulVec_sub_integral_le {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) {θ : ℝ} (hθ : 32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1) :
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
      linarith [show 2 * (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 =
        128 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 by ring]))
  let m (i : ι) : ℝ := ∫ ω', ‖Z i ω'‖ ^ 2 ∂P
  let D : ι → Ω → ℝ := fun i ω ↦ (A i i).re * (‖Z i ω‖ ^ 2 - m i)
  have hD_indep : iIndepFun D P :=
    hindep.comp (fun i z ↦ (A i i).re * (‖z‖ ^ 2 - m i)) fun _ ↦ by fun_prop
  have hD_meas (i : ι) : AEMeasurable (D i) P :=
    ((((continuous_norm.pow 2).measurable.comp_aemeasurable
      (hZ_int i).aemeasurable)).sub_const _).const_mul _
  obtain ⟨hD_sum_int, hD_bound⟩ := mgf_sum_le_of_iIndepFun hD_indep hD_meas
    (c := 6144 * (K : ℝ) ^ 2 * θ ^ 2) (by positivity) hdiag_frob fun i ↦ by
      have hθi := hentry _ ((Complex.abs_re_le_norm _).trans (A.norm_entry_le_l2_opNorm i i))
      obtain ⟨hint_i, hmgf_i⟩ :=
        mgf_norm_sq_sub_integral_le_of_hasSubgaussianMGF_re_star_mul (hZ i) hθi
      have hre_sq : (A i i).re ^ 2 ≤ ‖A i i‖ ^ 2 :=
        sq_le_sq.2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact Complex.abs_re_le_norm _)
      exact ⟨hint_i.congr (.of_forall fun ω ↦ by dsimp [D, m]; ring_nf),
        (mgf_const_mul (A i i).re).trans_le (((mul_comm (A i i).re (2 * θ) ▸ hmgf_i).trans_eq
          (by congr 1; ring)).trans
          (exp_le_exp.2 (mul_le_mul_of_nonneg_left hre_sq (by positivity))))⟩
  obtain ⟨hquad_int, hquad_mean⟩ := hindep.integral_star_dotProduct_mulVec_eq_sum_diag hZ A
  have hre_mean : ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
      ∑ i, (A i i).re * m i := by
    have h1 : ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
        (∫ ω', star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω') ∂P).re := by
      simpa only [Complex.reCLM_apply] using Complex.reCLM.integral_comp_comm hquad_int
    rw [h1, hquad_mean, Complex.re_sum]
    exact Finset.sum_congr rfl fun _ _ ↦ by simp [m, Complex.mul_re]
  have hsplit (ω : Ω) : (star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
      ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
        (∑ i, D i ω) + (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re := by
    rw [hre_mean]; nth_rw 1 [show A = Matrix.diagonal A.diag + B by simp [B]]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re,
      show (star (fun i ↦ Z i ω) ⬝ᵥ Matrix.diagonal A.diag *ᵥ (fun i ↦ Z i ω)).re =
        ∑ i, (A i i).re * ‖Z i ω‖ ^ 2 by
      simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diag_apply, Pi.star_apply,
        Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [Complex.sq_norm, Complex.normSq_apply]; simp only [Complex.star_def, Complex.mul_re,
        Complex.mul_im, Complex.conj_re, Complex.conj_im]; ring]
    simp only [D, mul_sub, Finset.sum_sub_distrib]; ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  exact ⟨hint, hle.trans_eq (by congr 1; ring)⟩

/-- **Complex Hanson–Wright inequality (real part)** with constant `1 / 12544`. -/
theorem measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le {Z : ι → Ω → ℂ}
    (hindep : iIndepFun Z P) {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
        ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P|} ≤
      2 * exp (-(1 / 12544) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  rw [← show min (1 / (4 * (3136 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 12544 by norm_num]
  exact ProbabilityTheory.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le (by norm_num)
    (by norm_num)
    (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (mul_nonneg K.coe_nonneg (norm_nonneg A))
    (fun θ hθ ↦ hindep.mgf_re_star_dotProduct_mulVec_sub_integral_le hZ A hθ) ht

/-- **Complex Hanson–Wright inequality (full complex norm)** with constant `1 / 150528`. -/
theorem measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le {Z : ι → Ω → ℂ}
    (hindep : iIndepFun Z P) {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < ‖star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) -
        ∫ ω', star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω') ∂P‖} ≤
      2 * exp (-(1 / 150528) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let Q : Ω → ℂ := fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)
  have hQ_int : Integrable Q P := (hindep.integral_star_dotProduct_mulVec_eq_sum_diag hZ A).1
  let AI : Matrix ι ι ℂ := (-Complex.I) • A
  have hAI_re (ω : Ω) : (star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re = (Q ω).im := by
    rw [show star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω) = (-Complex.I) * Q ω by
      simp only [AI, Q, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by ring]
    simp [Complex.mul_re]
  have hsub : {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ⊆
      {ω | t / 2 < |(Q ω).re - ∫ ω', (Q ω').re ∂P|} ∪
        {ω | t / 2 < |(star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re -
          ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω')).re ∂P|} := by
    intro ω (hω : t < ‖Q ω - ∫ ω', Q ω' ∂P‖)
    have hre_q : (∫ ω', Q ω' ∂P).re = ∫ ω', (Q ω').re ∂P := by
      simpa only [Complex.reCLM_apply] using (Complex.reCLM.integral_comp_comm hQ_int).symm
    have him_q : (∫ ω', Q ω' ∂P).im = ∫ ω', (Q ω').im ∂P := by
      simpa only [Complex.imCLM_apply] using (Complex.imCLM.integral_comp_comm hQ_int).symm
    simp only [Set.mem_union, Set.mem_ofPred_eq, hAI_re]; by_contra! h
    have hre : ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_re, hre_q, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.1 2
    have him : ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_im, him_q, ← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h.2 2
    have hns : ‖Q ω - ∫ ω', Q ω' ∂P‖ ^ 2 =
        ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 + ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    nlinarith [pow_lt_pow_left₀ hω ht (by norm_num : 2 ≠ 0)]
  let F := (K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2; let op := (K : ℝ) * ‖A‖
  let m : ℝ := min (t ^ 2 / F) (t / op)
  have hm_half : m / 4 ≤ min ((t / 2) ^ 2 / F) ((t / 2) / op) :=
    le_min (by linarith [min_le_left (t ^ 2 / F) (t / op),
        show (t / 2) ^ 2 / F = (t ^ 2 / F) / 4 by ring])
      (by linarith [min_le_right (t ^ 2 / F) (t / op),
        div_nonneg ht (mul_nonneg K.coe_nonneg (norm_nonneg A)),
        show (t / 2) / op = (t / op) / 2 by ring])
  have h1 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ A
    (by positivity : 0 ≤ t / 2)
  have h2 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ AI
    (by positivity : 0 ≤ t / 2)
  rw [show ‖AI‖ = ‖A‖ by rw [norm_smul, norm_neg, Complex.norm_I, one_mul],
    show ∑ i, ∑ j, ‖AI i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 from
      Finset.sum_congr rfl fun _ _ ↦ Finset.sum_congr rfl fun _ _ ↦ by simp [AI]] at h2
  have hexp_le : exp (-(1 / 12544) * min ((t / 2) ^ 2 / F) ((t / 2) / op)) ≤
      exp (-(1 / 50176) * m) := exp_le_exp.2 (by linarith)
  have h4 : P.real {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ≤ 4 * exp (-(1 / 50176) * m) :=
    ((measureReal_mono hsub).trans (measureReal_union_le _ _)).trans
      (by dsimp [F, op] at *; linarith)
  let u : ℝ := exp (-(1 / 150528) * m)
  change _ ≤ 2 * u
  by_cases hu_half : 1 / 2 ≤ u
  · exact ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ).trans (by linarith)
  · have hu_pos : 0 < u := exp_pos _
    refine h4.trans ((show 4 * exp (-(1 / 50176) * m) = 4 * u ^ 2 * u by
      dsimp [u]; rw [mul_assoc, ← pow_succ, ← exp_nat_mul]; congr 2; push_cast; ring).trans_le ?_)
    exact mul_le_mul_of_nonneg_right (by nlinarith) hu_pos.le

/-- **Complex Hanson–Wright inequality for bounded mean-zero coordinates.** -/
theorem measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le_of_norm_le
    {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P) (hZ_meas : ∀ i, AEMeasurable (Z i) P) {b : ℝ≥0}
    (hZ_norm : ∀ i, ∀ᵐ ω ∂P, ‖Z i ω‖ ≤ b) (hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0)
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
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
  let μ₀ : Measure B :=
    (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (.up true) + Measure.dirac (.up false))
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
  have hrad_subG : HasSubgaussianMGF rad 1 μ₀ :=
    (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hrad_meas.aemeasurable
      (.of_forall fun ⟨b⟩ ↦ show rad ⟨b⟩ ∈ Set.Icc (-1) 1 by cases b <;> simp [rad])
      hrad_mean).mono (by rw [← NNReal.coe_le_coe]; push_cast; norm_num)
  let P : Measure (Fin 2 → B) := Measure.pi fun _ : Fin 2 ↦ μ₀
  let X : Fin 2 → (Fin 2 → B) → ℝ := fun i ω ↦ rad (ω i)
  have hindep : iIndepFun X P := iIndepFun_pi fun _ ↦ hrad_meas.aemeasurable
  have hX_subG (i : Fin 2) : HasSubgaussianMGF (X i) 1 P := by
    change HasSubgaussianMGF (rad ∘ fun f : Fin 2 → B ↦ f i) 1 P
    refine HasSubgaussianMGF.of_map (measurable_pi_apply i).aemeasurable ?_
    rwa [show (fun f : Fin 2 → B ↦ f i) = Function.eval i from rfl,
      (measurePreserving_eval (fun _ : Fin 2 ↦ μ₀) i).map_eq]
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![0, 1], ![1, 0]]
  have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P = 0 := by
    rw [(hindep.integral_dotProduct_mulVec_eq_sum_diag hX_subG A).2, Fin.sum_univ_two]; simp [A]
  have hevent : {ω | (1 : ℝ) < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} = Set.univ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]; rw [hmean, sub_zero]
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, A, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, X, rad]
    cases h0 : (ω 0).down <;> cases h1 : (ω 1).down <;> norm_num [h0, h1]
  have hop : ‖A‖ = 1 := by
    refine le_antisymm ?_ (by simpa [A] using A.norm_entry_le_l2_opNorm 0 1)
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (𝕜 := ℝ) A).opNorm_le_bound zero_le_one fun v ↦ ?_
    rw [one_mul]; refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two,
      Fin.sum_univ_two,
      show ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) v).ofLp 0 = v.ofLp 1 by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A],
      show ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) v).ofLp 1 = v.ofLp 0 by
        simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A], add_comm]
  have hbound := hc P X 1 hindep hX_subG A 1 zero_le_one
  rw [hevent, probReal_univ, show ∑ i : Fin 2, ∑ j : Fin 2, A i j ^ 2 = 2 by
    simp [Fin.sum_univ_two, A]; norm_num, hop] at hbound
  simp only [NNReal.coe_one, one_pow, one_mul, div_one] at hbound
  rw [show min ((1 : ℝ) / 2) 1 = 1 / 2 by norm_num] at hbound
  have hlog := Real.log_le_log (by positivity)
    (by linarith : (2 : ℝ)⁻¹ ≤ Real.exp (-c * (1 / 2)))
  rw [Real.log_inv, Real.log_exp] at hlog; linarith

end TauCeti
