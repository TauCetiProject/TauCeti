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

Let `(Xᵢ)_{i : ι}` be independent real random variables on a probability space `(Ω, P)`, each
satisfying `HasSubgaussianMGF (X i) K P` with variance proxy `K : ℝ≥0` (which in particular forces
`P[X i] = 0`), and let `A : Matrix ι ι ℝ` be a real square matrix. The **Hanson–Wright inequality**
(Hanson–Wright 1971; Rudelson–Vershynin 2013) bounds the tails of the quadratic form
`Q(ω) = X(ω)ᵀ A X(ω)` around its expectation `P[Q] = ∑ i, A i i * P[X i ^ 2]` by a sub-exponential
rate governed simultaneously by the Frobenius norm `‖A‖_F² = ∑ i, ∑ j, A i j ^ 2` in the Gaussian
regime and the Euclidean operator norm `‖A‖` in the exponential tail regime:
`P(|Q - P[Q]| > t) ≤ 2 * exp (-c * min (t ^ 2 / (K ^ 2 * ∑ i, ∑ j, A i j ^ 2)) (t / (K * ‖A‖)))`
for all `t ≥ 0`, with an explicit absolute constant `c > 0`.

Following Rudelson–Vershynin (2013), the proof splits `A = diagonal A.diag + (A - diagonal A.diag)`:
* **Diagonal part:** `∑ i, A i i * (X i ^ 2 - P[X i ^ 2])` is a sum of independent centred squares
  of sub-Gaussian variables; each summand is sub-exponential by
  `ProbabilityTheory.HasSubgaussianMGF.mgf_sq_sub_integral_le`, and `|A i i| ≤ ‖A‖`.
* **Off-diagonal part:** convex decoupling
  (`ProbabilityTheory.iIndepFun.mgf_offDiag_dotProduct_mulVec_le`) reduces the coupled chaos MGF at
  `2 * θ` to the decoupled bilinear MGF `(X ⬝ᵥ B *ᵥ X')` at `8 * θ` for `B = A - diagonal A.diag`.
  Conditioning on `X`, dominating the `X'`-MGF by a Gaussian integral, conditioning on the Gaussian
  vector, and bounding the standard Gaussian quadratic form via
  `TauCeti.Probability.mgf_inner_toEuclideanLin_stdGaussian` and
  `Real.one_sub_rpow_neg_half_le_exp` yields a sub-exponential MGF bound controlled by `‖B‖_F²` and
  `‖B‖ ≤ 2 * ‖A‖`.

The same Gaussianization Lemma (`TauCeti.integral_exp_half_mul_sum_mulVec_sq_le`), combined with the
`2n × 2n` realification (`Matrix.realify`, `Matrix.l2_opNorm_realify`, `Matrix.sum_sq_realify`) and
complex off-diagonal decoupling
(`ProbabilityTheory.iIndepFun.mgf_offDiag_re_star_dotProduct_mulVec_le`),
yields the **complex Hanson–Wright inequality** for independent directionally `K`-sub-Gaussian
complex coordinates `(Zᵢ)` — and in particular for bounded or unit-modulus circular (Steinhaus)
coordinates. We also establish **conditional Hanson–Wright bounds** for a random matrix `A`
independent of `X`, and verify sharpness of the exponent structure by showing that the Rademacher
witness `A = E₁₂ + E₂₁` forces `c ≤ 2 * Real.log 2` for every valid Hanson–Wright constant `c`.

## Main results

* `TauCeti.integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le`: exponential moment bound for
  `∑ i, ((M *ᵥ g) i) ^ 2` under standard Gaussian product measure.
* `TauCeti.integral_exp_half_mul_sum_mulVec_sq_le`: exponential moment bound for `‖M *ᵥ V‖₂²` of a
  random vector `V` with sub-Gaussian linear forms.
* `iIndepFun.integral_dotProduct_mulVec_eq_sum_diag` and
  `iIndepFun.mgf_dotProduct_mulVec_sub_integral_le`: expectation and centred MGF bound for real
  sub-Gaussian quadratic forms.
* `iIndepFun.measureReal_dotProduct_mulVec_sub_integral_gt_le` and
  `iIndepFun.measureReal_abs_dotProduct_mulVec_sub_integral_gt_le`: one-sided and two-sided real
  Hanson–Wright inequalities with explicit constant `1 / 3200`.
* `TauCeti.hanson_wright` and `TauCeti.le_two_mul_log_two_of_hanson_wright`: the existential
  Hanson–Wright theorem on `Fin n` and the Rademacher upper bound `c ≤ 2 * Real.log 2` on `c`.
* `iIndepFun.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral` and
  `iIndepFun.measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound`: conditional
  Hanson–Wright inequalities for a random matrix independent of the coordinate vector.
* `iIndepFun.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le`,
  `iIndepFun.measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le`, and
  `iIndepFun.measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le_of_norm_le`: complex
  Hanson–Wright inequalities for directionally sub-Gaussian and bounded/circular coordinates.

## References

* D. L. Hanson, F. T. Wright, *A bound on tail probabilities for quadratic forms in independent
  random variables*, Ann. Math. Statist. **42** (1971), 1079–1083.
* M. Rudelson, R. Vershynin, *Hanson–Wright inequality and sub-gaussian concentration*,
  Electron. Commun. Probab. **18** (2013), no. 82, 1–9.
* R. Vershynin, *High-Dimensional Probability*, Cambridge University Press (2018), Theorem 6.2.1.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal NNReal Matrix Matrix.Norms.L2Operator RealInnerProductSpace

namespace TauCeti

/-! ### Exponential moments of norms of Gaussian and sub-Gaussian matrix-vector products -/

section GaussianNormSq

/-- For any real matrix `M : Matrix ι κ ℝ` and `0 ≤ s` satisfying `2 * s * ‖M‖ ^ 2 ≤ 1 / 2`, the
exponential `exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)` is integrable under the standard Gaussian product
measure on `κ → ℝ` and its integral is at most `exp (2 * s * ∑ i, ∑ j, M i j ^ 2)`. -/
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
  have hquad : ∀ g : κ → ℝ,
      ⟪WithLp.toLp 2 g, Θ.toEuclideanLin (WithLp.toLp 2 g)⟫ = ∑ i, ((M *ᵥ g) i) ^ 2 := by
    intro g
    simp only [Θ, hM_conj, Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ j, ((Mᵀ * M) *ᵥ g) j * g j
        = ((Mᵀ * M) *ᵥ g) ⬝ᵥ g := rfl
      _ = g ⬝ᵥ ((Mᵀ * M) *ᵥ g) := dotProduct_comm _ _
      _ = g ⬝ᵥ (Mᵀ *ᵥ (M *ᵥ g)) := by rw [Matrix.mulVec_mulVec]
      _ = (M *ᵥ g) ⬝ᵥ (M *ᵥ g) := by rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]
      _ = ∑ i, ((M *ᵥ g) i) ^ 2 := by simp [dotProduct, sq]
  have hΘ_norm : ‖Θ‖ = ‖M‖ ^ 2 := by
    rw [sq, ← Matrix.l2_opNorm_conjTranspose_mul_self M]
  have heig_nonneg : ∀ j, 0 ≤ hΘ.eigenvalues j := fun j ↦ hΘ_psd.eigenvalues_nonneg j
  have heig_le : ∀ j, hΘ.eigenvalues j ≤ ‖M‖ ^ 2 := by
    intro j
    let e : EuclideanSpace ℝ κ := hΘ.eigenvectorBasis j
    have he_norm : ‖e‖ = 1 := hΘ.eigenvectorBasis.orthonormal.1 j
    have heig : hΘ.eigenvalues j = ⟪e, (Matrix.toEuclideanCLM (𝕜 := ℝ) Θ) e⟫ := by
      rw [hΘ.eigenvalues_eq j]
      simp only [e, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, RCLike.re_to_real,
        dotProduct, Pi.star_apply, star_trivial]
      exact Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
    calc hΘ.eigenvalues j = ⟪e, (Matrix.toEuclideanCLM (𝕜 := ℝ) Θ) e⟫ := heig
      _ ≤ ‖e‖ * ‖(Matrix.toEuclideanCLM (𝕜 := ℝ) Θ) e‖ := real_inner_le_norm _ _
      _ ≤ ‖e‖ * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) Θ‖ * ‖e‖) :=
          mul_le_mul_of_nonneg_left ((Matrix.toEuclideanCLM (𝕜 := ℝ) Θ).le_opNorm e) (norm_nonneg e)
      _ = ‖Θ‖ := by rw [he_norm, Matrix.l2_opNorm_toEuclideanCLM]; ring
      _ = ‖M‖ ^ 2 := hΘ_norm
  have h2s_eig : ∀ j, 2 * s * hΘ.eigenvalues j ≤ 1 / 2 := fun j ↦
    (mul_le_mul_of_nonneg_left (heig_le j) (by positivity)).trans hs_bound
  have h2s_lt : ∀ j, 2 * s * hΘ.eigenvalues j < 1 := fun j ↦ by linarith [h2s_eig j]
  have hint_std : Integrable (fun x : EuclideanSpace ℝ κ ↦ exp (s * ⟪x, Θ.toEuclideanLin x⟫))
      (stdGaussian (EuclideanSpace ℝ κ)) :=
    (Probability.mem_integrableExpSet_inner_toEuclideanLin_stdGaussian_iff hΘ s).2 h2s_lt
  have htoLp_meas : Measurable (WithLp.toLp 2 : (κ → ℝ) → EuclideanSpace ℝ κ) := by fun_prop
  have hint_map : Integrable (fun x : EuclideanSpace ℝ κ ↦ exp (s * ⟪x, Θ.toEuclideanLin x⟫))
      (ν.map (WithLp.toLp 2)) := by
    rwa [map_pi_eq_stdGaussian]
  have hint_pi : Integrable (fun g : κ → ℝ ↦ exp (s * ∑ i, ((M *ᵥ g) i) ^ 2)) ν := by
    have hcomp := (integrable_map_measure hint_map.aestronglyMeasurable htoLp_meas.aemeasurable).mp
      hint_map
    exact hcomp.congr (Filter.Eventually.of_forall fun g ↦ by
      dsimp only [Function.comp_def]
      rw [hquad g])
  have htrace : ∑ j, hΘ.eigenvalues j = ∑ i, ∑ j, M i j ^ 2 := by
    have htr1 : Θ.trace = ∑ j, hΘ.eigenvalues j := by
      simpa using hΘ.trace_eq_sum_eigenvalues
    have htr2 : Θ.trace = ∑ i, ∑ j, M i j ^ 2 := by
      simp only [Θ, hM_conj, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
        Matrix.transpose_apply, sq]
      exact Finset.sum_comm
    linarith
  refine ⟨hint_pi, ?_⟩
  calc ∫ g : κ → ℝ, exp (s * ∑ i, ((M *ᵥ g) i) ^ 2) ∂ν
      = ∫ g : κ → ℝ, exp (s * ⟪WithLp.toLp 2 g, Θ.toEuclideanLin (WithLp.toLp 2 g)⟫) ∂ν :=
          integral_congr_ae (Filter.Eventually.of_forall fun g ↦ by dsimp only; rw [hquad g])
    _ = mgf (fun x : EuclideanSpace ℝ κ ↦ ⟪x, Θ.toEuclideanLin x⟫)
          (stdGaussian (EuclideanSpace ℝ κ)) s := by
          rw [← map_pi_eq_stdGaussian, mgf_map htoLp_meas.aemeasurable
            hint_map.aestronglyMeasurable, mgf]
          rfl
    _ = ∏ j, (1 - 2 * s * hΘ.eigenvalues j) ^ (-1 / 2 : ℝ) :=
          Probability.mgf_inner_toEuclideanLin_stdGaussian hΘ h2s_lt
    _ ≤ ∏ j, exp (2 * s * hΘ.eigenvalues j) := by
          refine Finset.prod_le_prod₀ (fun j _ ↦ ?_) (fun j _ ↦ ?_)
          · exact Real.rpow_nonneg (by linarith [h2s_lt j]) _
          · exact Real.one_sub_rpow_neg_half_le_exp
              (mul_nonneg (by positivity) (heig_nonneg j)) (h2s_eig j)
    _ = exp (∑ j, 2 * s * hΘ.eigenvalues j) := (Real.exp_sum _ _).symm
    _ = exp (2 * s * ∑ i, ∑ j, M i j ^ 2) := by
          rw [← Finset.mul_sum, htrace]

/-- Under the standard Gaussian product measure on `γ → ℝ`, the exponential moment of `r * (y ⬝ᵥ g)`
equals `exp (r ^ 2 / 2 * ∑ l, y l ^ 2)` for every deterministic vector `y : γ → ℝ` and `r : ℝ`. -/
private lemma integral_exp_mul_dotProduct_pi_gaussianReal {γ : Type*} [Fintype γ]
    (r : ℝ) (y : γ → ℝ) :
    Integrable (fun g : γ → ℝ ↦ exp (r * (y ⬝ᵥ g)))
        (Measure.pi fun _ : γ ↦ gaussianReal 0 1) ∧
      ∫ g : γ → ℝ, exp (r * (y ⬝ᵥ g)) ∂(Measure.pi fun _ : γ ↦ gaussianReal 0 1) =
        exp (r ^ 2 / 2 * ∑ l, y l ^ 2) := by
  let ν : Measure (γ → ℝ) := Measure.pi fun _ : γ ↦ gaussianReal 0 1
  have hrewrite : ∀ g : γ → ℝ, r * (y ⬝ᵥ g) = 1 * ∑ l, (r * y l) * g l := by
    intro g
    simp only [dotProduct, one_mul, Finset.mul_sum, mul_assoc]
  have hmgf : mgf (fun g : γ → ℝ ↦ ∑ l, (r * y l) * g l) ν 1 =
      exp (r ^ 2 / 2 * ∑ l, y l ^ 2) := by
    rw [TauCeti.mgf_sum_pi (fun l u ↦ (r * y l) * u) 1]
    have hcoord : ∀ l : γ, mgf (fun u : ℝ ↦ (r * y l) * u) (gaussianReal 0 1) 1 =
        exp (r ^ 2 / 2 * y l ^ 2) := by
      intro l
      rw [mgf_const_mul, mgf_fun_id_gaussianReal]
      dsimp only; congr 1
      simp only [NNReal.coe_one]; ring
    simp_rw [hcoord, ← Real.exp_sum, ← Finset.mul_sum]
  have hint_sum : Integrable (fun g : γ → ℝ ↦ exp (1 * ∑ l, (r * y l) * g l)) ν := by
    rw [← mgf_pos_iff, hmgf]
    exact exp_pos _
  refine ⟨hint_sum.congr
    (Filter.Eventually.of_forall fun g ↦ by dsimp only; rw [← hrewrite g]), ?_⟩
  calc ∫ g : γ → ℝ, exp (r * (y ⬝ᵥ g)) ∂ν
      = mgf (fun g : γ → ℝ ↦ ∑ l, (r * y l) * g l) ν 1 :=
          integral_congr_ae (Filter.Eventually.of_forall fun g ↦ by dsimp only; rw [hrewrite g])
    _ = exp (r ^ 2 / 2 * ∑ l, y l ^ 2) := hmgf

/-- **Gaussianization bound for Euclidean norms of sub-Gaussian linear images** (Vershynin 2018,
Lemma 6.2.3). Let `V : Ω → κ → ℝ` be a random vector whose coordinates are a.e.-measurable and
whose linear forms `ω ↦ V ω ⬝ᵥ w` satisfy the sub-Gaussian MGF bound with parameter `K : ℝ≥0`. For
every matrix `M : Matrix γ κ ℝ` and `0 ≤ a` with `(K : ℝ) * a * ‖M‖ ^ 2 ≤ 1 / 2`, the exponential
`exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2)` is integrable and has expectation at most
`exp ((K : ℝ) * a * ∑ l, ∑ q, M l q ^ 2)`. -/
theorem integral_exp_half_mul_sum_mulVec_sq_le {Ω γ κ : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] [Fintype γ] [Fintype κ] [DecidableEq κ]
    {V : Ω → κ → ℝ} (hV_meas : ∀ q, AEMeasurable (fun ω ↦ V ω q) P)
    {K : ℝ≥0}
    (hV_subG : ∀ (w : κ → ℝ) (r : ℝ),
      Integrable (fun ω ↦ exp (r * (V ω ⬝ᵥ w))) P ∧
        ∫ ω, exp (r * (V ω ⬝ᵥ w)) ∂P ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2))
    (M : Matrix γ κ ℝ) {a : ℝ} (ha_nonneg : 0 ≤ a)
    (ha_bound : (K : ℝ) * a * ‖M‖ ^ 2 ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2)) P ∧
      ∫ ω, exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) ∂P ≤
        exp ((K : ℝ) * a * ∑ l, ∑ q, M l q ^ 2) := by
  let : DecidableEq γ := Classical.decEq γ
  let ν : Measure (γ → ℝ) := Measure.pi fun _ : γ ↦ gaussianReal 0 1
  let r : ℝ := Real.sqrt a
  have hr_sq : r ^ 2 = a := Real.sq_sqrt ha_nonneg
  let F : Ω × (γ → ℝ) → ℝ := fun p ↦ exp (r * ((M *ᵥ V p.1) ⬝ᵥ p.2))
  have hV_vec : AEMeasurable V P := AEMeasurable.of_eval hV_meas
  have hF_meas : AEStronglyMeasurable F (P.prod ν) := by
    have hcont : Continuous (fun q : (κ → ℝ) × (γ → ℝ) ↦ exp (r * ((M *ᵥ q.1) ⬝ᵥ q.2))) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact hcont.measurable.comp_aemeasurable
      ((hV_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        measurable_snd.aemeasurable) |>.aestronglyMeasurable
  have hF_adj : ∀ ω (g : γ → ℝ), (M *ᵥ V ω) ⬝ᵥ g = V ω ⬝ᵥ (Mᵀ *ᵥ g) := by
    intro ω g
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have hMT_norm : ‖Mᵀ‖ = ‖M‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial M, Matrix.l2_opNorm_conjTranspose]
  have hs_nonneg : 0 ≤ (K : ℝ) * a / 2 := by positivity
  have hs_bound : 2 * ((K : ℝ) * a / 2) * ‖Mᵀ‖ ^ 2 ≤ 1 / 2 := by
    rw [hMT_norm]
    linarith
  obtain ⟨hg_int, hg_le⟩ :=
    integral_exp_mul_sum_mulVec_sq_pi_gaussianReal_le Mᵀ hs_nonneg hs_bound
  have hslice_P : ∀ g : γ → ℝ, Integrable (fun ω ↦ F (ω, g)) P ∧
      ∫ ω, F (ω, g) ∂P ≤ exp (((K : ℝ) * a / 2) * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) := by
    intro g
    obtain ⟨hint, hle⟩ := hV_subG (Mᵀ *ᵥ g) r
    refine ⟨hint.congr (Filter.Eventually.of_forall fun ω ↦ by dsimp [F]; rw [hF_adj]), ?_⟩
    calc ∫ ω, F (ω, g) ∂P
        = ∫ ω, exp (r * (V ω ⬝ᵥ (Mᵀ *ᵥ g))) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by dsimp [F]; rw [hF_adj])
      _ ≤ exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) := hle
      _ = exp (((K : ℝ) * a / 2) * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) := by rw [hr_sq]
  have hF_prod_int : Integrable F (P.prod ν) := by
    rw [integrable_prod_iff' hF_meas]
    refine ⟨Filter.Eventually.of_forall fun g ↦ (hslice_P g).1, ?_⟩
    refine hg_int.mono' hF_meas.prod_swap.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun g ↦ ?_)
    have hnorm_eq : ∫ ω, ‖F (ω, g)‖ ∂P = ∫ ω, F (ω, g) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ Real.norm_of_nonneg (exp_pos _).le)
    rw [Real.norm_of_nonneg (integral_nonneg fun ω ↦ norm_nonneg _), hnorm_eq]
    exact (hslice_P g).2
  have hgauss_id : ∀ ω, ∫ g : γ → ℝ, F (ω, g) ∂ν = exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) := by
    intro ω
    rw [(integral_exp_mul_dotProduct_pi_gaussianReal r (M *ᵥ V ω)).2, hr_sq]
  have hint_lhs : Integrable (fun ω ↦ exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2)) P := by
    have hnorm := hF_prod_int.integral_norm_prod_left
    refine hnorm.congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    calc ∫ g : γ → ℝ, ‖F (ω, g)‖ ∂ν
        = ∫ g : γ → ℝ, F (ω, g) ∂ν :=
            integral_congr_ae (Filter.Eventually.of_forall fun g ↦
              Real.norm_of_nonneg (exp_pos _).le)
      _ = exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) := hgauss_id ω
  refine ⟨hint_lhs, ?_⟩
  calc ∫ ω, exp (a / 2 * ∑ l, ((M *ᵥ V ω) l) ^ 2) ∂P
      = ∫ ω, (∫ g : γ → ℝ, F (ω, g) ∂ν) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ (hgauss_id ω).symm)
    _ = ∫ g : γ → ℝ, (∫ ω, F (ω, g) ∂P) ∂ν :=
          integral_integral_swap (f := fun ω g ↦ F (ω, g)) hF_prod_int
    _ ≤ ∫ g : γ → ℝ, exp (((K : ℝ) * a / 2) * ∑ q, ((Mᵀ *ᵥ g) q) ^ 2) ∂ν :=
          integral_mono_ae hF_prod_int.integral_prod_right hg_int
            (Filter.Eventually.of_forall fun g ↦ (hslice_P g).2)
    _ ≤ exp (2 * ((K : ℝ) * a / 2) * ∑ q, ∑ l, (Mᵀ) q l ^ 2) := hg_le
    _ = exp ((K : ℝ) * a * ∑ l, ∑ q, M l q ^ 2) := by
          congr 1
          rw [Finset.sum_comm]
          simp only [Matrix.transpose_apply]
          ring

end GaussianNormSq

end TauCeti

/-! ### Real and complex Hanson–Wright inequalities on `ProbabilityTheory.iIndepFun` -/

namespace ProbabilityTheory.iIndepFun

section RealHansonWright

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- For independent real random variables `(Xᵢ)` with sub-Gaussian variance proxy `K`, the
quadratic form `Xᵀ A X` is integrable and has expectation `∑ i, A i i * P[X i ^ 2]`. -/
theorem integral_dotProduct_mulVec_eq_sum_diag {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P) (A : Matrix ι ι ℝ) :
    Integrable (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω)) P ∧
      ∫ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) ∂P =
        ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hexpand : ∀ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) =
      ∑ i, ∑ j, A i j * (X i ω * X j ω) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hterm_int : ∀ i j, Integrable (fun ω ↦ A i j * (X i ω * X j ω)) P := by
    intro i j
    by_cases hij : i = j
    · subst hij
      simpa only [sq] using (((hX i).memLp 2).integrable_sq).const_mul (A i i)
    · exact ((hindep.indepFun hij).integrable_smul (hX i).integrable (hX j).integrable).const_mul
        (A i j)
  have hint : Integrable (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω)) P := by
    refine (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j).congr ?_
    exact Filter.Eventually.of_forall fun ω ↦ (hexpand ω).symm
  refine ⟨hint, ?_⟩
  calc ∫ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) ∂P
      = ∫ ω, ∑ i, ∑ j, A i j * (X i ω * X j ω) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i, ∑ j, ∫ ω, A i j * (X i ω * X j ω) ∂P := by
          rw [integral_finsetSum Finset.univ fun i _ ↦
            integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j]
          exact Finset.sum_congr rfl fun i _ ↦
            integral_finsetSum Finset.univ fun j _ ↦ hterm_int i j
    _ = ∑ i, A i i * ∫ ω, X i ω ^ 2 ∂P := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_eq_single i]
          · simp_rw [← sq, integral_const_mul]
          · intro j _ hji
            rw [integral_const_mul,
              (hindep.indepFun hji.symm).integral_fun_mul_eq_mul_integral
                (hX i).aestronglyMeasurable (hX j).aestronglyMeasurable,
              (hX i).integral_eq_zero, zero_mul, mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi

/-- Linear forms in independent `K`-sub-Gaussian coordinates have variance proxy `‖w‖₂² * K`. -/
private lemma subgaussian_dotProduct_of_iIndepFun {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P) (w : ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * ((fun i ↦ X i ω) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * ((fun i ↦ X i ω) ⬝ᵥ w)) ∂P ≤
        exp ((K : ℝ) * r ^ 2 / 2 * ∑ i, w i ^ 2) := by
  have hindep_w : iIndepFun (fun i ω ↦ w i * X i ω) P :=
    hindep.comp (fun i x ↦ w i * x) fun i ↦ measurable_const_mul (w i)
  have hsum : HasSubgaussianMGF (fun ω ↦ ∑ i : ι, w i * X i ω)
      (∑ i : ι, ‖w i‖₊ ^ 2 * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun hindep_w fun i _ ↦ (hX i).const_mul_nnnorm (w i)
  have hdot : ∀ ω, (fun i ↦ X i ω) ⬝ᵥ w = ∑ i, w i * X i ω := fun ω ↦ by
    simp only [dotProduct, mul_comm]
  refine ⟨(hsum.integrable_exp_mul r).congr
    (Filter.Eventually.of_forall fun ω ↦ by dsimp only; rw [hdot ω]), ?_⟩
  calc ∫ ω, exp (r * ((fun i ↦ X i ω) ⬝ᵥ w)) ∂P
      = mgf (fun ω ↦ ∑ i, w i * X i ω) P r :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by dsimp only; rw [hdot ω])
    _ ≤ exp ((↑(∑ i : ι, ‖w i‖₊ ^ 2 * K) : ℝ) * r ^ 2 / 2) := hsum.mgf_le r
    _ = exp ((K : ℝ) * r ^ 2 / 2 * ∑ i, w i ^ 2) := by
          congr 1
          push_cast
          simp only [Real.norm_eq_abs, sq_abs, ← Finset.sum_mul]
          ring

variable [DecidableEq ι]

/-- **Decoupled bilinear MGF bound (real case).** For independent `K`-sub-Gaussian coordinates `X`
and any real matrix `B`, if `(K : ℝ) * |u| * ‖B‖ ≤ 1 / 2` then the decoupled bilinear form
`p ↦ X(p.1) ⬝ᵥ B *ᵥ X(p.2)` has integrable exponential moment at `u` under `P.prod P` and its MGF is
bounded by `exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, B i j ^ 2)`. -/
theorem mgf_decoupled_dotProduct_mulVec_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (B : Matrix ι ι ℝ) {u : ℝ} (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) u ≤
      exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, B i j ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let G : Ω × Ω → ℝ := fun p ↦ exp (u * ((fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)))
  have hX_vec : AEMeasurable (fun ω i ↦ X i ω) P :=
    AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable
  have hG_meas : AEStronglyMeasurable G (P.prod P) := by
    have hcont : Continuous (fun q : (ι → ℝ) × (ι → ℝ) ↦ exp (u * (q.1 ⬝ᵥ B *ᵥ q.2))) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact hcont.measurable.comp_aemeasurable
      ((hX_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        (hX_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
      |>.aestronglyMeasurable
  have hadj : ∀ x y : ι → ℝ, x ⬝ᵥ B *ᵥ y = y ⬝ᵥ (Bᵀ *ᵥ x) := by
    intro x y
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  have hBT_norm : ‖Bᵀ‖ = ‖B‖ := by
    rw [← Matrix.conjTranspose_eq_transpose_of_trivial B, Matrix.l2_opNorm_conjTranspose]
  have ha_nonneg : 0 ≤ (K : ℝ) * u ^ 2 := by positivity
  have ha_bound : (K : ℝ) * ((K : ℝ) * u ^ 2) * ‖Bᵀ‖ ^ 2 ≤ 1 / 2 := by
    rw [hBT_norm]
    have hsq : ((K : ℝ) * |u| * ‖B‖) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hu 2
    rw [← sq_abs u]
    nlinarith
  obtain ⟨hX1_int, hX1_le⟩ := TauCeti.integral_exp_half_mul_sum_mulVec_sq_le
    (fun i ↦ (hX i).aemeasurable) (hindep.subgaussian_dotProduct_of_iIndepFun hX)
    Bᵀ ha_nonneg ha_bound
  have hslice : ∀ ω₁, Integrable (fun ω₂ ↦ G (ω₁, ω₂)) P ∧
      ∫ ω₂, G (ω₁, ω₂) ∂P ≤
        exp (((K : ℝ) * u ^ 2) / 2 * ∑ j, ((Bᵀ *ᵥ fun i ↦ X i ω₁) j) ^ 2) := by
    intro ω₁
    obtain ⟨hint, hle⟩ := hindep.subgaussian_dotProduct_of_iIndepFun hX (Bᵀ *ᵥ fun i ↦ X i ω₁) u
    refine ⟨hint.congr (Filter.Eventually.of_forall fun ω₂ ↦ by dsimp [G]; rw [hadj]), ?_⟩
    calc ∫ ω₂, G (ω₁, ω₂) ∂P
        = ∫ ω₂, exp (u * ((fun i ↦ X i ω₂) ⬝ᵥ (Bᵀ *ᵥ fun i ↦ X i ω₁))) ∂P :=
            integral_congr_ae (Filter.Eventually.of_forall fun ω₂ ↦ by dsimp [G]; rw [hadj])
      _ ≤ exp ((K : ℝ) * u ^ 2 / 2 * ∑ j, ((Bᵀ *ᵥ fun i ↦ X i ω₁) j) ^ 2) := hle
  have hG_int : Integrable G (P.prod P) := by
    rw [integrable_prod_iff hG_meas]
    refine ⟨Filter.Eventually.of_forall fun ω₁ ↦ (hslice ω₁).1, ?_⟩
    refine hX1_int.mono' hG_meas.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun ω₁ ↦ ?_)
    have hnorm_eq : ∫ ω₂, ‖G (ω₁, ω₂)‖ ∂P = ∫ ω₂, G (ω₁, ω₂) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω₂ ↦ Real.norm_of_nonneg (exp_pos _).le)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hnorm_eq]
    exact (hslice ω₁).2
  refine ⟨hG_int, ?_⟩
  calc mgf (fun p : Ω × Ω ↦ (fun i ↦ X i p.1) ⬝ᵥ B *ᵥ (fun i ↦ X i p.2)) (P.prod P) u
      = ∫ ω₁, (∫ ω₂, G (ω₁, ω₂) ∂P) ∂P := integral_prod G hG_int
    _ ≤ ∫ ω₁, exp (((K : ℝ) * u ^ 2) / 2 * ∑ j, ((Bᵀ *ᵥ fun i ↦ X i ω₁) j) ^ 2) ∂P :=
          integral_mono_ae hG_int.integral_prod_left hX1_int
            (Filter.Eventually.of_forall fun ω₁ ↦ (hslice ω₁).2)
    _ ≤ exp ((K : ℝ) * ((K : ℝ) * u ^ 2) * ∑ j, ∑ i, (Bᵀ) j i ^ 2) := hX1_le
    _ = exp ((K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, B i j ^ 2) := by
          congr 1
          rw [Finset.sum_comm]
          simp only [Matrix.transpose_apply]
          ring

/-- **Sub-exponential MGF bound for centred sub-Gaussian quadratic forms.** For independent
`K`-sub-Gaussian real coordinates `X`, every real square matrix `A`, and every `θ` satisfying
`32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1`, the centred quadratic form `Xᵀ A X - P[Xᵀ A X]` has finite
exponential moment at `θ` and MGF at most `exp (800 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, A i j ^ 2)`.
-/
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
  have hB_diag : ∀ i, B i i = 0 := fun i ↦ by simp [B]
  have hB_op : ‖B‖ ≤ 2 * ‖A‖ := A.l2_opNorm_sub_diagonal_diag_le
  have hpyth : (∑ i, A i i ^ 2) + ∑ i, ∑ j, B i j ^ 2 = ∑ i, ∑ j, A i j ^ 2 := by
    have hrow : ∀ i, A i i ^ 2 + ∑ j, B i j ^ 2 = ∑ j, A i j ^ 2 := by
      intro i
      have hpt : ∀ j, (if i = j then A i i ^ 2 else 0) + B i j ^ 2 = A i j ^ 2 := by
        intro j
        by_cases hij : i = j
        · subst hij; simp [B]
        · simp [B, hij]
      have hite : ∑ j : ι, (if i = j then A i i ^ 2 else 0) = A i i ^ 2 := by simp
      rw [← hite, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ hpt j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hrow i
  have hdiag_frob : ∑ i, A i i ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
    have hB_nn : 0 ≤ ∑ i, ∑ j, B i j ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  have hB_frob : ∑ i, ∑ j, B i j ^ 2 ≤ ∑ i, ∑ j, A i j ^ 2 := by
    have hA_nn : 0 ≤ ∑ i, A i i ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  -- Off-diagonal coupled MGF at `2 * θ`
  have hu_off : (K : ℝ) * |4 * (2 * θ)| * ‖B‖ ≤ 1 / 2 := by
    have h8 : |4 * (2 * θ)| = 8 * |θ| := by
      rw [show (4 : ℝ) * (2 * θ) = 8 * θ by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    rw [h8]
    calc (K : ℝ) * (8 * |θ|) * ‖B‖
        ≤ (K : ℝ) * (8 * |θ|) * (2 * ‖A‖) :=
          mul_le_mul_of_nonneg_left hB_op (by positivity)
      _ = (1 / 2) * (32 * ((K : ℝ) * ‖A‖) * |θ|) := by ring
      _ ≤ 1 / 2 := by linarith
  obtain ⟨hdec_int, hdec_mgf⟩ := hindep.mgf_decoupled_dotProduct_mulVec_le hX B hu_off
  obtain ⟨hoff_int, hoff_mgf⟩ := hindep.mgf_offDiag_dotProduct_mulVec_le
    (fun i ↦ (hX i).integrable) (fun i ↦ (hX i).integral_eq_zero) hB_diag (t := 2 * θ) hdec_int
  have hoff_bound : mgf (fun ω ↦ (fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) P (2 * θ) ≤
      exp (64 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) * θ ^ 2) := by
    refine (hoff_mgf.trans hdec_mgf).trans ?_
    apply exp_le_exp.2
    have h1 : (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, B i j ^ 2 =
        64 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, B i j ^ 2 := by ring
    rw [h1]
    have h2 : 64 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, B i j ^ 2 ≤
        64 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, A i j ^ 2 :=
      mul_le_mul_of_nonneg_left hB_frob (by positivity)
    linarith
  -- Diagonal centred MGF at `2 * θ`
  let D : ι → Ω → ℝ := fun i ω ↦ A i i * (X i ω ^ 2 - P[fun ω' ↦ X i ω' ^ 2])
  have hD_indep : iIndepFun D P := by
    refine hindep.comp (fun i x ↦ A i i * (x ^ 2 - P[fun ω' ↦ X i ω' ^ 2])) fun i ↦ ?_
    fun_prop
  have hD_meas : ∀ i, AEMeasurable (D i) P := fun i ↦ by
    have hsq : AEMeasurable (fun ω ↦ X i ω ^ 2) P := (measurable_id.pow_const 2).comp_aemeasurable
      (hX i).aemeasurable
    exact (hsq.sub_const _).const_mul (A i i)
  have hD_term : ∀ i, Integrable (fun ω ↦ exp ((2 * θ) * D i ω)) P ∧
      mgf (D i) P (2 * θ) ≤ exp (1536 * (K : ℝ) ^ 2 * θ ^ 2 * A i i ^ 2) := by
    intro i
    have hAii : |A i i| ≤ ‖A‖ := by simpa using A.norm_entry_le_l2_opNorm i i
    have hθi : (K : ℝ) * |(2 * θ) * A i i| ≤ 1 / 8 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc (K : ℝ) * (2 * |θ| * |A i i|)
          ≤ (K : ℝ) * (2 * |θ| * ‖A‖) := by gcongr
        _ = (1 / 16) * (32 * ((K : ℝ) * ‖A‖) * |θ|) := by ring
        _ ≤ 1 / 8 := by linarith
    obtain ⟨hint_i, hmgf_i⟩ := (hX i).mgf_sq_sub_integral_le hθi
    refine ⟨hint_i.congr (Filter.Eventually.of_forall fun ω ↦ by dsimp [D]; ring_nf), ?_⟩
    calc mgf (D i) P (2 * θ)
        = mgf (fun ω ↦ X i ω ^ 2 - P[fun ω' ↦ X i ω' ^ 2]) P (A i i * (2 * θ)) :=
            mgf_const_mul (A i i)
      _ = mgf (fun ω ↦ X i ω ^ 2 - P[fun ω' ↦ X i ω' ^ 2]) P ((2 * θ) * A i i) := by
            rw [mul_comm (A i i)]
      _ ≤ exp (384 * (K : ℝ) ^ 2 * ((2 * θ) * A i i) ^ 2) := hmgf_i
      _ = exp (1536 * (K : ℝ) ^ 2 * θ ^ 2 * A i i ^ 2) := by congr 1; ring
  have hD_mgf_eq : mgf (∑ i : ι, D i) P (2 * θ) = ∏ i : ι, mgf (D i) P (2 * θ) :=
    hD_indep.mgf_sum₀ hD_meas Finset.univ
  have hD_sum_int : Integrable (fun ω ↦ exp ((2 * θ) * ∑ i, D i ω)) P := by
    have hpos : 0 < mgf (∑ i : ι, D i) P (2 * θ) := by
      rw [hD_mgf_eq]
      exact Finset.prod_pos fun i _ ↦ mgf_pos (hD_term i).1
    exact (mgf_pos_iff.mp hpos).congr (Filter.Eventually.of_forall fun ω ↦ by simp)
  have hD_bound : mgf (fun ω ↦ ∑ i, D i ω) P (2 * θ) ≤
      exp (1536 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) * θ ^ 2) := by
    have hsum_fn : (fun ω ↦ ∑ i, D i ω) = ∑ i : ι, D i := by ext ω; simp
    rw [hsum_fn, hD_mgf_eq]
    calc ∏ i : ι, mgf (D i) P (2 * θ)
        ≤ ∏ i : ι, exp (1536 * (K : ℝ) ^ 2 * θ ^ 2 * A i i ^ 2) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) fun i _ ↦ (hD_term i).2
      _ = exp (∑ i : ι, 1536 * (K : ℝ) ^ 2 * θ ^ 2 * A i i ^ 2) := (Real.exp_sum _ _).symm
      _ ≤ exp (1536 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2) * θ ^ 2) := by
          apply exp_le_exp.2
          rw [← Finset.mul_sum]
          have hle := mul_le_mul_of_nonneg_left hdiag_frob
            (by positivity : 0 ≤ 1536 * (K : ℝ) ^ 2 * θ ^ 2)
          linarith
  -- Decomposition `Xᵀ A X - P[Xᵀ A X] = (∑ i, D i) + Xᵀ B X`
  have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P =
      ∑ i, A i i * P[fun ω' ↦ X i ω' ^ 2] :=
    (hindep.integral_dotProduct_mulVec_eq_sum_diag hX A).2
  have hsplit : ∀ ω, (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P =
        (∑ i, D i ω) + ((fun i ↦ X i ω) ⬝ᵥ B *ᵥ (fun i ↦ X i ω)) := by
    intro ω
    rw [hmean]
    have hAB : A = Matrix.diagonal A.diag + B := by simp [B]
    nth_rw 1 [hAB]
    rw [Matrix.add_mulVec, dotProduct_add]
    have hdiag_quad : (fun i ↦ X i ω) ⬝ᵥ Matrix.diagonal A.diag *ᵥ (fun i ↦ X i ω) =
        ∑ i, A i i * X i ω ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diag_apply]
      exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hdiag_quad]
    simp only [D, mul_sub, Finset.sum_sub_distrib]
    ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  refine ⟨hint, hle.trans_eq ?_⟩
  congr 1; ring

/-- **One-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013) with explicit constant
`1 / 3200`. -/
theorem measureReal_dotProduct_mulVec_sub_integral_gt_le {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (A : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < (fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P} ≤
      exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hF : 0 ≤ (K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hop : 0 ≤ (K : ℝ) * ‖A‖ := mul_nonneg K.coe_nonneg (norm_nonneg A)
  have hconst : min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 := by norm_num
  rw [← hconst]
  exact ProbabilityTheory.measureReal_gt_le_exp_min_of_mgf_le (by norm_num) (by norm_num) hF hop
    (fun θ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

/-- **Two-sided Hanson–Wright inequality** (Rudelson–Vershynin 2013, Theorem 1.1) for an arbitrary
finite index type `ι`, with explicit constant `1 / 3200`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_integral_gt_le {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    (A : Matrix ι ι ℝ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
        ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hF : 0 ≤ (K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hop : 0 ≤ (K : ℝ) * ‖A‖ := mul_nonneg K.coe_nonneg (norm_nonneg A)
  have hconst : min (1 / (4 * (800 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 3200 := by norm_num
  rw [← hconst]
  exact ProbabilityTheory.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le
    (by norm_num) (by norm_num) hF hop
    (fun θ hθ ↦ hindep.mgf_dotProduct_mulVec_sub_integral_le hX A hθ) ht

/-! ### Conditional Hanson–Wright inequalities for an independent random matrix -/

/-- **Integrated conditional Hanson–Wright inequality.** Let `A : Ω → Matrix ι ι ℝ` be an
a.e.-measurable random matrix independent of the random vector `ω ↦ (X i ω)_{i : ι}` of independent
`K`-sub-Gaussian coordinates. Then the deviation of `X(ω)ᵀ A(ω) X(ω)` from its conditional mean
`∑ i, A(ω) i i * P[X i ^ 2]` exceeds `t ≥ 0` with probability at most the expectation over `A` of
the clipped deterministic Hanson–Wright bound. -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_integral
    {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P)
    (hAX : IndepFun A (fun ω i ↦ X i ω) P) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
      ∫ ω, min 1 (2 * exp (-(1 / 3200) *
        min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A ω i j ^ 2))
          (t / ((K : ℝ) * ‖A ω‖)))) ∂P := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let hX_vec : AEMeasurable (fun ω i ↦ X i ω) P :=
    AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable
  let μA : Measure (Matrix ι ι ℝ) := P.map A
  let μX : Measure (ι → ℝ) := P.map (fun ω i ↦ X i ω)
  have : IsProbabilityMeasure μA := by dsimp [μA]; infer_instance
  have : IsProbabilityMeasure μX := by dsimp [μX]; infer_instance
  let E : Set (Matrix ι ι ℝ × (ι → ℝ)) :=
    {p | t < |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|}
  have hE_meas : MeasurableSet E := by
    have hcont : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) ↦
        |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact isOpen_lt continuous_const hcont |>.measurableSet
  let φ : Matrix ι ι ℝ → ℝ := fun M ↦ min 1 (2 * exp (-(1 / 3200) *
    min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2)) (t / ((K : ℝ) * ‖M‖))))
  have hφ_meas : Measurable φ := by
    have h1 : Measurable (fun M : Matrix ι ι ℝ ↦ ∑ i, ∑ j, M i j ^ 2) :=
      Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
        (Matrix.measurable_apply (i := i) (j := j)).pow_const 2
    have h2 : Measurable (fun M : Matrix ι ι ℝ ↦ ‖M‖) := continuous_norm.measurable
    fun_prop
  have hφ_int_μA : Integrable φ μA := by
    refine Integrable.of_mem_Icc 0 1 hφ_meas.aemeasurable (Filter.Eventually.of_forall fun M ↦ ?_)
    exact ⟨le_min zero_le_one (by positivity), min_le_left _ _⟩
  have hslice_le : ∀ M : Matrix ι ι ℝ, μX.real (Prod.mk M ⁻¹' E) ≤ φ M := by
    intro M
    have hpre_meas : MeasurableSet (Prod.mk M ⁻¹' E) := hE_meas.preimage measurable_prodMk_left
    rw [map_measureReal_apply_of_aemeasurable hX_vec hpre_meas]
    refine le_min ((measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ) ?_
    have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ M *ᵥ (fun i ↦ X i ω') ∂P =
        ∑ i, M i i * P[fun ω' ↦ X i ω' ^ 2] :=
      (hindep.integral_dotProduct_mulVec_eq_sum_diag hX M).2
    simpa only [E, Set.preimage_ofPred_eq, hmean] using
      hindep.measureReal_abs_dotProduct_mulVec_sub_integral_gt_le hX M ht
  have hind_int : Integrable (E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ)) (μA.prod μX) :=
    (integrable_const (1 : ℝ)).indicator hE_meas
  have hslice_eq : ∀ M, ∫ x, E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x) ∂μX =
      μX.real (Prod.mk M ⁻¹' E) := by
    intro M
    have hind_eq : (fun x ↦ E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x)) =
        (Prod.mk M ⁻¹' E).indicator 1 := by
      ext x
      by_cases hx : (M, x) ∈ E <;> simp [hx]
    rw [hind_eq, integral_indicator_one (hE_meas.preimage measurable_prodMk_left)]
  have hprod_eq : P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = (μA.prod μX).real E := by
    rw [← hAX.map_prod_eq_prod_map_map hA_meas hX_vec,
      map_measureReal_apply_of_aemeasurable (hA_meas.prodMk hX_vec) hE_meas]
    rfl
  rw [hprod_eq, ← integral_indicator_one hE_meas, integral_prod _ hind_int]
  calc ∫ M, (∫ x, E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x) ∂μX) ∂μA
      = ∫ M, μX.real (Prod.mk M ⁻¹' E) ∂μA :=
          integral_congr_ae (Filter.Eventually.of_forall hslice_eq)
    _ ≤ ∫ M, φ M ∂μA :=
          integral_mono_ae
            (hind_int.integral_prod_left.congr (Filter.Eventually.of_forall hslice_eq))
            hφ_int_μA (Filter.Eventually.of_forall hslice_le)
    _ = ∫ ω, φ (A ω) ∂P := integral_map hA_meas hφ_meas.aestronglyMeasurable

/-- **Conditional Hanson–Wright inequality under a.s. norm bounds.** If `A : Ω → Matrix ι ι ℝ` is
independent of `X` and satisfies `∑ i, ∑ j, A ω i j ^ 2 ≤ F` and `‖A ω‖ ≤ op` almost surely, then
`X(ω)ᵀ A(ω) X(ω)` concentrates around `∑ i, A(ω) i i * P[X i ^ 2]` with parameters `F` and `op`. -/
theorem measureReal_abs_dotProduct_mulVec_sub_sum_diag_gt_le_of_ae_bound
    {X : ι → Ω → ℝ} (hindep : iIndepFun X P)
    {K : ℝ≥0} (hX : ∀ i, HasSubgaussianMGF (X i) K P)
    {A : Ω → Matrix ι ι ℝ} (hA_meas : AEMeasurable A P)
    (hAX : IndepFun A (fun ω i ↦ X i ω) P)
    {F op : ℝ} (hA_frob : ∀ᵐ ω ∂P, ∑ i, ∑ j, A ω i j ^ 2 ≤ F)
    (hA_op : ∀ᵐ ω ∂P, ‖A ω‖ ≤ op) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} ≤
      2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  -- Handle `K = 0` directly: every `X i =ᵐ[P] 0`, so the deviation vanishes a.s.
  rcases eq_or_ne K 0 with rfl | hK_ne
  · have hX_zero : ∀ᵐ ω ∂P, ∀ i, X i ω = 0 :=
      ae_all_iff.2 fun i ↦ (hX i).ae_eq_zero_of_hasSubgaussianMGF_zero
    have hmean_zero : ∀ i, P[fun ω' ↦ X i ω' ^ 2] = 0 := by
      intro i
      refine integral_eq_zero_of_ae ?_
      filter_upwards [(hX i).ae_eq_zero_of_hasSubgaussianMGF_zero] with ω hω
      simp only [Pi.zero_apply] at hω
      simp [hω]
    have hnull : P {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = 0 := by
      refine measure_mono_null (fun ω (hω : t < _) ↦ ?_) (ae_iff.1 hX_zero)
      intro hzero
      have hvec0 : (fun i ↦ X i ω) = 0 := funext hzero
      rw [hvec0, Matrix.mulVec_zero, dotProduct_zero] at hω
      simp only [hmean_zero, mul_zero, Finset.sum_const_zero, sub_zero, abs_zero] at hω
      linarith
    have hreal0 : P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
        ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = 0 := by
      simp [Measure.real, hnull]
    rw [hreal0]
    positivity
  have hK_pos : 0 < (K : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hK_ne)
  -- Repeat the product-measure slice estimate, noting that at `M = 0` the slice is empty.
  let hX_vec : AEMeasurable (fun ω i ↦ X i ω) P :=
    AEMeasurable.of_eval fun i ↦ (hX i).aemeasurable
  let μA : Measure (Matrix ι ι ℝ) := P.map A
  let μX : Measure (ι → ℝ) := P.map (fun ω i ↦ X i ω)
  have : IsProbabilityMeasure μA := by dsimp [μA]; infer_instance
  have : IsProbabilityMeasure μX := by dsimp [μX]; infer_instance
  let E : Set (Matrix ι ι ℝ × (ι → ℝ)) :=
    {p | t < |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|}
  have hE_meas : MeasurableSet E := by
    have hcont : Continuous (fun p : Matrix ι ι ℝ × (ι → ℝ) ↦
        |p.2 ⬝ᵥ p.1 *ᵥ p.2 - ∑ i, p.1 i i * P[fun ω' ↦ X i ω' ^ 2]|) := by
      simp only [dotProduct, Matrix.mulVec]
      fun_prop
    exact isOpen_lt continuous_const hcont |>.measurableSet
  let Bnd : ℝ := 2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op)))
  have hBnd_nonneg : 0 ≤ Bnd := by positivity
  have hae_μA : ∀ᵐ M ∂μA, (∑ i, ∑ j, M i j ^ 2 ≤ F) ∧ ‖M‖ ≤ op := by
    have hS_meas : MeasurableSet {M : Matrix ι ι ℝ | (∑ i, ∑ j, M i j ^ 2 ≤ F) ∧ ‖M‖ ≤ op} := by
      have h1 : Measurable (fun M : Matrix ι ι ℝ ↦ ∑ i, ∑ j, M i j ^ 2) :=
        Finset.measurable_sum _ fun i _ ↦ Finset.measurable_sum _ fun j _ ↦
          (Matrix.measurable_apply (i := i) (j := j)).pow_const 2
      exact (measurableSet_le h1 measurable_const).inter
        (measurableSet_le continuous_norm.measurable measurable_const)
    rw [ae_map_iff hA_meas hS_meas]
    exact hA_frob.and hA_op
  have hslice_ae : ∀ᵐ M ∂μA, μX.real (Prod.mk M ⁻¹' E) ≤ Bnd := by
    filter_upwards [hae_μA] with M ⟨hMf, hMop⟩
    by_cases hM0 : M = 0
    · subst hM0
      have hemp : Prod.mk (0 : Matrix ι ι ℝ) ⁻¹' E = ∅ := by
        ext x
        simp only [E, Set.mem_preimage, Set.mem_ofPred_eq, Matrix.zero_mulVec, dotProduct_zero,
          Matrix.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, abs_zero,
          Set.mem_empty_iff_false, iff_false, not_lt]
        exact ht
      rw [hemp, measureReal_empty]
      exact hBnd_nonneg
    · obtain ⟨i₀, j₀, hij₀⟩ : ∃ i j, M i j ≠ 0 := by
        by_contra! h
        exact hM0 (Matrix.ext h)
      have hMf_pos : 0 < ∑ i, ∑ j, M i j ^ 2 := by
        have h1 : 0 < M i₀ j₀ ^ 2 := sq_pos_of_ne_zero hij₀
        have h2 : M i₀ j₀ ^ 2 ≤ ∑ j, M i₀ j ^ 2 :=
          Finset.single_le_sum (fun j _ ↦ sq_nonneg (M i₀ j)) (Finset.mem_univ j₀)
        have h3 : ∑ j, M i₀ j ^ 2 ≤ ∑ i, ∑ j, M i j ^ 2 :=
          Finset.single_le_sum (fun i _ ↦ Finset.sum_nonneg fun j _ ↦ sq_nonneg _)
            (Finset.mem_univ i₀)
        linarith
      have hMop_pos : 0 < ‖M‖ := norm_pos_iff.2 hM0
      have hpre_meas : MeasurableSet (Prod.mk M ⁻¹' E) := hE_meas.preimage measurable_prodMk_left
      rw [map_measureReal_apply_of_aemeasurable hX_vec hpre_meas]
      have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ M *ᵥ (fun i ↦ X i ω') ∂P =
          ∑ i, M i i * P[fun ω' ↦ X i ω' ^ 2] :=
        (hindep.integral_dotProduct_mulVec_eq_sum_diag hX M).2
      have hdet := hindep.measureReal_abs_dotProduct_mulVec_sub_integral_gt_le hX M ht
      have hdet' : P.real ((fun ω i ↦ X i ω) ⁻¹' (Prod.mk M ⁻¹' E)) ≤
          2 * exp (-(1 / 3200) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2))
            (t / ((K : ℝ) * ‖M‖))) := by
        simpa only [E, Set.preimage_preimage, Set.preimage_ofPred_eq, hmean] using hdet
      refine hdet'.trans ?_
      have hmin_le : min (t ^ 2 / ((K : ℝ) ^ 2 * F)) (t / ((K : ℝ) * op)) ≤
          min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, M i j ^ 2)) (t / ((K : ℝ) * ‖M‖)) := by
        refine min_le_min ?_ ?_
        · exact div_le_div_of_nonneg_left (sq_nonneg t) (by positivity)
            (mul_le_mul_of_nonneg_left hMf (sq_nonneg _))
        · exact div_le_div_of_nonneg_left ht (by positivity)
            (mul_le_mul_of_nonneg_left hMop hK_pos.le)
      dsimp only [Bnd]
      exact mul_le_mul_of_nonneg_left (exp_le_exp.2 (by linarith)) zero_le_two
  have hind_int : Integrable (E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ)) (μA.prod μX) :=
    (integrable_const (1 : ℝ)).indicator hE_meas
  have hslice_eq : ∀ M, ∫ x, E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x) ∂μX =
      μX.real (Prod.mk M ⁻¹' E) := by
    intro M
    have hind_eq : (fun x ↦ E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x)) =
        (Prod.mk M ⁻¹' E).indicator 1 := by
      ext x
      by_cases hx : (M, x) ∈ E <;> simp [hx]
    rw [hind_eq, integral_indicator_one (hE_meas.preimage measurable_prodMk_left)]
  have hprod_eq : P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A ω *ᵥ (fun i ↦ X i ω) -
      ∑ i, A ω i i * P[fun ω' ↦ X i ω' ^ 2]|} = (μA.prod μX).real E := by
    rw [← hAX.map_prod_eq_prod_map_map hA_meas hX_vec,
      map_measureReal_apply_of_aemeasurable (hA_meas.prodMk hX_vec) hE_meas]
    rfl
  rw [hprod_eq, ← integral_indicator_one hE_meas, integral_prod _ hind_int]
  calc ∫ M, (∫ x, E.indicator (1 : Matrix ι ι ℝ × (ι → ℝ) → ℝ) (M, x) ∂μX) ∂μA
      = ∫ M, μX.real (Prod.mk M ⁻¹' E) ∂μA :=
          integral_congr_ae (Filter.Eventually.of_forall hslice_eq)
    _ ≤ ∫ _, Bnd ∂μA :=
          integral_mono_ae
            (hind_int.integral_prod_left.congr (Filter.Eventually.of_forall hslice_eq))
            (integrable_const Bnd) hslice_ae
    _ = Bnd := by simp [probReal_univ]

end RealHansonWright

/-! ### Complex Hanson–Wright inequality for directionally sub-Gaussian and circular vectors -/

section ComplexHansonWright

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {P : Measure Ω}

/-- Expectation of a complex sesquilinear form `star Z ⬝ᵥ A *ᵥ Z` of independent directionally
sub-Gaussian complex coordinates. -/
theorem integral_star_dotProduct_mulVec_eq_sum_diag {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) :
    Integrable (fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)) P ∧
      ∫ ω, star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) ∂P =
        ∑ i, A i i * ((P[fun ω ↦ ‖Z i ω‖ ^ 2] : ℝ) : ℂ) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hZ_int : ∀ i, Integrable (Z i) P := fun i ↦
    integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)
  have hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0 := fun i ↦
    integral_eq_zero_of_hasSubgaussianMGF_re_star_mul (hZ i)
  have hZ_star_int : ∀ i, Integrable (fun ω ↦ star (Z i ω)) P := fun i ↦
    (hZ_int i).mono (continuous_star.comp_aestronglyMeasurable (hZ_int i).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω ↦ by simp)
  have hZ_norm_sq_int : ∀ i, Integrable (fun ω ↦ ‖Z i ω‖ ^ 2) P := by
    intro i
    have hre := ((hasSubgaussianMGF_re_of_star_mul (hZ i)).memLp 2).integrable_sq
    have him := ((hasSubgaussianMGF_im_of_star_mul (hZ i)).memLp 2).integrable_sq
    refine (hre.add him).congr (Filter.Eventually.of_forall fun ω ↦ ?_)
    dsimp only [Pi.add_apply]
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hexpand : ∀ ω, star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) =
      ∑ i, ∑ j, A i j * (star (Z i ω) * Z j ω) := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
  have hcast : ∀ i ω, A i i * (star (Z i ω) * Z i ω) = A i i * ((‖Z i ω‖ ^ 2 : ℝ) : ℂ) := by
    intro i ω; rw [Complex.star_def, Complex.conj_mul']; norm_cast
  have hterm_int : ∀ i j, Integrable (fun ω ↦ A i j * (star (Z i ω) * Z j ω)) P := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact ((hZ_norm_sq_int i).ofReal.const_mul (A i i)).congr
        (Filter.Eventually.of_forall fun ω ↦ by dsimp only; exact (hcast i ω).symm)
    · have hind_ij : IndepFun (fun ω ↦ star (Z i ω)) (Z j) P :=
        (hindep.indepFun hij).comp continuous_star.measurable measurable_id
      exact (hind_ij.integrable_smul (hZ_star_int i) (hZ_int j)).const_mul (A i j)
  have hint : Integrable (fun ω ↦ star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)) P :=
    (integrable_finsetSum Finset.univ fun i _ ↦
      integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j).congr
      (Filter.Eventually.of_forall fun ω ↦ (hexpand ω).symm)
  refine ⟨hint, ?_⟩
  calc ∫ ω, star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω) ∂P
      = ∫ ω, ∑ i, ∑ j, A i j * (star (Z i ω) * Z j ω) ∂P :=
          integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = ∑ i, ∑ j, ∫ ω, A i j * (star (Z i ω) * Z j ω) ∂P := by
          rw [integral_finsetSum Finset.univ fun i _ ↦
            integrable_finsetSum Finset.univ fun j _ ↦ hterm_int i j]
          exact Finset.sum_congr rfl fun i _ ↦
            integral_finsetSum Finset.univ fun j _ ↦ hterm_int i j
    _ = ∑ i, A i i * ((P[fun ω ↦ ‖Z i ω‖ ^ 2] : ℝ) : ℂ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          rw [Finset.sum_eq_single i]
          · calc ∫ ω, A i i * (star (Z i ω) * Z i ω) ∂P
                = ∫ ω, A i i * ((‖Z i ω‖ ^ 2 : ℝ) : ℂ) ∂P :=
                    integral_congr_ae (Filter.Eventually.of_forall (hcast i))
              _ = A i i * ∫ ω, ((‖Z i ω‖ ^ 2 : ℝ) : ℂ) ∂P := integral_const_mul _ _
              _ = A i i * ((P[fun ω ↦ ‖Z i ω‖ ^ 2] : ℝ) : ℂ) :=
                    congrArg (A i i * ·) integral_ofReal
          · intro j _ hji
            have hind_ij : IndepFun (fun ω ↦ star (Z i ω)) (Z j) P :=
              (hindep.indepFun hji.symm).comp continuous_star.measurable measurable_id
            rw [integral_const_mul,
              hind_ij.integral_fun_mul_eq_mul_integral (hZ_star_int i).aestronglyMeasurable
                (hZ_int j).aestronglyMeasurable,
              hZ_mean j, mul_zero, mul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi

/-- Realified linear forms of independent directionally `K`-sub-Gaussian complex coordinates have
variance proxy `‖w‖₂² * K`. -/
private lemma subgaussian_realify_dotProduct_of_iIndepFun {Z : ι → Ω → ℂ}
    (hindep : iIndepFun Z P) {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (w : ι ⊕ ι → ℝ) (r : ℝ) :
    Integrable (fun ω ↦ exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w))) P ∧
      ∫ ω, exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)) ∂P ≤
        exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2) := by
  let u : ι → ℂ := fun i ↦ ⟨w (.inl i), w (.inr i)⟩
  let W : ι → Ω → ℝ := fun i ω ↦ (star (u i) * Z i ω).re
  have hW_indep : iIndepFun W P :=
    hindep.comp (fun i z ↦ (star (u i) * z).re) fun i ↦ by fun_prop
  have hW_subG : HasSubgaussianMGF (fun ω ↦ ∑ i : ι, W i ω) (∑ i : ι, ‖u i‖₊ ^ 2 * K) P :=
    HasSubgaussianMGF.sum_of_iIndepFun hW_indep fun i _ ↦ hZ i (u i)
  have hdot : ∀ ω, Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w = ∑ i, W i ω := by
    intro ω
    simp only [dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      ← Finset.sum_add_distrib, W, u, Complex.mul_re, Complex.star_def, Complex.conj_re,
      Complex.conj_im]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnorm_sum : ∑ i : ι, ‖u i‖ ^ 2 = ∑ q : ι ⊕ ι, w q ^ 2 := by
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [u, sq]
  refine ⟨(hW_subG.integrable_exp_mul r).congr
    (Filter.Eventually.of_forall fun ω ↦ by dsimp only; rw [hdot ω]), ?_⟩
  calc ∫ ω, exp (r * (Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im) ⬝ᵥ w)) ∂P
      = mgf (fun ω ↦ ∑ i, W i ω) P r :=
          integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by dsimp only; rw [hdot ω])
    _ ≤ exp ((↑(∑ i : ι, ‖u i‖₊ ^ 2 * K) : ℝ) * r ^ 2 / 2) := hW_subG.mgf_le r
    _ = exp ((K : ℝ) * r ^ 2 / 2 * ∑ q, w q ^ 2) := by
          congr 1
          push_cast
          rw [← Finset.sum_mul, hnorm_sum]
          ring

variable [DecidableEq ι]

/-- **Decoupled sesquilinear MGF bound (complex case).** For independent directionally
`K`-sub-Gaussian complex coordinates `Z` and any `B : Matrix ι ι ℂ`, if
`(K : ℝ) * |u| * ‖B‖ ≤ 1 / 2` then `(star (Z p.1) ⬝ᵥ B *ᵥ (Z p.2)).re` has finite exponential
moment at `u` under `P.prod P` and MGF at most
`exp (2 * (K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2)`. -/
theorem mgf_decoupled_re_star_dotProduct_mulVec_le {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (B : Matrix ι ι ℂ) {u : ℝ} (hu : (K : ℝ) * |u| * ‖B‖ ≤ 1 / 2) :
    Integrable (fun p : Ω × Ω ↦
      exp (u * (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re)) (P.prod P) ∧
    mgf (fun p : Ω × Ω ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re) (P.prod P) u ≤
      exp (2 * (K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  let G : Ω × Ω → ℝ :=
    fun p ↦ exp (u * (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re)
  have hZ_meas : ∀ i, AEMeasurable (Z i) P := fun i ↦
    (integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)).aemeasurable
  have hZ_vec : AEMeasurable (fun ω i ↦ Z i ω) P := AEMeasurable.of_eval hZ_meas
  have hG_meas : AEStronglyMeasurable G (P.prod P) := by
    have hcont : Continuous (fun q : (ι → ℂ) × (ι → ℂ) ↦ exp (u * (star q.1 ⬝ᵥ B *ᵥ q.2).re)) := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
      fun_prop
    exact hcont.measurable.comp_aemeasurable
      ((hZ_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst).prodMk
        (hZ_vec.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd))
      |>.aestronglyMeasurable
  let V : Ω → ι ⊕ ι → ℝ := fun ω ↦ Sum.elim (fun i ↦ (Z i ω).re) (fun i ↦ (Z i ω).im)
  have hV_meas : ∀ q, AEMeasurable (fun ω ↦ V ω q) P := by
    rintro (i | i)
    · exact Complex.continuous_re.measurable.comp_aemeasurable (hZ_meas i)
    · exact Complex.continuous_im.measurable.comp_aemeasurable (hZ_meas i)
  have hadj : ∀ z w : ι → ℂ,
      (star z ⬝ᵥ B *ᵥ w).re = ∑ j, (star ((Bᴴ *ᵥ z) j) * w j).re := by
    intro z w
    have h1 : star z ⬝ᵥ B *ᵥ w = ∑ j, star ((Bᴴ *ᵥ z) j) * w j := by
      simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Matrix.conjTranspose_apply,
        Finset.mul_sum, Finset.sum_mul, star_sum, star_mul', star_star]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun i _ ↦ by ring
    rw [h1, Complex.re_sum]
  have hrealify_norm : ∀ ω₁, ∑ j, ‖(Bᴴ *ᵥ fun i ↦ Z i ω₁) j‖ ^ 2 =
      ∑ q : ι ⊕ ι, (((Bᴴ).realify *ᵥ V ω₁) q) ^ 2 := by
    intro ω₁
    rw [Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    have hinl : ((Bᴴ).realify *ᵥ V ω₁) (.inl j) = ((Bᴴ *ᵥ fun i ↦ Z i ω₁) j).re := by
      simp only [V, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Matrix.realify_apply_inl_inl, Matrix.realify_apply_inl_inr, RCLike.re_eq_complex_re,
        RCLike.im_eq_complex_im, neg_mul, Finset.sum_neg_distrib, Complex.re_sum,
        Complex.mul_re, Finset.sum_sub_distrib]
      ring
    have hinr : ((Bᴴ).realify *ᵥ V ω₁) (.inr j) = ((Bᴴ *ᵥ fun i ↦ Z i ω₁) j).im := by
      simp only [V, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
        Matrix.realify_apply_inr_inl, Matrix.realify_apply_inr_inr, RCLike.re_eq_complex_re,
        RCLike.im_eq_complex_im, Complex.im_sum, Complex.mul_im, Finset.sum_add_distrib]
      ring
    rw [hinl, hinr, Complex.sq_norm, Complex.normSq_apply]
    ring
  have hM_norm : ‖(Bᴴ).realify‖ = ‖B‖ := by
    rw [Matrix.l2_opNorm_realify, Matrix.l2_opNorm_conjTranspose]
  have ha_nonneg : 0 ≤ (K : ℝ) * u ^ 2 := by positivity
  have ha_bound : (K : ℝ) * ((K : ℝ) * u ^ 2) * ‖(Bᴴ).realify‖ ^ 2 ≤ 1 / 2 := by
    rw [hM_norm]
    have hsq : ((K : ℝ) * |u| * ‖B‖) ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hu 2
    rw [← sq_abs u]
    nlinarith
  obtain ⟨hX1_int, hX1_le⟩ := TauCeti.integral_exp_half_mul_sum_mulVec_sq_le
    hV_meas (hindep.subgaussian_realify_dotProduct_of_iIndepFun hZ)
    (Bᴴ).realify ha_nonneg ha_bound
  have hslice : ∀ ω₁, Integrable (fun ω₂ ↦ G (ω₁, ω₂)) P ∧
      ∫ ω₂, G (ω₁, ω₂) ∂P ≤
        exp (((K : ℝ) * u ^ 2) / 2 * ∑ q, (((Bᴴ).realify *ᵥ V ω₁) q) ^ 2) := by
    intro ω₁
    let v : ι → ℂ := Bᴴ *ᵥ fun i ↦ Z i ω₁
    let U : ι → Ω → ℝ := fun j ω₂ ↦ (star (v j) * Z j ω₂).re
    have hU_indep : iIndepFun U P :=
      hindep.comp (fun j z ↦ (star (v j) * z).re) fun j ↦ by fun_prop
    have hU_subG : HasSubgaussianMGF (fun ω₂ ↦ ∑ j : ι, U j ω₂) (∑ j : ι, ‖v j‖₊ ^ 2 * K) P :=
      HasSubgaussianMGF.sum_of_iIndepFun hU_indep fun j _ ↦ hZ j (v j)
    refine ⟨(hU_subG.integrable_exp_mul u).congr
      (Filter.Eventually.of_forall fun ω₂ ↦ by dsimp only [G, U, v]; rw [hadj]), ?_⟩
    calc ∫ ω₂, G (ω₁, ω₂) ∂P
        = mgf (fun ω₂ ↦ ∑ j : ι, U j ω₂) P u := by
            rw [mgf]
            exact integral_congr_ae
              (Filter.Eventually.of_forall fun ω₂ ↦ by dsimp only [G, U, v]; rw [hadj])
      _ ≤ exp ((↑(∑ j : ι, ‖v j‖₊ ^ 2 * K) : ℝ) * u ^ 2 / 2) := hU_subG.mgf_le u
      _ = exp (((K : ℝ) * u ^ 2) / 2 * ∑ q, (((Bᴴ).realify *ᵥ V ω₁) q) ^ 2) := by
            congr 1
            push_cast
            rw [← Finset.sum_mul, hrealify_norm ω₁]
            ring
  have hG_int : Integrable G (P.prod P) := by
    rw [integrable_prod_iff hG_meas]
    refine ⟨Filter.Eventually.of_forall fun ω₁ ↦ (hslice ω₁).1, ?_⟩
    refine hX1_int.mono' hG_meas.norm.integral_prod_right'
      (Filter.Eventually.of_forall fun ω₁ ↦ ?_)
    have hnorm_eq : ∫ ω₂, ‖G (ω₁, ω₂)‖ ∂P = ∫ ω₂, G (ω₁, ω₂) ∂P :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω₂ ↦ Real.norm_of_nonneg (exp_pos _).le)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ ↦ norm_nonneg _), hnorm_eq]
    exact (hslice ω₁).2
  refine ⟨hG_int, ?_⟩
  calc mgf (fun p : Ω × Ω ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re) (P.prod P) u
      = ∫ ω₁, (∫ ω₂, G (ω₁, ω₂) ∂P) ∂P := integral_prod G hG_int
    _ ≤ ∫ ω₁, exp (((K : ℝ) * u ^ 2) / 2 * ∑ q, (((Bᴴ).realify *ᵥ V ω₁) q) ^ 2) ∂P :=
          integral_mono_ae hG_int.integral_prod_left hX1_int
            (Filter.Eventually.of_forall fun ω₁ ↦ (hslice ω₁).2)
    _ ≤ exp ((K : ℝ) * ((K : ℝ) * u ^ 2) * ∑ p, ∑ q, (Bᴴ).realify p q ^ 2) := hX1_le
    _ = exp (2 * (K : ℝ) ^ 2 * u ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2) := by
          congr 1
          rw [Matrix.sum_sq_realify, Finset.sum_comm]
          simp only [Matrix.conjTranspose_apply, norm_star]
          ring

/-- **Centred MGF bound for the real part of a complex sub-Gaussian sesquilinear form.** For
`32 * ((K : ℝ) * ‖A‖) * |θ| ≤ 1`, `(star Z ⬝ᵥ A *ᵥ Z).re - P[(star Z ⬝ᵥ A *ᵥ Z).re]` has MGF at `θ`
bounded by `exp (3136 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2)`. -/
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
  have hB_diag : ∀ i, B i i = 0 := fun i ↦ by simp [B]
  have hB_op : ‖B‖ ≤ 2 * ‖A‖ := A.l2_opNorm_sub_diagonal_diag_le
  have hpyth : (∑ i, ‖A i i‖ ^ 2) + ∑ i, ∑ j, ‖B i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    have hrow : ∀ i, ‖A i i‖ ^ 2 + ∑ j, ‖B i j‖ ^ 2 = ∑ j, ‖A i j‖ ^ 2 := by
      intro i
      have hpt : ∀ j, (if i = j then ‖A i i‖ ^ 2 else 0) + ‖B i j‖ ^ 2 = ‖A i j‖ ^ 2 := by
        intro j
        by_cases hij : i = j
        · subst hij; simp [B]
        · simp [B, hij]
      have hite : ∑ j : ι, (if i = j then ‖A i i‖ ^ 2 else 0) = ‖A i i‖ ^ 2 := by simp
      rw [← hite, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ ↦ hpt j
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ ↦ hrow i
  have hdiag_frob : ∑ i, ‖A i i‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    have hB_nn : 0 ≤ ∑ i, ∑ j, ‖B i j‖ ^ 2 :=
      Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  have hB_frob : ∑ i, ∑ j, ‖B i j‖ ^ 2 ≤ ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    have hA_nn : 0 ≤ ∑ i, ‖A i i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
    linarith
  -- Off-diagonal coupled MGF at `2 * θ`
  have hu_off : (K : ℝ) * |4 * (2 * θ)| * ‖B‖ ≤ 1 / 2 := by
    have h8 : |4 * (2 * θ)| = 8 * |θ| := by
      rw [show (4 : ℝ) * (2 * θ) = 8 * θ by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 8)]
    rw [h8]
    calc (K : ℝ) * (8 * |θ|) * ‖B‖
        ≤ (K : ℝ) * (8 * |θ|) * (2 * ‖A‖) :=
          mul_le_mul_of_nonneg_left hB_op (by positivity)
      _ = (1 / 2) * (32 * ((K : ℝ) * ‖A‖) * |θ|) := by ring
      _ ≤ 1 / 2 := by linarith
  obtain ⟨hdec_int, hdec_mgf⟩ := hindep.mgf_decoupled_re_star_dotProduct_mulVec_le hZ B hu_off
  have hZ_int : ∀ i, Integrable (Z i) P := fun i ↦
    integrable_of_hasSubgaussianMGF_re_star_mul (hZ i)
  have hZ_mean : ∀ i, ∫ ω, Z i ω ∂P = 0 := fun i ↦
    integral_eq_zero_of_hasSubgaussianMGF_re_star_mul (hZ i)
  obtain ⟨hoff_int, hoff_mgf⟩ := hindep.mgf_offDiag_re_star_dotProduct_mulVec_le
    hZ_int hZ_mean hB_diag (t := 2 * θ) hdec_int
  have hoff_bound : mgf (fun ω ↦ (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re) P (2 * θ) ≤
      exp (128 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2) := by
    have hoff_mgf' : mgf (fun ω ↦ (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re) P (2 * θ) ≤
        mgf (fun p : Ω × Ω ↦ (star (fun i ↦ Z i p.1) ⬝ᵥ B *ᵥ (fun i ↦ Z i p.2)).re)
          (P.prod P) (4 * (2 * θ)) := hoff_mgf
    refine (hoff_mgf'.trans hdec_mgf).trans ?_
    apply exp_le_exp.2
    have h1 : 2 * (K : ℝ) ^ 2 * (4 * (2 * θ)) ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 =
        128 * (K : ℝ) ^ 2 * θ ^ 2 * ∑ i, ∑ j, ‖B i j‖ ^ 2 := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hB_frob (by positivity : 0 ≤ 128 * (K : ℝ) ^ 2 * θ ^ 2)
    linarith
  -- Diagonal centred MGF at `2 * θ`
  let D : ι → Ω → ℝ := fun i ω ↦ (A i i).re * (‖Z i ω‖ ^ 2 - P[fun ω' ↦ ‖Z i ω'‖ ^ 2])
  have hD_indep : iIndepFun D P := by
    refine hindep.comp (fun i z ↦ (A i i).re * (‖z‖ ^ 2 - P[fun ω' ↦ ‖Z i ω'‖ ^ 2])) fun i ↦ ?_
    fun_prop
  have hD_meas : ∀ i, AEMeasurable (D i) P := fun i ↦ by
    have hsq : AEMeasurable (fun ω ↦ ‖Z i ω‖ ^ 2) P :=
      (continuous_norm.pow 2).measurable.comp_aemeasurable (hZ_int i).aemeasurable
    exact (hsq.sub_const _).const_mul (A i i).re
  have hD_term : ∀ i, Integrable (fun ω ↦ exp ((2 * θ) * D i ω)) P ∧
      mgf (D i) P (2 * θ) ≤ exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * ‖A i i‖ ^ 2) := by
    intro i
    have hAii : |(A i i).re| ≤ ‖A‖ :=
      (Complex.abs_re_le_norm _).trans (A.norm_entry_le_l2_opNorm i i)
    have hθi : (K : ℝ) * |(2 * θ) * (A i i).re| ≤ 1 / 16 := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      calc (K : ℝ) * (2 * |θ| * |(A i i).re|)
          ≤ (K : ℝ) * (2 * |θ| * ‖A‖) := by gcongr
        _ = (1 / 16) * (32 * ((K : ℝ) * ‖A‖) * |θ|) := by ring
        _ ≤ 1 / 16 := by linarith
    obtain ⟨hint_i, hmgf_i⟩ :=
      mgf_norm_sq_sub_integral_le_of_hasSubgaussianMGF_re_star_mul (hZ i) hθi
    have hre_sq : (A i i).re ^ 2 ≤ ‖A i i‖ ^ 2 :=
      sq_le_sq.2 (by rw [abs_of_nonneg (norm_nonneg _)]; exact Complex.abs_re_le_norm _)
    refine ⟨hint_i.congr (Filter.Eventually.of_forall fun ω ↦ by dsimp [D]; ring_nf), ?_⟩
    calc mgf (D i) P (2 * θ)
        = mgf (fun ω ↦ ‖Z i ω‖ ^ 2 - P[fun ω' ↦ ‖Z i ω'‖ ^ 2]) P ((A i i).re * (2 * θ)) :=
            mgf_const_mul (A i i).re
      _ = mgf (fun ω ↦ ‖Z i ω‖ ^ 2 - P[fun ω' ↦ ‖Z i ω'‖ ^ 2]) P ((2 * θ) * (A i i).re) := by
            rw [mul_comm (A i i).re]
      _ ≤ exp (1536 * (K : ℝ) ^ 2 * ((2 * θ) * (A i i).re) ^ 2) := hmgf_i
      _ = exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * (A i i).re ^ 2) := by congr 1; ring
      _ ≤ exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * ‖A i i‖ ^ 2) :=
            exp_le_exp.2 (mul_le_mul_of_nonneg_left hre_sq (by positivity))
  have hD_mgf_eq : mgf (∑ i : ι, D i) P (2 * θ) = ∏ i : ι, mgf (D i) P (2 * θ) :=
    hD_indep.mgf_sum₀ hD_meas Finset.univ
  have hD_sum_int : Integrable (fun ω ↦ exp ((2 * θ) * ∑ i, D i ω)) P := by
    have hpos : 0 < mgf (∑ i : ι, D i) P (2 * θ) := by
      rw [hD_mgf_eq]
      exact Finset.prod_pos fun i _ ↦ mgf_pos (hD_term i).1
    exact (mgf_pos_iff.mp hpos).congr (Filter.Eventually.of_forall fun ω ↦ by simp)
  have hD_bound : mgf (fun ω ↦ ∑ i, D i ω) P (2 * θ) ≤
      exp (6144 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2) := by
    have hsum_fn : (fun ω ↦ ∑ i, D i ω) = ∑ i : ι, D i := by ext ω; simp
    rw [hsum_fn, hD_mgf_eq]
    calc ∏ i : ι, mgf (D i) P (2 * θ)
        ≤ ∏ i : ι, exp (6144 * (K : ℝ) ^ 2 * θ ^ 2 * ‖A i i‖ ^ 2) :=
          Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) fun i _ ↦ (hD_term i).2
      _ = exp (∑ i : ι, 6144 * (K : ℝ) ^ 2 * θ ^ 2 * ‖A i i‖ ^ 2) := (Real.exp_sum _ _).symm
      _ ≤ exp (6144 * ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) * θ ^ 2) := by
          apply exp_le_exp.2
          rw [← Finset.mul_sum]
          have hle := mul_le_mul_of_nonneg_left hdiag_frob
            (by positivity : 0 ≤ 6144 * (K : ℝ) ^ 2 * θ ^ 2)
          linarith
  -- Decomposition of `(star Z ⬝ᵥ A *ᵥ Z).re - P[(star Z ⬝ᵥ A *ᵥ Z).re]`
  have hmul_ofReal_re : ∀ (w : ℂ) (r : ℝ), (w * (r : ℂ)).re = w.re * r := fun w r ↦ by
    simp [Complex.mul_re]
  obtain ⟨hquad_int, hquad_mean⟩ := hindep.integral_star_dotProduct_mulVec_eq_sum_diag hZ A
  have hre_mean : ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
      ∑ i, (A i i).re * P[fun ω' ↦ ‖Z i ω'‖ ^ 2] := by
    have hcomm : (∫ ω', star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω') ∂P).re =
        ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P :=
      (Complex.reCLM.integral_comp_comm hquad_int).symm
    rw [← hcomm, hquad_mean, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ ↦ hmul_ofReal_re (A i i) _
  have hsplit : ∀ ω, (star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
      ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P =
        (∑ i, D i ω) + (star (fun i ↦ Z i ω) ⬝ᵥ B *ᵥ (fun i ↦ Z i ω)).re := by
    intro ω
    rw [hre_mean]
    have hAB : A = Matrix.diagonal A.diag + B := by simp [B]
    nth_rw 1 [hAB]
    rw [Matrix.add_mulVec, dotProduct_add, Complex.add_re]
    have hdiag_quad : (star (fun i ↦ Z i ω) ⬝ᵥ Matrix.diagonal A.diag *ᵥ (fun i ↦ Z i ω)).re =
        ∑ i, (A i i).re * ‖Z i ω‖ ^ 2 := by
      simp only [dotProduct, Matrix.mulVec_diagonal, Matrix.diag_apply, Pi.star_apply,
        Complex.re_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      have hconj : star (Z i ω) * (A i i * Z i ω) = A i i * ((‖Z i ω‖ ^ 2 : ℝ) : ℂ) := by
        calc star (Z i ω) * (A i i * Z i ω)
            = A i i * (star (Z i ω) * Z i ω) := by ring
          _ = A i i * ((‖Z i ω‖ ^ 2 : ℝ) : ℂ) := by
              rw [Complex.star_def, Complex.conj_mul']; norm_cast
      exact (congrArg Complex.re hconj).trans (hmul_ofReal_re (A i i) (‖Z i ω‖ ^ 2))
    rw [hdiag_quad]
    simp only [D, mul_sub, Finset.sum_sub_distrib]
    ring
  simp_rw [hsplit]
  obtain ⟨hint, hle⟩ := mgf_add_le_exp_half_add hD_sum_int hoff_int hD_bound hoff_bound
  refine ⟨hint, hle.trans_eq ?_⟩
  congr 1; ring

/-- **Complex Hanson–Wright inequality (real part).** For independent directionally
`K`-sub-Gaussian complex coordinates `Z` and any `A : Matrix ι ι ℂ`, the real part of
`star Z ⬝ᵥ A *ᵥ Z` concentrates around its mean with constant `1 / 12544`. -/
theorem measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le {Z : ι → Ω → ℂ}
    (hindep : iIndepFun Z P) {K : ℝ≥0}
    (hZ : ∀ i (u : ℂ), HasSubgaussianMGF (fun ω ↦ (star u * Z i ω).re) (‖u‖₊ ^ 2 * K) P)
    (A : Matrix ι ι ℂ) {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |(star (fun i ↦ Z i ω) ⬝ᵥ A *ᵥ (fun i ↦ Z i ω)).re -
        ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ A *ᵥ (fun i ↦ Z i ω')).re ∂P|} ≤
      2 * exp (-(1 / 12544) * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        (t / ((K : ℝ) * ‖A‖))) := by
  have : IsProbabilityMeasure P := hindep.isProbabilityMeasure
  have hF : 0 ≤ (K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _)
  have hop : 0 ≤ (K : ℝ) * ‖A‖ := mul_nonneg K.coe_nonneg (norm_nonneg A)
  have hconst : min (1 / (4 * (3136 : ℝ))) (1 / (2 * (32 : ℝ))) = 1 / 12544 := by norm_num
  rw [← hconst]
  exact ProbabilityTheory.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le (by norm_num)
    (by norm_num) hF hop
    (fun θ hθ ↦ hindep.mgf_re_star_dotProduct_mulVec_sub_integral_le hZ A hθ) ht

/-- **Complex Hanson–Wright inequality (full complex norm).** For independent directionally
`K`-sub-Gaussian complex coordinates `Z` and *any* complex square matrix `A : Matrix ι ι ℂ` (not
necessarily Hermitian), `‖star Z ⬝ᵥ A *ᵥ Z - P[star Z ⬝ᵥ A *ᵥ Z]‖` exceeds `t ≥ 0` with probability
at most `2 * exp (-(1 / 150528) * min (t ^ 2 / (K ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2)) (t / (K * ‖A‖)))`.
-/
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
  have hre_int_eq : (∫ ω', Q ω' ∂P).re = ∫ ω', (Q ω').re ∂P :=
    (Complex.reCLM.integral_comp_comm hQ_int).symm
  have him_int_eq : (∫ ω', Q ω' ∂P).im = ∫ ω', (Q ω').im ∂P :=
    (Complex.imCLM.integral_comp_comm hQ_int).symm
  -- Identify `(Q ω).im` with `(star Z ⬝ᵥ ((-I) • A) *ᵥ Z).re`
  let AI : Matrix ι ι ℂ := (-Complex.I) • A
  have hAI_re : ∀ ω, (star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re = (Q ω).im := by
    intro ω
    have hsmul : star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω) = (-Complex.I) * Q ω := by
      simp only [AI, Q, dotProduct, Matrix.mulVec, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ by ring
    rw [hsmul]
    simp [Complex.mul_re]
  have hAI_op : ‖AI‖ = ‖A‖ := by
    rw [norm_smul, norm_neg, Complex.norm_I, one_mul]
  have hAI_frob : ∑ i, ∑ j, ‖AI i j‖ ^ 2 = ∑ i, ∑ j, ‖A i j‖ ^ 2 := by
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    simp [AI]
  -- Split `{t < ‖Q - P[Q]‖}` into real and imaginary deviations past `t / 2`
  have hsub : {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ⊆
      {ω | t / 2 < |(Q ω).re - ∫ ω', (Q ω').re ∂P|} ∪
        {ω | t / 2 < |(star (fun i ↦ Z i ω) ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω)).re -
          ∫ ω', (star (fun i ↦ Z i ω') ⬝ᵥ AI *ᵥ (fun i ↦ Z i ω')).re ∂P|} := by
    intro ω (hω : t < ‖Q ω - ∫ ω', Q ω' ∂P‖)
    simp only [Set.mem_union, Set.mem_ofPred_eq, hAI_re]
    by_contra! hboth
    obtain ⟨hb1, hb2⟩ := hboth
    have hsq1 : ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_re, hre_int_eq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb1 2
    have hsq2 : ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 ≤ (t / 2) ^ 2 := by
      rw [Complex.sub_im, him_int_eq, ← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hb2 2
    have hnorm_sq : ‖Q ω - ∫ ω', Q ω' ∂P‖ ^ 2 =
        ((Q ω - ∫ ω', Q ω' ∂P).re) ^ 2 + ((Q ω - ∫ ω', Q ω' ∂P).im) ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hlt : t ^ 2 < ‖Q ω - ∫ ω', Q ω' ∂P‖ ^ 2 :=
      pow_lt_pow_left₀ hω ht (by norm_num)
    nlinarith
  let m : ℝ := min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2)) (t / ((K : ℝ) * ‖A‖))
  have hm_nonneg : 0 ≤ m := by
    refine le_min ?_ ?_
    · exact div_nonneg (sq_nonneg t)
        (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦
          sq_nonneg _))
    · exact div_nonneg ht (mul_nonneg K.coe_nonneg (norm_nonneg A))
  have hm_half : m / 4 ≤
      min ((t / 2) ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
        ((t / 2) / ((K : ℝ) * ‖A‖)) := by
    refine le_min ?_ ?_
    · have hle : m ≤ t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) := min_le_left _ _
      have heq : (t / 2) ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2) =
          (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2)) / 4 := by ring
      linarith
    · have hle : m ≤ t / ((K : ℝ) * ‖A‖) := min_le_right _ _
      have hnn : 0 ≤ t / ((K : ℝ) * ‖A‖) :=
        div_nonneg ht (mul_nonneg K.coe_nonneg (norm_nonneg A))
      have heq : (t / 2) / ((K : ℝ) * ‖A‖) = (t / ((K : ℝ) * ‖A‖)) / 2 := by ring
      linarith
  have h1 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ A
    (by positivity : 0 ≤ t / 2)
  have h2 := hindep.measureReal_abs_re_star_dotProduct_mulVec_sub_integral_gt_le hZ AI
    (by positivity : 0 ≤ t / 2)
  rw [hAI_op, hAI_frob] at h2
  have h4 : P.real {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖} ≤ 4 * exp (-(1 / 50176) * m) := by
    have hexp_le : exp (-(1 / 12544) *
        min ((t / 2) ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, ‖A i j‖ ^ 2))
          ((t / 2) / ((K : ℝ) * ‖A‖))) ≤ exp (-(1 / 50176) * m) := by
      apply exp_le_exp.2
      linarith
    calc P.real {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖}
        ≤ P.real _ := measureReal_mono hsub
      _ ≤ P.real _ + P.real _ := measureReal_union_le _ _
      _ ≤ 2 * exp (-(1 / 50176) * m) + 2 * exp (-(1 / 50176) * m) := by
          linarith [h1, h2, hexp_le]
      _ = 4 * exp (-(1 / 50176) * m) := by ring
  -- Upgrade min 1 (4 * exp (-a)) to 2 * exp (-(a / 3)) using 4 * u ^ 3 ≤ 2 * u for u < 1 / 2
  let u : ℝ := exp (-(1 / 150528) * m)
  have hu_pos : 0 < u := exp_pos _
  have hu_cube : exp (-(1 / 50176) * m) = u ^ 3 := by
    dsimp [u]
    rw [← exp_nat_mul]
    congr 1
    ring
  by_cases hu_half : 1 / 2 ≤ u
  · calc P.real {ω | t < ‖Q ω - ∫ ω', Q ω' ∂P‖}
        ≤ 1 := (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
      _ ≤ 2 * u := by linarith
  · push Not at hu_half
    have h4u3 : 4 * u ^ 3 ≤ 2 * u := by
      have hu2 : 4 * u ^ 2 ≤ 1 := by nlinarith
      nlinarith
    rw [hu_cube] at h4
    exact h4.trans h4u3

/-- **Complex Hanson–Wright inequality for bounded mean-zero coordinates** (including unit-modulus
circular / Steinhaus coordinates when `b = 1`). -/
theorem measureReal_norm_star_dotProduct_mulVec_sub_integral_gt_le_of_norm_le
    {Z : ι → Ω → ℂ} (hindep : iIndepFun Z P)
    (hZ_meas : ∀ i, AEMeasurable (Z i) P) {b : ℝ≥0}
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

/-! ### Existential statement on `Fin n` and Rademacher sharpness -/

namespace TauCeti

/-- **Hanson–Wright inequality** (Rudelson–Vershynin 2013, Theorem 1.1). There is an absolute
constant `c > 0` such that for independent real coordinates `Xᵢ`, each sub-Gaussian with variance
proxy `K`, and every real square matrix `A`, the quadratic form `Xᵀ A X` deviates from its mean by
more than `t ≥ 0` with probability at most `2 * exp (-c * min (t ^ 2 / (K ^ 2 * ‖A‖_F²))
(t / (K * ‖A‖)))`, where `‖A‖_F² = ∑ i, ∑ j, A i j ^ 2` and `‖A‖` is the Euclidean operator norm. -/
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

/-- **Rademacher sharpness of the Hanson–Wright exponent.** Any constant `c : ℝ` satisfying the
Hanson–Wright tail bound for independent `1`-sub-Gaussian Rademacher coordinates on `Fin 2` and the
symmetric off-diagonal matrix `A = !![0, 1; 1, 0]` at `t = 1` satisfies `c ≤ 2 * Real.log 2`. -/
theorem le_two_mul_log_two_of_hanson_wright {c : ℝ}
    (hc : ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] {n : ℕ}
      (X : Fin n → Ω → ℝ) (K : ℝ≥0), iIndepFun X P → (∀ i, HasSubgaussianMGF (X i) K P) →
      ∀ (A : Matrix (Fin n) (Fin n) ℝ) (t : ℝ), 0 ≤ t →
        P.real {ω | t < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
            ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} ≤
          2 * Real.exp (-c * min (t ^ 2 / ((K : ℝ) ^ 2 * ∑ i, ∑ j, A i j ^ 2))
            (t / ((K : ℝ) * ‖A‖)))) :
    c ≤ 2 * Real.log 2 := by
  let μ₀ : Measure (ULift Bool) :=
    (2 : ℝ≥0∞)⁻¹ • (Measure.dirac (ULift.up true) + Measure.dirac (ULift.up false))
  have hμ₀_prob : IsProbabilityMeasure μ₀ := by
    refine ⟨?_⟩
    simp only [μ₀, smul_apply, FunLike.coe_add, Pi.add_apply,
      Measure.dirac_apply' _ MeasurableSet.univ, Set.indicator_univ, Pi.one_apply, smul_eq_mul,
      one_add_one_eq_two]
    exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)
  let rad : ULift Bool → ℝ := fun b ↦ if b.down then 1 else -1
  have hrad_meas : Measurable rad := measurable_of_finite rad
  have hrad_Icc : ∀ᵐ b ∂μ₀, rad b ∈ Set.Icc (-1 : ℝ) 1 :=
    Filter.Eventually.of_forall fun b ↦ by cases b with | up b => cases b <;> simp [rad]
  have hrad_mean : ∫ b, rad b ∂μ₀ = 0 := by
    rw [integral_smul_measure, integral_add_measure Integrable.of_finite Integrable.of_finite,
      integral_dirac, integral_dirac]
    simp [rad]
  have hrad_subG : HasSubgaussianMGF rad 1 μ₀ := by
    have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hrad_meas.aemeasurable
      hrad_Icc hrad_mean
    refine h.mono ?_
    rw [← NNReal.coe_le_coe]
    push_cast
    norm_num
  let P : Measure (Fin 2 → ULift Bool) := Measure.pi fun _ : Fin 2 ↦ μ₀
  let X : Fin 2 → (Fin 2 → ULift Bool) → ℝ := fun i ω ↦ rad (ω i)
  have hindep : iIndepFun X P := iIndepFun_pi fun _ ↦ hrad_meas.aemeasurable
  have hX_subG : ∀ i, HasSubgaussianMGF (X i) 1 P := by
    intro i
    have hmp : HasSubgaussianMGF rad 1 (P.map fun f ↦ f i) := by
      rw [show (fun f : Fin 2 → ULift Bool ↦ f i) = Function.eval i from rfl,
        (measurePreserving_eval (fun _ : Fin 2 ↦ μ₀) i).map_eq]
      exact hrad_subG
    exact HasSubgaussianMGF.of_map (μ := P) (measurable_pi_apply i).aemeasurable hmp
  let A : Matrix (Fin 2) (Fin 2) ℝ := Matrix.of ![![0, 1], ![1, 0]]
  have hmean : ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P = 0 := by
    rw [(hindep.integral_dotProduct_mulVec_eq_sum_diag hX_subG A).2, Fin.sum_univ_two]
    simp [A]
  have hquad_abs : ∀ ω : Fin 2 → ULift Bool,
      |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) - 0| = 2 := by
    intro ω
    simp only [dotProduct, Matrix.mulVec, Fin.sum_univ_two, A, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, X, rad]
    cases h0 : (ω 0).down <;> cases h1 : (ω 1).down <;> norm_num [h0, h1]
  have hevent : {ω | (1 : ℝ) < |(fun i ↦ X i ω) ⬝ᵥ A *ᵥ (fun i ↦ X i ω) -
      ∫ ω', (fun i ↦ X i ω') ⬝ᵥ A *ᵥ (fun i ↦ X i ω') ∂P|} = Set.univ := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true, hmean, hquad_abs ω]
    norm_num
  have hfrob : ∑ i : Fin 2, ∑ j : Fin 2, A i j ^ 2 = 2 := by
    simp [Fin.sum_univ_two, A]
    norm_num
  have hop_le : ‖A‖ ≤ 1 := by
    rw [← Matrix.l2_opNorm_toEuclideanCLM]
    refine (Matrix.toEuclideanCLM (𝕜 := ℝ) A).opNorm_le_bound zero_le_one fun v ↦ ?_
    rw [one_mul]
    refine (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp ?_
    rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
    have h0 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) v).ofLp 0 = v.ofLp 1 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]
    have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℝ) A) v).ofLp 1 = v.ofLp 0 := by
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, A]
    rw [Fin.sum_univ_two, Fin.sum_univ_two, h0, h1, add_comm]
  have hop_ge : 1 ≤ ‖A‖ := by
    simpa [A] using A.norm_entry_le_l2_opNorm 0 1
  have hop : ‖A‖ = 1 := le_antisymm hop_le hop_ge
  have hbound := hc P X 1 hindep hX_subG A 1 zero_le_one
  rw [hevent, probReal_univ, hfrob, hop] at hbound
  simp only [NNReal.coe_one, one_pow, one_mul, div_one] at hbound
  have hmin : min ((1 : ℝ) / 2) 1 = 1 / 2 := by norm_num
  rw [hmin] at hbound
  have hexp_ge : (2 : ℝ)⁻¹ ≤ Real.exp (-c * (1 / 2)) := by linarith
  have hlog := Real.log_le_log (by positivity) hexp_ge
  rw [Real.log_inv, Real.log_exp] at hlog
  linarith

end TauCeti
