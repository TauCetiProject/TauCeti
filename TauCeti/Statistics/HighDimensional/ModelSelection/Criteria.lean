/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import TauCeti.Order.SmallestArgmin
public import TauCeti.Probability.Distributions.ChiSquared.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.LiminfLimsup
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Topology.Algebra.Monoid
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.Analysis.InnerProductSpace.Projection.Nested
import TauCeti.MeasureTheory.Function.SmallestArgmin
import TauCeti.Probability.Distributions.ChiSquared.Support
import TauCeti.Probability.Distributions.Gaussian.Projection
import TauCeti.Probability.Moments.SubGaussian

/-!
# Akaike's and Schwarz's model selection criteria

We formalize the Gaussian log-likelihood `gaussLogLik`, Akaike's optimism identity (`aic_optimism`),
the linear-dimension-penalty selector `dimPenaltySelector` (breaking ties via
`TauCeti.smallestArgmin`) together with its AIC and BIC specializations (`aicSelector`,
`bicSelector`), measurability of all selectors, general-weight asymptotic overfitting and
consistency theorems (`dimPenaltySelector_overfit`, `dimPenaltySelector_overfit_pos`,
`dimPenaltySelector_consistent`), and their AIC/BIC specializations (`aic_overfit`,
`aic_overfit_pos`, `bic_consistent`) in finite-dimensional real inner product spaces.

In dimension `n = Module.finrank ℝ E` with known noise variance `σ ^ 2`,
`gaussLogLik σ g Y = -(n / 2) * log (2 * π * σ ^ 2) - ‖Y - g‖ ^ 2 / (2 * σ ^ 2)`,
and over a finite linearly ordered family of subspaces `S : ι → Submodule ℝ E`,
`dimPenaltySelector S σ c` minimizes `‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + dim (S j) * c`
(`c = 2` for `aicSelector` and `c = log n` for `bicSelector`).

## References

* H. Akaike, *Information theory and an extension of the maximum likelihood principle*,
  2nd International Symposium on Information Theory (1973), 267–281.
* G. Schwarz, *Estimating the dimension of a model*, Ann. Statist. **6** (1978), 461–464.
* C. Giraud, *Introduction to High-Dimensional Statistics*, 2nd ed., CRC Press (2022), §2.1–2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal RealInnerProductSpace

namespace TauCeti

section LogLik

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-! ### Gaussian log-likelihood and Akaike's optimism identity -/

/-- The Gaussian log-likelihood of mean `g` at observation `Y` with known variance `σ ^ 2`:
`-(Module.finrank ℝ E / 2) * Real.log (2 * Real.pi * σ ^ 2) - ‖Y - g‖ ^ 2 / (2 * σ ^ 2)`. -/
def gaussLogLik (σ : ℝ) (g Y : E) : ℝ :=
  -(Module.finrank ℝ E / 2 : ℝ) * Real.log (2 * Real.pi * σ ^ 2) -
    ‖Y - g‖ ^ 2 / (2 * σ ^ 2)

/-- Unfolding lemma for `gaussLogLik`. -/
theorem gaussLogLik_def (σ : ℝ) (g Y : E) : gaussLogLik σ g Y =
    -(Module.finrank ℝ E / 2 : ℝ) * Real.log (2 * Real.pi * σ ^ 2) - ‖Y - g‖ ^ 2 / (2 * σ ^ 2) :=
  (rfl)

/-- The Gaussian log-likelihood is invariant under negating `σ`. -/
@[simp]
theorem gaussLogLik_neg (σ : ℝ) (g Y : E) : gaussLogLik (-σ) g Y = gaussLogLik σ g Y := by
  simp [gaussLogLik_def]

/-- When `g = Y`, the residual term of `gaussLogLik` vanishes. -/
@[simp]
theorem gaussLogLik_self (σ : ℝ) (Y : E) :
    gaussLogLik σ Y Y = -(Module.finrank ℝ E / 2 : ℝ) * Real.log (2 * Real.pi * σ ^ 2) := by
  simp [gaussLogLik_def]

/-- The Gaussian log-likelihood at `Y` is maximized globally at `g = Y`. -/
theorem gaussLogLik_le_self (σ : ℝ) (g Y : E) : gaussLogLik σ g Y ≤ gaussLogLik σ Y Y := by
  rw [gaussLogLik_def, gaussLogLik_self]; exact sub_le_self _ (by positivity)

/-- The difference of Gaussian log-likelihoods at two observations `Y₁, Y₂` with the same mean `g`
equals `(‖Y₂ - g‖ ^ 2 - ‖Y₁ - g‖ ^ 2) / (2 * σ ^ 2)`. -/
theorem gaussLogLik_sub_gaussLogLik (σ : ℝ) (g Y₁ Y₂ : E) :
    gaussLogLik σ g Y₁ - gaussLogLik σ g Y₂ = (‖Y₂ - g‖ ^ 2 - ‖Y₁ - g‖ ^ 2) / (2 * σ ^ 2) := by
  simp only [gaussLogLik_def]; ring

/-- The Gaussian log-likelihood is jointly continuous in `(g, Y)`. -/
@[fun_prop]
theorem continuous_gaussLogLik (σ : ℝ) : Continuous fun p : E × E ↦ gaussLogLik σ p.1 p.2 := by
  unfold gaussLogLik; fun_prop

end LogLik

section Optimism

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Over a subspace `S` admitting orthogonal projection, the Gaussian log-likelihood at `Y` is
maximized at the orthogonal projection `S.starProjection Y`. -/
theorem gaussLogLik_le_starProjection (σ : ℝ) (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    {g : E} (hg : g ∈ S) (Y : E) :
    gaussLogLik σ g Y ≤ gaussLogLik σ (S.starProjection Y) Y := by
  rw [gaussLogLik_def, gaussLogLik_def]
  exact sub_le_sub_left (div_le_div_of_nonneg_right
    (pow_le_pow_left₀ (norm_nonneg _) (S.norm_sub_starProjection_le_of_mem Y hg) 2)
    (by positivity)) _

/-- Pointwise orthogonal split of the in-sample minus out-of-sample Gaussian log-likelihood of
`S.starProjection (f + σ • ξ₁)` at `f + σ • ξ₂`. -/
private theorem gaussLogLik_starProjection_sub_eq (S : Submodule ℝ E) [S.HasOrthogonalProjection]
    (f : E) {σ : ℝ} (hσ : σ ≠ 0) (q : E × E) :
    gaussLogLik σ (S.starProjection (f + σ • q.1)) (f + σ • q.1) -
        gaussLogLik σ (S.starProjection (f + σ • q.1)) (f + σ • q.2) =
      (‖S.starProjection q.2‖ ^ 2 + ‖S.starProjection q.1‖ ^ 2) / 2 -
        ⟪S.starProjection q.2, S.starProjection q.1⟫ +
        (‖Sᗮ.starProjection f + σ • Sᗮ.starProjection q.2‖ ^ 2 -
          ‖Sᗮ.starProjection f + σ • Sᗮ.starProjection q.1‖ ^ 2) / (2 * σ ^ 2) := by
  set P : E →L[ℝ] E := S.starProjection
  set Q : E →L[ℝ] E := Sᗮ.starProjection
  have hPP (x : E) : P (P x) = P x :=
    Submodule.starProjection_eq_self_iff.mpr (S.starProjection_apply_mem x)
  have hQP (x : E) : Q (P x) = 0 := by rw [Submodule.starProjection_orthogonal_val, hPP, sub_self]
  rw [gaussLogLik_sub_gaussLogLik]
  have hnorm1 : ‖(f + σ • q.1) - P (f + σ • q.1)‖ ^ 2 = ‖Q f + σ • Q q.1‖ ^ 2 := by
    rw [← Submodule.starProjection_orthogonal_val, map_add, map_smul]
  have hnorm2 : ‖(f + σ • q.2) - P (f + σ • q.1)‖ ^ 2 =
      σ ^ 2 * (‖P q.2‖ ^ 2 - 2 * ⟪P q.2, P q.1⟫ + ‖P q.1‖ ^ 2) + ‖Q f + σ • Q q.2‖ ^ 2 := by
    rw [S.norm_sq_eq_add_norm_sq_starProjection ((f + σ • q.2) - P (f + σ • q.1))]
    have h1 : P ((f + σ • q.2) - P (f + σ • q.1)) = σ • (P q.2 - P q.1) := by
      rw [map_sub, hPP, map_add, map_smul, map_add, map_smul]; simp [smul_sub]
    have h2 : Q ((f + σ • q.2) - P (f + σ • q.1)) = Q f + σ • Q q.2 := by
      rw [map_sub, hQP, sub_zero, map_add, map_smul]
    rw [h1, h2, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, norm_sub_sq_real]
  rw [hnorm1, hnorm2]
  have : σ ^ 2 ≠ 0 := pow_ne_zero 2 hσ
  field_simp; ring

/-- Under `(stdGaussian E).prod (stdGaussian E)`, the projected cross term `⟪P q.2, P q.1⟫` is
integrable and has expectation zero. -/
private theorem integrable_and_integral_inner_starProjection_prod [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (S : Submodule ℝ E) :
    Integrable (fun q : E × E ↦ ⟪S.starProjection q.2, S.starProjection q.1⟫)
        ((stdGaussian E).prod (stdGaussian E)) ∧
      ∫ q : E × E, ⟪S.starProjection q.2, S.starProjection q.1⟫
        ∂((stdGaussian E).prod (stdGaussian E)) = 0 := by
  set μ : Measure E := stdGaussian E
  set P : E →L[ℝ] E := S.starProjection
  have hP_int := S.integrable_norm_sq_starProjection_stdGaussian
  have hsum_int : Integrable (fun q : E × E ↦ (‖P q.2‖ ^ 2 + ‖P q.1‖ ^ 2) / 2) (μ.prod μ) :=
    ((hP_int.comp_snd μ).add (hP_int.comp_fst μ)).div_const 2
  have hcross_int : Integrable (fun q : E × E ↦ ⟪P q.2, P q.1⟫) (μ.prod μ) := by
    refine Integrable.mono' hsum_int (by fun_prop) (.of_forall fun q ↦ ?_)
    rw [Real.norm_eq_abs]
    nlinarith [abs_real_inner_le_norm (P q.2) (P q.1), sq_nonneg (‖P q.2‖ - ‖P q.1‖)]
  refine ⟨hcross_int, ?_⟩
  rw [integral_prod _ hcross_int]
  have hslice (x : E) : ∫ y : E, ⟪P y, P x⟫ ∂μ = 0 := by
    have heq : (fun y : E ↦ ⟪P y, P x⟫) = ((innerSL ℝ (P x)).comp P) :=
      funext fun y ↦ real_inner_comm (P x) (P y)
    rw [heq]; exact integral_strongDual_stdGaussian _
  simp [hslice]

/-- **Akaike's optimism identity**: for any subspace `S`, true mean `f : E`, and `σ ≠ 0`, if
`ξ, ξ'` are independent standard Gaussian vectors in `E`, then the expected in-sample minus
out-of-sample Gaussian log-likelihood of `S.starProjection (f + σ • ξ)` equals
`Module.finrank ℝ S`, regardless of whether `f ∈ S`. -/
theorem aic_optimism [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (S : Submodule ℝ E) (f : E) {σ : ℝ} (hσ : σ ≠ 0) :
    ∫ q, (gaussLogLik σ (S.starProjection (f + σ • q.1)) (f + σ • q.1) -
        gaussLogLik σ (S.starProjection (f + σ • q.1)) (f + σ • q.2))
      ∂((stdGaussian E).prod (stdGaussian E)) = Module.finrank ℝ S := by
  -- Decompose pointwise into `S` components (`(‖P q.2‖² + ‖P q.1‖²)/2 - ⟪P q.2, P q.1⟫`) and an
  -- `Sᗮ` difference `(h_orth q.2 - h_orth q.1) / (2 σ²)` whose marginals cancel in expectation.
  simp_rw [gaussLogLik_starProjection_sub_eq S f hσ]
  set μ : Measure E := stdGaussian E
  set P : E →L[ℝ] E := S.starProjection
  set Q : E →L[ℝ] E := Sᗮ.starProjection
  set h_orth : E → ℝ := fun ξ ↦ ‖Q f + σ • Q ξ‖ ^ 2
  have hP_int : Integrable (fun ξ : E ↦ ‖P ξ‖ ^ 2) μ :=
    S.integrable_norm_sq_starProjection_stdGaussian
  have h_orth_int : Integrable h_orth μ := by
    have hexp (ξ : E) : h_orth ξ = ‖Q f‖ ^ 2 + 2 * σ * ⟪Q f, Q ξ⟫ + σ ^ 2 * ‖Q ξ‖ ^ 2 := by
      dsimp only [h_orth]
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, real_inner_smul_right]
      ring
    have hinner : Integrable (fun ξ : E ↦ ⟪Q f, Q ξ⟫) μ :=
      ((innerSL ℝ (Q f)).comp Q).integrable_comp IsGaussian.integrable_id
    exact (((integrable_const (‖Q f‖ ^ 2)).add (hinner.const_mul (2 * σ))).add
      (Sᗮ.integrable_norm_sq_starProjection_stdGaussian.const_mul (σ ^ 2))).congr
      (.of_forall fun ξ ↦ (hexp ξ).symm)
  obtain ⟨hcross_int, hcross_zero⟩ := integrable_and_integral_inner_starProjection_prod S
  have hP2_int : Integrable (fun q : E × E ↦ ‖P q.2‖ ^ 2) (μ.prod μ) := hP_int.comp_snd μ
  have hP1_int : Integrable (fun q : E × E ↦ ‖P q.1‖ ^ 2) (μ.prod μ) := hP_int.comp_fst μ
  have hsum_int : Integrable (fun q : E × E ↦ (‖P q.2‖ ^ 2 + ‖P q.1‖ ^ 2) / 2) (μ.prod μ) :=
    (hP2_int.add hP1_int).div_const 2
  have hdiff_int : Integrable
      (fun q : E × E ↦ (‖P q.2‖ ^ 2 + ‖P q.1‖ ^ 2) / 2 - ⟪P q.2, P q.1⟫) (μ.prod μ) :=
    hsum_int.sub hcross_int
  have horth2_int : Integrable (fun q : E × E ↦ h_orth q.2) (μ.prod μ) := h_orth_int.comp_snd μ
  have horth1_int : Integrable (fun q : E × E ↦ h_orth q.1) (μ.prod μ) := h_orth_int.comp_fst μ
  have horth_diff_int : Integrable (fun q : E × E ↦ (h_orth q.2 - h_orth q.1) / (2 * σ ^ 2))
      (μ.prod μ) := (horth2_int.sub horth1_int).div_const (2 * σ ^ 2)
  rw [integral_add hdiff_int horth_diff_int, integral_sub hsum_int hcross_int,
    integral_div, integral_add hP2_int hP1_int, integral_div, integral_sub horth2_int horth1_int,
    integral_fun_snd (f := fun ξ ↦ ‖P ξ‖ ^ 2), integral_fun_fst (f := fun ξ ↦ ‖P ξ‖ ^ 2),
    integral_fun_snd (f := h_orth), integral_fun_fst (f := h_orth),
    hcross_zero, S.integral_norm_sq_starProjection_stdGaussian]
  simp only [probReal_univ, one_smul]; ring

end Optimism

/-! ### Dimension-penalty, AIC, and BIC selectors -/

section Selectors

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [Nonempty ι] [LinearOrder ι]

/-- Model selector over a finite linearly ordered family of subspaces `S` with per-dimension
penalty weight `c`: minimizes
`‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c`, breaking ties in favor of
the smallest index. -/
def dimPenaltySelector (S : ι → Submodule ℝ E) (σ c : ℝ) (Y : E) : ι :=
  smallestArgmin fun j ↦ ‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c

/-- Unfolding lemma for `dimPenaltySelector`. -/
theorem dimPenaltySelector_def (S : ι → Submodule ℝ E) (σ c : ℝ) (Y : E) :
    dimPenaltySelector S σ c Y =
      smallestArgmin fun j ↦
        ‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c := (rfl)

/-- `dimPenaltySelector` attains the minimum of the dimension-penalized residual objective. -/
theorem dimPenaltySelector_le (S : ι → Submodule ℝ E) (σ c : ℝ) (Y : E) (i : ι) :
    ‖Y - (S (dimPenaltySelector S σ c Y)).starProjection Y‖ ^ 2 / σ ^ 2 +
        Module.finrank ℝ (S (dimPenaltySelector S σ c Y)) * c ≤
      ‖Y - (S i).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S i) * c :=
  smallestArgmin_le
    (fun j ↦ ‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c) i

/-- Exact characterization of `dimPenaltySelector S σ c Y = j`. -/
theorem dimPenaltySelector_eq_iff (S : ι → Submodule ℝ E) (σ c : ℝ) (Y : E) (j : ι) :
    dimPenaltySelector S σ c Y = j ↔
      (∀ i, ‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c ≤
          ‖Y - (S i).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S i) * c) ∧
      (∀ i < j, ‖Y - (S j).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j) * c <
          ‖Y - (S i).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S i) * c) :=
  smallestArgmin_eq_iff

/-- `dimPenaltySelector` is invariant under negating `σ`. -/
@[simp]
theorem dimPenaltySelector_neg (S : ι → Submodule ℝ E) (σ c : ℝ) (Y : E) :
    dimPenaltySelector S (-σ) c Y = dimPenaltySelector S σ c Y :=
  smallestArgmin_congr fun _ ↦ by simp

/-- `dimPenaltySelector` is measurable in the observation `Y`. -/
@[fun_prop]
theorem measurable_dimPenaltySelector [MeasurableSpace E] [OpensMeasurableSpace E]
    [MeasurableSpace ι] (S : ι → Submodule ℝ E) (σ c : ℝ) :
    Measurable (dimPenaltySelector S σ c) :=
  measurable_smallestArgmin fun _ ↦ Continuous.measurable (by fun_prop)

/-- Akaike's (AIC) model selector over `S`, defined as `dimPenaltySelector S σ 2`. -/
def aicSelector (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) : ι := dimPenaltySelector S σ 2 Y

/-- Unfolding lemma for `aicSelector`. -/
theorem aicSelector_def (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) :
    aicSelector S σ Y = dimPenaltySelector S σ 2 Y := (rfl)

/-- `aicSelector` is invariant under negating `σ`. -/
@[simp]
theorem aicSelector_neg (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) :
    aicSelector S (-σ) Y = aicSelector S σ Y := dimPenaltySelector_neg S σ 2 Y

/-- `aicSelector` is measurable in the observation `Y`. -/
@[fun_prop]
theorem measurable_aicSelector [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace ι]
    (S : ι → Submodule ℝ E) (σ : ℝ) : Measurable (aicSelector S σ) :=
  measurable_dimPenaltySelector S σ 2

/-- Schwarz's (BIC) model selector over `S`, defined as
`dimPenaltySelector S σ (Real.log (Module.finrank ℝ E))`. -/
def bicSelector (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) : ι :=
  dimPenaltySelector S σ (Real.log (Module.finrank ℝ E)) Y

/-- Unfolding lemma for `bicSelector`. -/
theorem bicSelector_def (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) :
    bicSelector S σ Y = dimPenaltySelector S σ (Real.log (Module.finrank ℝ E)) Y := (rfl)

/-- `bicSelector` is invariant under negating `σ`. -/
@[simp]
theorem bicSelector_neg (S : ι → Submodule ℝ E) (σ : ℝ) (Y : E) :
    bicSelector S (-σ) Y = bicSelector S σ Y := dimPenaltySelector_neg S σ _ Y

/-- `bicSelector` is measurable in the observation `Y`. -/
@[fun_prop]
theorem measurable_bicSelector [MeasurableSpace E] [OpensMeasurableSpace E] [MeasurableSpace ι]
    (S : ι → Submodule ℝ E) (σ : ℝ) : Measurable (bicSelector S σ) :=
  measurable_dimPenaltySelector S σ _

end Selectors

/-! ### Asymptotics: general dimension penalty, AIC overfitting, and BIC consistency -/

section NestedComparison

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

private theorem norm_sq_starProjection_orthogonal_inf_add_smul {U V : Submodule ℝ E} (hUV : U ≤ V)
    {f : E} (hf : f ∈ U) {σ : ℝ} (hσ : σ ≠ 0) (ξ : E) :
    ‖(Uᗮ ⊓ V).starProjection (f + σ • ξ)‖ ^ 2 / σ ^ 2 = ‖(Uᗮ ⊓ V).starProjection ξ‖ ^ 2 := by
  have hDf : (Uᗮ ⊓ V).starProjection f = 0 := by
    rw [Submodule.starProjection_orthogonal_inf_apply_of_le hUV,
      Submodule.starProjection_eq_self_iff.mpr (hUV hf),
      Submodule.starProjection_eq_self_iff.mpr hf, sub_self]
  have hD : (Uᗮ ⊓ V).starProjection (f + σ • ξ) = σ • (Uᗮ ⊓ V).starProjection ξ := by simp [hDf]
  rw [hD, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_div_cancel_left₀ _ (pow_ne_zero 2 hσ)]

/-- For nested `U ≤ V`, `V` strictly beats `U` under weight `c` when `‖P_{Uᗮ ⊓ V} Y‖² / σ²`
exceeds `(dim V - dim U) * c`. -/
private theorem dimPenalty_lt_of_le {U V : Submodule ℝ E} (hUV : U ≤ V) {σ c : ℝ} {Y : E}
    (hgt : ((Module.finrank ℝ V : ℝ) - Module.finrank ℝ U) * c <
      ‖(Uᗮ ⊓ V).starProjection Y‖ ^ 2 / σ ^ 2) :
    ‖Y - V.starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ V * c <
      ‖Y - U.starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ U * c := by
  rw [Submodule.norm_sub_starProjection_sq_of_le hUV Y, add_div]; linarith

/-- For nested `U ≤ V`, `U` beats or ties `V` under weight `c` when
`‖P_{Uᗮ ⊓ V} Y‖² / σ² ≤ (dim V - dim U) * c`. -/
private theorem dimPenalty_le_of_le {U V : Submodule ℝ E} (hUV : U ≤ V) {σ c : ℝ} {Y : E}
    (hle : ‖(Uᗮ ⊓ V).starProjection Y‖ ^ 2 / σ ^ 2 ≤
      ((Module.finrank ℝ V : ℝ) - Module.finrank ℝ U) * c) :
    ‖Y - U.starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ U * c ≤
      ‖Y - V.starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ V * c := by
  rw [Submodule.norm_sub_starProjection_sq_of_le hUV Y, add_div]; linarith

/-- Sub-Gaussian tail bound for under-selection between nested models `U ≤ V` with `f ∈ V`. -/
private theorem measureReal_underselect_le_exp [MeasurableSpace E] [BorelSpace E]
    {U V : Submodule ℝ E} (hUV : U ≤ V) {f : E} (hf : f ∈ V)
    (ha_pos : 0 < ‖f - U.starProjection f‖) {σ b : ℝ} (hσ : σ ≠ 0)
    (hdom : σ ^ 2 * b ≤ (1 / 2 : ℝ) * ‖f - U.starProjection f‖ ^ 2) :
    (stdGaussian E).real {ξ | ‖(Uᗮ ⊓ V).starProjection (f + σ • ξ)‖ ^ 2 / σ ^ 2 ≤ b} ≤
      Real.exp (-(‖f - U.starProjection f‖ ^ 2 / (32 * σ ^ 2))) := by
  have hσ2 : 0 < σ ^ 2 := sq_pos_of_ne_zero hσ
  set D : Submodule ℝ E := Uᗮ ⊓ V
  set a : E := f - U.starProjection f
  have hDf : D.starProjection f = a := by
    rw [Submodule.starProjection_orthogonal_inf_apply_of_le hUV,
      Submodule.starProjection_eq_self_iff.mpr hf]
  have ha_mem : a ∈ D := hDf ▸ D.starProjection_apply_mem f
  set u : E := (-2 * σ) • a
  set L : StrongDual ℝ E := innerSL ℝ u
  -- Drop `σ ^ 2 * ‖D.starProjection ξ‖ ^ 2 ≥ 0` to reduce to a linear Gaussian tail event `L ξ`.
  have hsub : {ξ : E | ‖D.starProjection (f + σ • ξ)‖ ^ 2 / σ ^ 2 ≤ b} ⊆
      {ξ : E | (1 / 2 : ℝ) * ‖a‖ ^ 2 ≤ L ξ} := fun ξ hξ ↦ by
    simp only [Set.mem_ofPred_eq] at hξ ⊢
    have hmul : ‖a + σ • D.starProjection ξ‖ ^ 2 ≤ σ ^ 2 * b := by
      rw [← hDf, ← map_smul, ← map_add]; linarith [(div_le_iff₀ hσ2).mp hξ]
    have hinner_eq : ⟪a, D.starProjection ξ⟫ = ⟪a, ξ⟫ := by
      rw [← D.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr ha_mem]
    have hexp : ‖a + σ • D.starProjection ξ‖ ^ 2 =
        ‖a‖ ^ 2 + 2 * σ * ⟪a, ξ⟫ + σ ^ 2 * ‖D.starProjection ξ‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
        real_inner_smul_right, hinner_eq]; ring
    have hLξ : L ξ = -2 * σ * ⟪a, ξ⟫ := by
      simp only [L, u, innerSL_apply_apply, real_inner_smul_left]
    linarith [show 0 ≤ σ ^ 2 * ‖D.starProjection ξ‖ ^ 2 by positivity]
  -- Apply the centered Gaussian Chernoff bound to `L ~ N(0, 4 σ² ‖a‖²)`.
  set v : ℝ≥0 := ‖u‖₊ ^ 2
  have hlaw : HasLaw L (gaussianReal 0 v) (stdGaussian E) := by
    refine ⟨L.continuous.aemeasurable, ?_⟩
    rw [IsGaussian.map_eq_gaussianReal L, integral_strongDual_stdGaussian L,
      variance_dual_stdGaussian L, innerSL_apply_norm]
    congr 1; ext; rw [Real.coe_toNNReal _ (sq_nonneg _)]; simp [v]
  have htail := hlaw.hasSubgaussianMGF.measure_ge_le (ε := (1 / 2 : ℝ) * ‖a‖ ^ 2) (by positivity)
  have hunorm : (v : ℝ) = 4 * σ ^ 2 * ‖a‖ ^ 2 := by
    simp only [v, NNReal.coe_pow, coe_nnNorm, u, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]; ring
  have hratio : -((1 / 2 : ℝ) * ‖a‖ ^ 2) ^ 2 / (2 * (v : ℝ)) = -(‖a‖ ^ 2 / (32 * σ ^ 2)) := by
    rw [hunorm]
    have : ‖a‖ ^ 2 ≠ 0 := pow_ne_zero 2 ha_pos.ne'
    have : σ ^ 2 ≠ 0 := hσ2.ne'
    field_simp; ring
  rw [hratio] at htail
  exact (measureReal_mono hsub).trans htail

/-- Markov bound for over-selection between nested models `U ≤ V` with `f ∈ U` and `kU < kV`. -/
private theorem measureReal_overselect_le_inv [MeasurableSpace E] [BorelSpace E]
    {U V : Submodule ℝ E} (hUV : U ≤ V) {kU kV : ℕ} (hklt : kU < kV)
    (hU : Module.finrank ℝ U = kU) (hV : Module.finrank ℝ V = kV)
    {f : E} (hf : f ∈ U) {σ w : ℝ} (hσ : σ ≠ 0) (hw : 0 < w) :
    (stdGaussian E).real
      {ξ | ((kV : ℝ) - kU) * w < ‖(Uᗮ ⊓ V).starProjection (f + σ • ξ)‖ ^ 2 / σ ^ 2} ≤ w⁻¹ := by
  set D : Submodule ℝ E := Uᗮ ⊓ V
  set d : ℕ := kV - kU
  have hd_pos : 0 < (d : ℝ) := Nat.cast_pos.mpr (Nat.sub_pos_of_lt hklt)
  have hDdim : Module.finrank ℝ D = d :=
    Submodule.finrank_add_inf_finrank_orthogonal' hUV (by rw [hU, hV]; omega)
  have hd_cast : (d : ℝ) = (kV : ℝ) - kU := by simp only [d, Nat.cast_sub hklt.le]
  have hsub : {ξ : E | ((kV : ℝ) - kU) * w < ‖D.starProjection (f + σ • ξ)‖ ^ 2 / σ ^ 2} ⊆
      {ξ : E | (d : ℝ) * w ≤ ‖D.starProjection ξ‖ ^ 2} := fun ξ hξ ↦ by
    simp only [Set.mem_ofPred_eq] at hξ ⊢
    rw [norm_sq_starProjection_orthogonal_inf_add_smul hUV hf hσ, ← hd_cast] at hξ; exact hξ.le
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := stdGaussian E)
    (f := fun ξ : E ↦ ‖D.starProjection ξ‖ ^ 2) (.of_forall fun _ ↦ sq_nonneg _)
    D.integrable_norm_sq_starProjection_stdGaussian ((d : ℝ) * w)
  rw [D.integral_norm_sq_starProjection_stdGaussian, hDdim] at hmarkov
  have hdiv := (le_div_iff₀' (by positivity : 0 < (d : ℝ) * w)).mpr hmarkov
  have : (d : ℝ) ≠ 0 := hd_pos.ne'
  have : w ≠ 0 := hw.ne'
  exact (measureReal_mono hsub).trans (hdiv.trans_eq (by field_simp))

end NestedComparison

section Asymptotics

variable {E : ℕ → Type*}
  [∀ n, NormedAddCommGroup (E n)] [∀ n, InnerProductSpace ℝ (E n)]
  [∀ n, FiniteDimensional ℝ (E n)] [∀ n, MeasurableSpace (E n)] [∀ n, BorelSpace (E n)]

/-- Shared under-selection probability bound for nested Gaussian linear models. -/
private theorem tendsto_measureReal_underselect
    (U V : (n : ℕ) → Submodule ℝ (E n)) (f : (n : ℕ) → E n) {σ : ℝ} (hσ : σ ≠ 0) (w : ℕ → ℝ)
    (c : ℝ) (hle : ∀ᶠ n in atTop, U n ≤ V n) (hf : ∀ᶠ n in atTop, f n ∈ V n)
    (hsep : Tendsto (fun n ↦ ‖f n - (U n).starProjection (f n)‖) atTop atTop)
    (hdom : ∀ᶠ n in atTop,
      σ ^ 2 * c * w n ≤ (1 / 2 : ℝ) * ‖f n - (U n).starProjection (f n)‖ ^ 2) :
    Tendsto (fun n ↦ (stdGaussian (E n)).real
      {ξ | ‖((U n)ᗮ ⊓ V n).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤ c * w n})
      atTop (𝓝 0) := by
  have hbound : ∀ᶠ n in atTop,
      (stdGaussian (E n)).real
          {ξ | ‖((U n)ᗮ ⊓ V n).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤ c * w n} ≤
        Real.exp (-(‖f n - (U n).starProjection (f n)‖ ^ 2 / (32 * σ ^ 2))) := by
    filter_upwards [hle, hf, hdom, hsep.eventually (eventually_gt_atTop 0)]
      with n hUV hfn hdom_n ha_pos
    exact measureReal_underselect_le_exp hUV hfn ha_pos hσ (by linarith)
  exact squeeze_zero' (.of_forall fun _ ↦ measureReal_nonneg) hbound <|
    Real.tendsto_exp_atBot.comp <| tendsto_neg_atTop_atBot.comp <|
      ((tendsto_pow_atTop two_ne_zero).comp hsep).atTop_div_const
        (by positivity : 0 < 32 * σ ^ 2)

/-- Over-selection probability bound for nested Gaussian linear models. -/
private theorem tendsto_measureReal_overselect
    (U V : (n : ℕ) → Submodule ℝ (E n)) (f : (n : ℕ) → E n) {σ : ℝ} (hσ : σ ≠ 0) (w : ℕ → ℝ)
    (kU kV : ℕ) (hle : ∀ᶠ n in atTop, U n ≤ V n)
    (hdimU : ∀ᶠ n in atTop, Module.finrank ℝ (U n) = kU)
    (hdimV : ∀ᶠ n in atTop, Module.finrank ℝ (V n) = kV)
    (hf : ∀ᶠ n in atTop, f n ∈ U n) (hw : Tendsto w atTop atTop) :
    Tendsto (fun n ↦ (stdGaussian (E n)).real
      {ξ | ((kV : ℝ) - kU) * w n <
        ‖((U n)ᗮ ⊓ V n).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2}) atTop (𝓝 0) := by
  have hkle : kU ≤ kV := by
    obtain ⟨n, hUV, hU, hV⟩ := (hle.and (hdimU.and hdimV)).exists
    simpa [hU, hV] using Submodule.finrank_mono hUV
  rcases hkle.eq_or_lt with hkeq | hklt
  · -- Equal dimensions force `U n = V n`, so `(U n)ᗮ ⊓ V n = ⊥` and the event is empty.
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hle, hdimU, hdimV] with n hUV hU hV
    have hSeq : U n = V n := Submodule.eq_of_le_of_finrank_eq hUV (by rw [hU, hV, hkeq])
    have hDbot : (U n)ᗮ ⊓ V n = ⊥ := hSeq ▸ (Submodule.orthogonal_disjoint (U n)).symm.eq_bot
    have : {ξ : E n | ((kV : ℝ) - kU) * w n <
        ‖((U n)ᗮ ⊓ V n).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2} = ∅ := by
      ext ξ; simp [hkeq, hDbot]
    rw [this, measureReal_empty]
  · -- Positive rank gap `d = kV - kU`: apply `measureReal_overselect_le_inv`.
    refine squeeze_zero' (.of_forall fun _ ↦ measureReal_nonneg) ?_ (tendsto_inv_atTop_zero.comp hw)
    filter_upwards [hle, hdimU, hdimV, hf, hw.eventually (eventually_gt_atTop 0)]
      with n hUV hU hV hfn hw_pos
    exact measureReal_overselect_le_inv hUV hklt hU hV hfn hσ hw_pos

variable {ι : Type*} [Fintype ι] [Nonempty ι] [LinearOrder ι]

/-- **Bounded dimension penalties overfit** (asymptotic lower bound): when `c n ≤ C` eventually,
`S n` is eventually monotone with dimensions `k`, `f n ∈ S n j₀` eventually, `k j₀ < k j₁`, and
smaller models satisfy `‖f n - (S n j).starProjection (f n)‖ → ∞`, the asymptotic probability that
`dimPenaltySelector (S n) σ (c n)` selects an index `> j₀` is at least `P(χ²_d > C * d)` for
`d = k j₁ - k j₀`. -/
theorem dimPenaltySelector_overfit (k : ι → ℕ) (S : (n : ℕ) → ι → Submodule ℝ (E n))
    (c : ℕ → ℝ) (C : ℝ) (hc : ∀ᶠ n in atTop, c n ≤ C) (hS : ∀ᶠ n in atTop, Monotone (S n))
    (hdim : ∀ᶠ n in atTop, ∀ j, Module.finrank ℝ (S n j) = k j)
    (f : (n : ℕ) → E n) (j₀ j₁ : ι) (hk : k j₀ < k j₁) (hf : ∀ᶠ n in atTop, f n ∈ S n j₀)
    (hsep : ∀ j < j₀, Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖) atTop atTop)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (TauCeti.Probability.chiSquaredMeasure (k j₁ - k j₀ : ℕ)).real
        (Set.Ioi (C * ((k j₁ - k j₀ : ℕ) : ℝ))) ≤
      liminf (fun n ↦ (stdGaussian (E n)).real
        {ξ | j₀ < dimPenaltySelector (S n) σ (c n) (f n + σ • ξ)}) atTop := by
  have hj₀₁ : j₀ < j₁ := by
    obtain ⟨n, hSn, hdimn⟩ := (hS.and hdim).exists
    exact lt_of_not_ge fun hle ↦ not_le_of_gt hk
      (by simpa [hdimn j₀, hdimn j₁] using Submodule.finrank_mono (hSn hle))
  set d : ℕ := k j₁ - k j₀
  set p : ℝ := (TauCeti.Probability.chiSquaredMeasure d).real (Set.Ioi (C * (d : ℝ)))
  let u : ℕ → ℝ := fun n ↦
    (stdGaussian (E n)).real {ξ | j₀ < dimPenaltySelector (S n) σ (c n) (f n + σ • ξ)}
  let b : ι → ℕ → ℝ := fun j n ↦ (stdGaussian (E n)).real
    {ξ : E n | ‖((S n j)ᗮ ⊓ S n j₀).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤
      ((k j₀ : ℝ) - k j) * C}
  let lower : Finset ι := Finset.univ.filter (· < j₀)
  -- Under-selection probabilities against models `j < j₀` vanish exponentially fast.
  have hb (j : ι) (hj : j < j₀) : Tendsto (b j) atTop (𝓝 0) := by
    refine tendsto_measureReal_underselect (fun n ↦ S n j) (fun n ↦ S n j₀) f hσ
      (fun _ ↦ C) ((k j₀ : ℝ) - k j) (hS.mono fun _ h ↦ h hj.le) hf (hsep j hj) ?_
    filter_upwards [((tendsto_pow_atTop two_ne_zero).comp (hsep j hj)).eventually
      (eventually_ge_atTop (2 * (σ ^ 2 * ((k j₀ : ℝ) - k j) * C)))] with n hn
    dsimp only [Function.comp_apply] at hn; linarith
  have hsum_zero : Tendsto (fun n ↦ ∑ j ∈ lower, b j n) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum lower fun j hj ↦ hb j (Finset.mem_filter.mp hj).2
  -- On `{ξ | C * d < ‖P_D ξ‖²}` minus the under-selection events, `j₁` beats every `i ≤ j₀`.
  have hstep : ∀ᶠ n in atTop, p ≤ u n + ∑ j ∈ lower, b j n := by
    filter_upwards [hc, hS, hdim, hf] with n hcn hSn hdimn hfn
    set D : Submodule ℝ (E n) := (S n j₀)ᗮ ⊓ S n j₁
    set A : Set (E n) := {ξ | C * (d : ℝ) < ‖D.starProjection ξ‖ ^ 2}
    have hDdim : Module.finrank ℝ D = d :=
      Submodule.finrank_add_inf_finrank_orthogonal' (hSn hj₀₁.le)
        (by rw [hdimn j₀, hdimn j₁]; omega)
    have hA_prob : (stdGaussian (E n)).real A = p := by
      have hmap := D.map_norm_sq_starProjection_stdGaussian
      rw [hDdim] at hmap
      rw [show p = (TauCeti.Probability.chiSquaredMeasure d).real (Set.Ioi (C * (d : ℝ))) from rfl,
        ← hmap, map_measureReal_apply (by fun_prop) measurableSet_Ioi]
      simp only [A, Set.Ioi, Set.preimage_ofPred_eq]
    have hsub : A ⊆ {ξ | j₀ < dimPenaltySelector (S n) σ (c n) (f n + σ • ξ)} ∪
        ⋃ j ∈ lower, {ξ : E n | ‖((S n j)ᗮ ⊓ S n j₀).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤
          ((k j₀ : ℝ) - k j) * C} := fun ξ hξ ↦ by
      simp only [A, D, Set.mem_ofPred_eq] at hξ
      by_cases hunder : ∃ j ∈ lower,
          ‖((S n j)ᗮ ⊓ S n j₀).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤ ((k j₀ : ℝ) - k j) * C
      · obtain ⟨j, hj, hle⟩ := hunder
        exact Or.inr (Set.mem_iUnion₂.mpr ⟨j, hj, hle⟩)
      · left; push Not at hunder
        set Y : E n := f n + σ • ξ
        simp only [Set.mem_ofPred_eq]; rw [dimPenaltySelector_def]
        refine lt_smallestArgmin_of_forall_lt fun i hi ↦ ⟨j₁, ?_⟩
        have h10 := dimPenalty_lt_of_le (hSn hj₀₁.le) (σ := σ) (c := c n) (Y := Y) <| by
          rw [hdimn j₁, hdimn j₀,
            norm_sq_starProjection_orthogonal_inf_add_smul (hSn hj₀₁.le) hfn hσ]
          have hd_cast : (d : ℝ) = (k j₁ : ℝ) - k j₀ := by simp only [d, Nat.cast_sub hk.le]
          rw [← hd_cast]
          exact (mul_le_mul_of_nonneg_left hcn (Nat.cast_nonneg d)).trans_lt (by linarith)
        rcases hi.eq_or_lt with rfl | hlt
        · exact h10
        · have hgt := hunder i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
          have hk_sub_nonneg : 0 ≤ (k j₀ : ℝ) - k i := sub_nonneg.mpr <| by
            exact_mod_cast (hdimn i ▸ hdimn j₀ ▸ Submodule.finrank_mono (hSn hlt.le))
          exact h10.trans <| dimPenalty_lt_of_le (hSn hlt.le) <| by
            rw [hdimn j₀, hdimn i]
            exact (mul_le_mul_of_nonneg_left hcn hk_sub_nonneg).trans_lt hgt
    exact hA_prob.symm.trans_le <| (measureReal_mono hsub).trans <|
      (measureReal_union_le _ _).trans <| add_le_add le_rfl (measureReal_biUnion_finset_le lower _)
  refine le_of_forall_pos_le_add fun ε hε ↦ ?_
  have hev : ∀ᶠ n in atTop, p - ε ≤ u n := by
    filter_upwards [hstep, hsum_zero.eventually (Iio_mem_nhds hε)] with n hn1 hn2; linarith
  linarith [le_liminf_of_le (isCoboundedUnder_ge_of_le atTop fun _ ↦ measureReal_le_one) hev]

/-- **Akaike's criterion overfits** (asymptotic lower bound): for nested models `S n` with
dimensions eventually equal to `k`, true mean `f n ∈ S n j₀` eventually, `k j₀ < k j₁`, and smaller
models separated by `‖f n - (S n j).starProjection (f n)‖ → ∞`, the asymptotic probability that
`aicSelector` selects an index `> j₀` is at least `P(χ²_d > 2 * d)` for `d = k j₁ - k j₀`. -/
theorem aic_overfit (k : ι → ℕ) (S : (n : ℕ) → ι → Submodule ℝ (E n))
    (hS : ∀ᶠ n in atTop, Monotone (S n))
    (hdim : ∀ᶠ n in atTop, ∀ j, Module.finrank ℝ (S n j) = k j)
    (f : (n : ℕ) → E n) (j₀ j₁ : ι) (hk : k j₀ < k j₁) (hf : ∀ᶠ n in atTop, f n ∈ S n j₀)
    (hsep : ∀ j < j₀, Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖) atTop atTop)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (TauCeti.Probability.chiSquaredMeasure (k j₁ - k j₀ : ℕ)).real
        (Set.Ioi (2 * ((k j₁ - k j₀ : ℕ) : ℝ))) ≤
      liminf (fun n ↦ (stdGaussian (E n)).real
        {ξ | j₀ < aicSelector (S n) σ (f n + σ • ξ)}) atTop :=
  dimPenaltySelector_overfit k S (fun _ ↦ 2) 2 (.of_forall fun _ ↦ le_rfl) hS hdim f j₀ j₁ hk hf
    hsep hσ

/-- Under the hypotheses of `aic_overfit`, the asymptotic overfitting probability of `aicSelector`
is strictly positive. -/
theorem aic_overfit_pos (k : ι → ℕ) (S : (n : ℕ) → ι → Submodule ℝ (E n))
    (hS : ∀ᶠ n in atTop, Monotone (S n))
    (hdim : ∀ᶠ n in atTop, ∀ j, Module.finrank ℝ (S n j) = k j)
    (f : (n : ℕ) → E n) (j₀ j₁ : ι) (hk : k j₀ < k j₁) (hf : ∀ᶠ n in atTop, f n ∈ S n j₀)
    (hsep : ∀ j < j₀, Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖) atTop atTop)
    {σ : ℝ} (hσ : σ ≠ 0) :
    0 < liminf (fun n ↦ (stdGaussian (E n)).real
      {ξ | j₀ < aicSelector (S n) σ (f n + σ • ξ)}) atTop :=
  (TauCeti.Probability.measureReal_Ioi_chiSquaredMeasure_pos
    (Nat.cast_pos.mpr (Nat.sub_pos_of_lt hk)) _).trans_le
    (aic_overfit k S hS hdim f j₀ j₁ hk hf hsep hσ)

/-- Deterministic inclusion of `{dimPenaltySelector S σ c Y ≠ j₀}` into the union of pairwise
under-selection (`j < j₀`) and over-selection (`j₀ < j`) events for nested models `S`. -/
private theorem subset_underselect_union_overselect {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] {S : ι → Submodule ℝ F} (hS : Monotone S)
    {k : ι → ℕ} (hdim : ∀ j, Module.finrank ℝ (S j) = k j) (j₀ : ι) (σ c : ℝ) (Y : F)
    (hne : dimPenaltySelector S σ c Y ≠ j₀) :
    (∃ j ∈ Finset.univ.filter (· < j₀),
        ‖((S j)ᗮ ⊓ S j₀).starProjection Y‖ ^ 2 / σ ^ 2 ≤ ((k j₀ : ℝ) - k j) * c) ∨
      (∃ j ∈ Finset.univ.filter (j₀ < ·),
        ((k j : ℝ) - k j₀) * c < ‖((S j₀)ᗮ ⊓ S j).starProjection Y‖ ^ 2 / σ ^ 2) := by
  by_contra hnone
  push Not at hnone
  have hlt_low (i : ι) (hi : i < j₀) :
      ‖Y - (S j₀).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S j₀) * c <
        ‖Y - (S i).starProjection Y‖ ^ 2 / σ ^ 2 + Module.finrank ℝ (S i) * c :=
    dimPenalty_lt_of_le (hS hi.le) <| by
      rw [hdim j₀, hdim i]; exact hnone.1 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  refine hne ((dimPenaltySelector_eq_iff S σ c Y j₀).mpr ⟨fun i ↦ ?_, hlt_low⟩)
  rcases lt_trichotomy i j₀ with hi | rfl | hi
  · exact (hlt_low i hi).le
  · exact le_rfl
  · exact dimPenalty_le_of_le (hS hi.le) <| by
      rw [hdim i, hdim j₀]; exact hnone.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)

/-- **Diverging dimension penalties are consistent**: for nested models `S n` with dimensions
eventually equal to `k`, penalty weights `c n → ∞`, `f n ∈ S n j₀` eventually, and smaller models
separated by `‖f n - (S n j).starProjection (f n)‖ ^ 2 / c n → ∞`, the probability that
`dimPenaltySelector (S n) σ (c n)` selects `j₀` tends to `1` (ties broken in favor of `j₀`). -/
theorem dimPenaltySelector_consistent (k : ι → ℕ) (S : (n : ℕ) → ι → Submodule ℝ (E n))
    {c : ℕ → ℝ} (hc : Tendsto c atTop atTop) (hS : ∀ᶠ n in atTop, Monotone (S n))
    (hdim : ∀ᶠ n in atTop, ∀ j, Module.finrank ℝ (S n j) = k j)
    (f : (n : ℕ) → E n) (j₀ : ι) (hf : ∀ᶠ n in atTop, f n ∈ S n j₀)
    (hsep : ∀ j < j₀, Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖ ^ 2 / c n) atTop atTop)
    {σ : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun n ↦ (stdGaussian (E n)).real
      {ξ | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) = j₀}) atTop (𝓝 1) := by
  let lower : Finset ι := Finset.univ.filter (· < j₀)
  let upper : Finset ι := Finset.univ.filter (j₀ < ·)
  let b_low : ι → ℕ → ℝ := fun j n ↦ (stdGaussian (E n)).real
    {ξ : E n | ‖((S n j)ᗮ ⊓ S n j₀).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤
      ((k j₀ : ℝ) - k j) * c n}
  let b_high : ι → ℕ → ℝ := fun j n ↦ (stdGaussian (E n)).real
    {ξ : E n | ((k j : ℝ) - k j₀) * c n <
      ‖((S n j₀)ᗮ ⊓ S n j).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2}
  -- Pairwise under-selection (`j < j₀`) and over-selection (`j₀ < j`) probabilities tend to `0`.
  have hb_low (j : ι) (hj : j < j₀) : Tendsto (b_low j) atTop (𝓝 0) := by
    have hnorm_sq : Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖ ^ 2) atTop atTop :=
      tendsto_atTop_mono' atTop
        ((hc.eventually (eventually_ge_atTop 1)).mono fun _ hn ↦ div_le_self (sq_nonneg _) hn)
        (hsep j hj)
    have hnorm : Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖) atTop atTop := by
      simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
        Real.tendsto_sqrt_atTop.comp hnorm_sq
    refine tendsto_measureReal_underselect (fun n ↦ S n j) (fun n ↦ S n j₀) f hσ c
      ((k j₀ : ℝ) - k j) (hS.mono fun _ h ↦ h hj.le) hf hnorm ?_
    filter_upwards [(hsep j hj).eventually (eventually_ge_atTop (2 * (σ ^ 2 * ((k j₀ : ℝ) - k j)))),
      hc.eventually (eventually_gt_atTop 0)] with n hn hc_pos
    have := mul_le_mul_of_nonneg_right hn hc_pos.le
    rw [div_mul_cancel₀ _ hc_pos.ne'] at this; linarith
  have hb_high (j : ι) (hj : j₀ < j) : Tendsto (b_high j) atTop (𝓝 0) :=
    tendsto_measureReal_overselect (fun n ↦ S n j₀) (fun n ↦ S n j) f hσ c (k j₀) (k j)
      (hS.mono fun _ h ↦ h hj.le) (hdim.mono fun _ h ↦ h j₀) (hdim.mono fun _ h ↦ h j) hf hc
  -- Union bound over `lower` and `upper`, then pass to the complement event.
  have hbad_zero : Tendsto
      (fun n ↦ (stdGaussian (E n)).real {ξ | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) ≠ j₀})
      atTop (𝓝 0) := by
    have hsum_low : Tendsto (fun n ↦ ∑ j ∈ lower, b_low j n) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum lower fun j hj ↦ hb_low j (Finset.mem_filter.mp hj).2
    have hsum_high : Tendsto (fun n ↦ ∑ j ∈ upper, b_high j n) atTop (𝓝 0) := by
      simpa using tendsto_finsetSum upper fun j hj ↦ hb_high j (Finset.mem_filter.mp hj).2
    refine squeeze_zero' (.of_forall fun _ ↦ measureReal_nonneg) ?_
      (by simpa using hsum_low.add hsum_high)
    filter_upwards [hS, hdim] with n hSn hdimn
    have hsub : {ξ : E n | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) ≠ j₀} ⊆
        (⋃ j ∈ lower, {ξ : E n | ‖((S n j)ᗮ ⊓ S n j₀).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2 ≤
          ((k j₀ : ℝ) - k j) * c n}) ∪
        (⋃ j ∈ upper, {ξ : E n | ((k j : ℝ) - k j₀) * c n <
          ‖((S n j₀)ᗮ ⊓ S n j).starProjection (f n + σ • ξ)‖ ^ 2 / σ ^ 2}) := fun ξ hξ ↦
      (subset_underselect_union_overselect hSn hdimn j₀ σ (c n) (f n + σ • ξ) hξ).imp
        (fun ⟨j, hj, hle⟩ ↦ Set.mem_iUnion₂.mpr ⟨j, hj, hle⟩)
        (fun ⟨j, hj, hlt⟩ ↦ Set.mem_iUnion₂.mpr ⟨j, hj, hlt⟩)
    exact (measureReal_mono hsub).trans <| (measureReal_union_le _ _).trans <|
      add_le_add (measureReal_biUnion_finset_le lower _) (measureReal_biUnion_finset_le upper _)
  have hcompl (n : ℕ) :
      (stdGaussian (E n)).real {ξ | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) = j₀} =
        1 - (stdGaussian (E n)).real {ξ | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) ≠ j₀} := by
    let : MeasurableSpace ι := ⊤
    have hmset : MeasurableSet {ξ : E n | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) ≠ j₀} :=
      ((measurable_dimPenaltySelector (S n) σ (c n)).comp (by fun_prop))
        (t := {j₀}ᶜ) MeasurableSpace.measurableSet_top
    have heq : {ξ : E n | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) = j₀} =
        {ξ : E n | dimPenaltySelector (S n) σ (c n) (f n + σ • ξ) ≠ j₀}ᶜ := by ext ξ; simp
    rw [heq, probReal_compl_eq_one_sub hmset]
  simp_rw [hcompl]
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hbad_zero

/-- **Schwarz's criterion (BIC) is consistent**: for nested models `S n` with dimensions eventually
equal to `k` inside ambient spaces `E n` with `Module.finrank ℝ (E n) → ∞`, `f n ∈ S n j₀`
eventually, and smaller models separated by
`‖f n - (S n j).starProjection (f n)‖ ^ 2 / Real.log (Module.finrank ℝ (E n)) → ∞`, the
probability that `bicSelector` selects `j₀` tends to `1` (ties broken in favor of `j₀`). -/
theorem bic_consistent (k : ι → ℕ) (S : (n : ℕ) → ι → Submodule ℝ (E n))
    (hdim_E : Tendsto (fun n ↦ (Module.finrank ℝ (E n) : ℝ)) atTop atTop)
    (hS : ∀ᶠ n in atTop, Monotone (S n))
    (hdim : ∀ᶠ n in atTop, ∀ j, Module.finrank ℝ (S n j) = k j)
    (f : (n : ℕ) → E n) (j₀ : ι) (hf : ∀ᶠ n in atTop, f n ∈ S n j₀)
    (hsep : ∀ j < j₀,
      Tendsto (fun n ↦ ‖f n - (S n j).starProjection (f n)‖ ^ 2 /
        Real.log (Module.finrank ℝ (E n))) atTop atTop)
    {σ : ℝ} (hσ : σ ≠ 0) :
    Tendsto (fun n ↦ (stdGaussian (E n)).real
      {ξ | bicSelector (S n) σ (f n + σ • ξ) = j₀}) atTop (𝓝 1) :=
  dimPenaltySelector_consistent k S (Real.tendsto_log_atTop.comp hdim_E) hS hdim f j₀ hf hsep hσ

end Asymptotics

end TauCeti
