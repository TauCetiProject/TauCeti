/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.Filter.Cofinite
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.MeasureTheory.Function.SmallestArgmin
import TauCeti.Probability.Distributions.Gaussian.Projection

/-!
# Penalized model selection in the Gaussian regression model

Given a finite-dimensional real inner product space `E` of dimension `n = Module.finrank ℝ E` and a
countable family of linear models `(S m)_{m : M}`, the penalized empirical-risk criterion is
`penalizedCriterion S pen Y m = ‖Y - (S m).starProjection Y‖ ^ 2 / n + pen m`.

For `Y = f + σ • ξ` with `ξ ~ stdGaussian E`, we prove:
* existence of a measurable minimizer (`exists_measurable_penalizedSelector_of_tendsto`,
  `exists_measurable_penalizedSelector`), without `MeasurableSingletonClass M`;
* integrability of the squared error (`integrable_sq_norm_starProjection_sub`) and the
  Birgé–Massart / Giraud oracle inequality (`penalized_model_selection`) for any `κ > 4` with
  leading constant `κ / (κ - 4)` (without assuming `σ > 0`, `∑' π ≤ 1`, or `Nontrivial E`).

## References

* C. Giraud, *Introduction to High-Dimensional Statistics*, 2nd ed., CRC Press (2022), Theorem 2.2.
* P. Massart, *Concentration Inequalities and Model Selection*, Lecture Notes in Math. **1896**,
  Springer (2007), Theorem 4.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal RealInnerProductSpace

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ### The penalized criterion -/

/-- The penalized empirical least-squares criterion
`‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m`. -/
def penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) : ℝ :=
  ‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m

/-- Unfolding lemma for `penalizedCriterion`. -/
theorem penalizedCriterion_def {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) :
    penalizedCriterion S pen Y m = ‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m :=
  (rfl)

/-- If the observation `Y` already lies in `S m`, the penalized criterion reduces to `pen m`. -/
theorem penalizedCriterion_of_mem {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) {Y : E}
    {m : M} (hY : Y ∈ S m) : penalizedCriterion S pen Y m = pen m := by
  simp [penalizedCriterion_def, Submodule.starProjection_eq_self_iff.mpr hY]

/-- At `S m = ⊥`, the penalized criterion is `‖Y‖ ^ 2 / Module.finrank ℝ E + pen m`. -/
theorem penalizedCriterion_of_eq_bot {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E)
    {m : M} (h : S m = ⊥) :
    penalizedCriterion S pen Y m = ‖Y‖ ^ 2 / Module.finrank ℝ E + pen m := by
  simp [penalizedCriterion_def, h]

/-- At the full space `S m = ⊤`, the penalized criterion is `pen m`. -/
theorem penalizedCriterion_of_eq_top {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E)
    {m : M} (h : S m = ⊤) : penalizedCriterion S pen Y m = pen m :=
  penalizedCriterion_of_mem S pen (h.symm ▸ Submodule.mem_top)

/-- The penalty lower-bounds the penalized criterion. -/
theorem le_penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) :
    pen m ≤ penalizedCriterion S pen Y m :=
  penalizedCriterion_def S pen Y m ▸ le_add_of_nonneg_left (by positivity)

/-- For each model `m`, the penalized criterion depends continuously on the observation `Y`. -/
@[fun_prop]
theorem continuous_penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (m : M) :
    Continuous fun Y ↦ penalizedCriterion S pen Y m := by unfold penalizedCriterion; fun_prop

/-- For each model `m`, the penalized criterion is measurable in the observation `Y`. -/
@[fun_prop]
theorem measurable_penalizedCriterion [MeasurableSpace E] [OpensMeasurableSpace E]
    {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (m : M) :
    Measurable fun Y ↦ penalizedCriterion S pen Y m :=
  (continuous_penalizedCriterion S pen m).measurable

/-! ### Existence of a measurable selector -/

/-- If `pen` tends to `+∞` along `cofinite` on a countable nonempty type `M`, then
`penalizedCriterion S pen Y` admits a measurable minimizer `mh : E → M` (without requiring
`MeasurableSingletonClass M`). -/
theorem exists_measurable_penalizedSelector_of_tendsto [MeasurableSpace E]
    [OpensMeasurableSpace E] {M : Type*} [Countable M] [Nonempty M] [MeasurableSpace M]
    (S : M → Submodule ℝ E) (pen : M → ℝ) (hpen : Tendsto pen cofinite atTop) :
    ∃ mh : E → M, Measurable mh ∧
      ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m :=
  exists_measurable_forall_le (measurable_penalizedCriterion S pen) fun Y ↦
    (tendsto_atTop_mono (le_penalizedCriterion S pen Y) hpen).exists_forall_le

/-- A measurable minimizer of `penalizedCriterion` exists when `E` is nontrivial, `κ > 0`, `σ ≠ 0`,
`π` is positive and summable, and `pen` dominates the Birgé–Massart penalty
`κ * σ ^ 2 * (dim (S m) + log (1 / π m)) / Module.finrank ℝ E`. -/
theorem exists_measurable_penalizedSelector [Nontrivial E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {M : Type*} [Countable M] [Nonempty M] [MeasurableSpace M]
    (S : M → Submodule ℝ E) (π pen : M → ℝ) {κ σ : ℝ} (hκ : 0 < κ) (hσ : σ ≠ 0)
    (hπ : ∀ m, 0 < π m) (hsum : Summable π)
    (hpen : ∀ m, κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) /
      Module.finrank ℝ E ≤ pen m) :
    ∃ mh : E → M, Measurable mh ∧
      ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m := by
  refine exists_measurable_penalizedSelector_of_tendsto S pen (tendsto_atTop.mpr fun C ↦ ?_)
  have hdim : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hε : 0 < Real.exp (-((Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2))) := Real.exp_pos _
  refine (hsum.tendsto_cofinite_zero.eventually (Iio_mem_nhds hε)).mono fun m hm ↦ ?_
  have hlog : Real.log (π m) < -((Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2)) :=
    (Real.log_lt_log (hπ m) hm).trans_eq (Real.log_exp _)
  have hlog_inv : (Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2) ≤ Real.log (1 / π m) := by
    rw [one_div, Real.log_inv]; linarith
  have h1 : C ≤ κ * σ ^ 2 * Real.log (1 / π m) / Module.finrank ℝ E := by
    rw [le_div_iff₀ hdim, mul_comm C]
    have := (div_le_iff₀ (by positivity : 0 < κ * σ ^ 2)).mp hlog_inv
    linarith
  exact (h1.trans (by gcongr; exact le_add_of_nonneg_left (Nat.cast_nonneg _))).trans (hpen m)

/-! ### Exponential-moment control and pointwise oracle bound -/

/-- Per-model chi-squared exponential-moment bound at tilt `1 / 4`: for `U = S ⊔ ℝ ∙ f`, the MGF
`(1 - 2 / 4) ^ (-dim U / 2) = 2 ^ (dim U / 2)` is bounded by `exp (dim S + 1)`, so shifting by
`4 * (dim S + 1 + log (1 / π))` bounds the expectation by `π`. -/
private theorem lintegral_exp_norm_sq_starProjection_sup_span_le [MeasurableSpace E] [BorelSpace E]
    (S : Submodule ℝ E) (f : E) {π : ℝ} (hπ : 0 < π) :
    ∫⁻ ξ, ENNReal.ofReal (Real.exp ((‖(S ⊔ Submodule.span ℝ {f}).starProjection ξ‖ ^ 2 -
        4 * (Module.finrank ℝ S + 1 + Real.log (1 / π))) / 4)) ∂stdGaussian E ≤
      ENNReal.ofReal π := by
  let U : Submodule ℝ E := S ⊔ Submodule.span ℝ {f}
  let t : ℝ := 4 * (Module.finrank ℝ S + 1 + Real.log (1 / π))
  have hU_dim : Module.finrank ℝ U ≤ Module.finrank ℝ S + 1 := by
    have := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {f})
    have hspan : Module.finrank ℝ (Submodule.span ℝ ({f} : Set E)) ≤ 1 := by
      by_cases hf : f = 0
      · rw [hf, Submodule.span_zero_singleton, finrank_bot]; exact Nat.zero_le 1
      · rw [finrank_span_singleton hf]
    dsimp only [U]; omega
  -- Factor out `exp (-t / 4)` and evaluate the Gaussian projection MGF at `1 / 4`.
  have hfact (ξ : E) : Real.exp ((‖U.starProjection ξ‖ ^ 2 - t) / 4) =
      Real.exp (-t / 4) * Real.exp ((1 / 4 : ℝ) * ‖U.starProjection ξ‖ ^ 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have hint : Integrable (fun ξ ↦ Real.exp ((‖U.starProjection ξ‖ ^ 2 - t) / 4)) (stdGaussian E) :=
    ((U.integrable_exp_mul_norm_sq_starProjection_stdGaussian (t := 1 / 4)
      (by norm_num)).const_mul _).congr (.of_forall fun ξ ↦ (hfact ξ).symm)
  rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (Real.exp_pos _).le)]
  refine ENNReal.ofReal_le_ofReal ?_
  simp_rw [hfact]; rw [integral_const_mul]
  have hmgf := U.mgf_norm_sq_starProjection_stdGaussian (t := 1 / 4) (by norm_num)
  simp only [mgf] at hmgf; rw [hmgf]
  -- Bound `(1 - 2 * (1 / 4)) ^ (-(k / 2)) = 2 ^ (k / 2) ≤ e ^ k` and cancel with `exp (-t / 4)`.
  set k : ℝ := (Module.finrank ℝ U : ℝ)
  have hpow : (1 - 2 * (1 / 4 : ℝ)) ^ (-(k / 2)) ≤ Real.exp k := by
    have hhalf : 1 - 2 * (1 / 4 : ℝ) = (2 : ℝ)⁻¹ := by norm_num
    rw [hhalf, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
    calc (2 : ℝ) ^ (k / 2) ≤ (Real.exp 1) ^ (k / 2) :=
        Real.rpow_le_rpow (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) (by positivity)
      _ = Real.exp (k / 2) := by rw [← Real.exp_mul, one_mul]
      _ ≤ Real.exp k := Real.exp_le_exp.mpr
          (by linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ U)])
  have hexp_t : Real.exp (-t / 4) = Real.exp (-((Module.finrank ℝ S : ℝ) + 1)) * π := by
    have : -t / 4 = -((Module.finrank ℝ S : ℝ) + 1) + Real.log π := by
      simp only [t, one_div, Real.log_inv]; ring
    rw [this, Real.exp_add, Real.exp_log hπ]
  have hdim_le : k ≤ Module.finrank ℝ S + 1 := by simpa [k] using (Nat.cast_le (α := ℝ)).mpr hU_dim
  calc Real.exp (-t / 4) * (1 - 2 * (1 / 4 : ℝ)) ^ (-(k / 2))
      ≤ Real.exp (-t / 4) * Real.exp k := mul_le_mul_of_nonneg_left hpow (Real.exp_pos _).le
    _ = Real.exp (-((Module.finrank ℝ S : ℝ) + 1) + k) * π := by
        rw [hexp_t, mul_right_comm, ← Real.exp_add]
    _ ≤ 1 * π := mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (by linarith)) hπ.le
    _ = π := one_mul _

/-- Auxiliary supremum majorant `W(ξ) = 4 * ∑' m, exp ((Z m ξ - t m) / 4)` dominating all shifted
chi-squared projections `‖(S m ⊔ ℝ ∙ f).starProjection ξ‖ ^ 2`. -/
private theorem exists_majorant_sup_starProjection [MeasurableSpace E] [BorelSpace E]
    {M : Type*} [Countable M] (S : M → Submodule ℝ E) (π : M → ℝ) (f : E)
    (hπ : ∀ m, 0 < π m) (hsum : Summable π) :
    ∃ W : E → ℝ, Measurable W ∧ (∀ ξ, 0 ≤ W ξ) ∧ Integrable W (stdGaussian E) ∧
      (∫ ξ, W ξ ∂stdGaussian E ≤ 4 * ∑' m, π m) ∧
      (∀ᵐ ξ ∂stdGaussian E, ∀ m : M, ‖(S m ⊔ Submodule.span ℝ {f}).starProjection ξ‖ ^ 2 ≤
        4 * (Module.finrank ℝ (S m) + 1 + Real.log (1 / π m)) + W ξ) := by
  let U : M → Submodule ℝ E := fun m ↦ S m ⊔ Submodule.span ℝ {f}
  let t : M → ℝ := fun m ↦ 4 * (Module.finrank ℝ (S m) + 1 + Real.log (1 / π m))
  let F : M → E → ℝ≥0∞ := fun m ξ ↦
    ENNReal.ofReal (Real.exp ((‖(U m).starProjection ξ‖ ^ 2 - t m) / 4))
  let Wₑ : E → ℝ≥0∞ := fun ξ ↦ 4 * ∑' m : M, F m ξ
  have hF_meas (m : M) : Measurable (F m) := by fun_prop
  have hWₑ_meas : Measurable Wₑ := Measurable.const_mul (Measurable.tsum hF_meas) 4
  -- Sum the per-model MGF bounds via Tonelli to control `∫⁻ Wₑ` by `4 * ∑' m, π m`.
  have hlint_le : ∫⁻ ξ, Wₑ ξ ∂stdGaussian E ≤ ENNReal.ofReal (4 * ∑' m, π m) := by
    dsimp only [Wₑ]
    rw [lintegral_const_mul _ (Measurable.tsum hF_meas),
      lintegral_tsum fun m ↦ (hF_meas m).aemeasurable]
    calc 4 * ∑' m, ∫⁻ ξ, F m ξ ∂stdGaussian E ≤ 4 * ∑' m, ENNReal.ofReal (π m) := by
          gcongr with m; exact lintegral_exp_norm_sq_starProjection_sup_span_le (S m) f (hπ m)
      _ = 4 * ENNReal.ofReal (∑' m, π m) := by
          rw [ENNReal.ofReal_tsum_of_nonneg (fun m ↦ (hπ m).le) hsum]
      _ = ENNReal.ofReal (4 * ∑' m, π m) := by
          rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hlint_lt : ∫⁻ ξ, Wₑ ξ ∂stdGaussian E < ⊤ := hlint_le.trans_lt ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ ξ ∂stdGaussian E, Wₑ ξ ≠ ⊤ :=
    (ae_lt_top hWₑ_meas hlint_lt.ne).mono fun _ h ↦ h.ne
  have hW_int : Integrable (fun ξ ↦ (Wₑ ξ).toReal) (stdGaussian E) :=
    integrable_toReal_of_lintegral_ne_top hWₑ_meas.aemeasurable hlint_lt.ne
  refine ⟨fun ξ ↦ (Wₑ ξ).toReal, hWₑ_meas.ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, hW_int, ?_, ?_⟩
  · rw [← ENNReal.ofReal_le_ofReal_iff (mul_nonneg (by norm_num) (tsum_nonneg fun m ↦ (hπ m).le)),
      ofReal_integral_eq_lintegral_ofReal hW_int (.of_forall fun _ ↦ ENNReal.toReal_nonneg)]
    exact (lintegral_congr_ae (hae_fin.mono fun _ h ↦ ENNReal.ofReal_toReal h)).le.trans hlint_le
  · -- Use `u ≤ exp u` on `u = (‖P_{U m} ξ‖ ^ 2 - t m) / 4` to dominate every model simultaneously.
    refine hae_fin.mono fun ξ hξ m ↦ ?_
    set u : ℝ := (‖(U m).starProjection ξ‖ ^ 2 - t m) / 4
    have hu : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have hterm_le : ENNReal.ofReal (4 * Real.exp u) ≤ Wₑ ξ := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
      exact mul_le_mul_right (le_tsum (fun m' ↦ F m' ξ) m) 4
    have h4 : 4 * Real.exp u ≤ (Wₑ ξ).toReal := by
      simpa only [ENNReal.toReal_ofReal (by positivity : 0 ≤ 4 * Real.exp u)] using
        ENNReal.toReal_mono hξ hterm_le
    have hu4 : ‖(U m).starProjection ξ‖ ^ 2 - t m = 4 * u := by dsimp only [u]; ring
    linarith

/-- Cauchy–Schwarz and Young's inequality on `S ⊔ ℝ ∙ f` bound the noise cross term
`2 * σ * ⟪g - f, ξ⟫` for `g ∈ S` by
`4 / κ * ‖g - f‖ ^ 2 + κ / 4 * σ ^ 2 * ‖P_{S ⊔ ℝ ∙ f} ξ‖ ^ 2`. -/
private theorem two_mul_inner_sub_le_starProjection {S : Submodule ℝ E} {g f ξ : E}
    (hg : g ∈ S) {κ : ℝ} (σ : ℝ) (hκ : 0 < κ) :
    2 * σ * ⟪g - f, ξ⟫ ≤
      4 / κ * ‖g - f‖ ^ 2 +
        κ / 4 * σ ^ 2 * ‖(S ⊔ Submodule.span ℝ {f}).starProjection ξ‖ ^ 2 := by
  set U : Submodule ℝ E := S ⊔ Submodule.span ℝ {f}
  have hmemU : g - f ∈ U := U.sub_mem (Submodule.mem_sup_left hg)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
  have hinner : ⟪g - f, ξ⟫ = ⟪g - f, U.starProjection ξ⟫ := by
    rw [← U.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hmemU]
  rw [hinner]
  have habs : σ * ⟪g - f, U.starProjection ξ⟫ ≤ |σ| * (‖g - f‖ * ‖U.starProjection ξ‖) :=
    (le_abs_self _).trans <| by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg σ)
  have hsq : 0 ≤ (4 * ‖g - f‖ - κ * |σ| * ‖U.starProjection ξ‖) ^ 2 / (4 * κ) := by positivity
  have hsq_exp : (4 * ‖g - f‖ - κ * |σ| * ‖U.starProjection ξ‖) ^ 2 / (4 * κ) =
      4 / κ * ‖g - f‖ ^ 2 - 2 * |σ| * (‖g - f‖ * ‖U.starProjection ξ‖) +
        κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 := by
    have := hκ.ne'; field_simp; rw [← sq_abs σ]; ring
  linarith

/-- Pointwise comparison inequality at an observation `Y = f + σ • ξ` between the selected model
`mh Y` and any competitor model `m`, given the quadratic projection bound on `U (mh Y)`. -/
private theorem penalized_pointwise_bound {M : Type*} (S : M → Submodule ℝ E) (π pen : M → ℝ)
    {κ σ : ℝ} (f : E) (mh : E → M) (hκ : 4 < κ) (hdim : 0 < Module.finrank ℝ E)
    (hpen : ∀ m, κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) /
      Module.finrank ℝ E ≤ pen m)
    (hmin : ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m)
    {ξ : E} {w : ℝ}
    (hw : ‖(S (mh (f + σ • ξ)) ⊔ Submodule.span ℝ {f}).starProjection ξ‖ ^ 2 ≤
      4 * (Module.finrank ℝ (S (mh (f + σ • ξ))) + 1 + Real.log (1 / π (mh (f + σ • ξ)))) + w)
    (m : M) :
    (κ - 4) / κ * (‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 /
        Module.finrank ℝ E) ≤
      ‖f - (S m).starProjection f‖ ^ 2 / Module.finrank ℝ E + pen m +
        κ * σ ^ 2 / Module.finrank ℝ E +
        κ / 4 * σ ^ 2 * w / Module.finrank ℝ E +
        2 * σ * ⟪f - (S m).starProjection f, ξ⟫ / Module.finrank ℝ E := by
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hdim
  set Y : E := f + σ • ξ
  set mhY : M := mh Y
  set fhat : E := (S mhY).starProjection Y
  set fm : E := (S m).starProjection f
  -- 1. Empirical optimality of `mhY` and projection minimality `‖Y - P_{S m} Y‖ ≤ ‖Y - P_{S m} f‖`.
  have hproj_min : ‖Y - (S m).starProjection Y‖ ^ 2 ≤ ‖Y - fm‖ ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _)
      ((S m).norm_sub_starProjection_le_of_mem Y ((S m).starProjection_apply_mem f)) 2
  have hopt : ‖Y - fhat‖ ^ 2 + n * pen mhY ≤ ‖Y - fm‖ ^ 2 + n * pen m := by
    have h1 : ‖Y - fhat‖ ^ 2 / n + pen mhY ≤ ‖Y - fm‖ ^ 2 / n + pen m := by
      have h := hmin Y m
      rw [penalizedCriterion_def, penalizedCriterion_def] at h
      exact h.trans (add_le_add (div_le_div_of_nonneg_right hproj_min hn.le) le_rfl)
    have h2 := mul_le_mul_of_nonneg_left h1 hn.le
    rwa [mul_add, mul_add, mul_div_cancel₀ _ hn.ne', mul_div_cancel₀ _ hn.ne'] at h2
  -- 2. Expand `‖Y - fhat‖ ^ 2` and `‖Y - fm‖ ^ 2` around `f` to cancel `σ ^ 2 * ‖ξ‖ ^ 2`.
  have hexp1 : ‖Y - fhat‖ ^ 2 =
      ‖fhat - f‖ ^ 2 - 2 * σ * ⟪fhat - f, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2 := by
    have heq : Y - fhat = σ • ξ - (fhat - f) := by simp only [Y]; abel
    rw [heq, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_comm]; ring
  have hexp2 : ‖Y - fm‖ ^ 2 = ‖f - fm‖ ^ 2 + 2 * σ * ⟪f - fm, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2 := by
    have heq : Y - fm = (f - fm) + σ • ξ := by simp only [Y]; abel
    rw [heq, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]; ring
  -- 3. Absorb `2 * σ * ⟪fhat - f, ξ⟫` via Young's inequality and the penalty lower bound `hpen`.
  have hyoung := two_mul_inner_sub_le_starProjection (f := f) (ξ := ξ)
    ((S mhY).starProjection_apply_mem Y) σ (by linarith : 0 < κ)
  have hpen_mh : κ * σ ^ 2 * (Module.finrank ℝ (S mhY) + Real.log (1 / π mhY)) ≤ n * pen mhY := by
    have := (div_le_iff₀ hn).mp (hpen mhY); linarith
  have hw_scaled := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ κ / 4 * σ ^ 2)
  have hcomb : (κ - 4) / κ * ‖fhat - f‖ ^ 2 ≤
      ‖f - fm‖ ^ 2 + n * pen m + κ * σ ^ 2 + κ / 4 * σ ^ 2 * w + 2 * σ * ⟪f - fm, ξ⟫ := by
    have : κ ≠ 0 := by linarith
    have hcoeff : (κ - 4) / κ * ‖fhat - f‖ ^ 2 = ‖fhat - f‖ ^ 2 - 4 / κ * ‖fhat - f‖ ^ 2 := by
      field_simp
    linarith
  have hdiv := div_le_div_of_nonneg_right hcomb hn.le
  have : n ≠ 0 := hn.ne'
  rw [← mul_div_assoc]
  exact hdiv.trans_eq (by field_simp)

/-! ### Integrability and oracle inequality -/

private theorem integrable_rhs [MeasurableSpace E] [BorelSpace E]
    (U : Submodule ℝ E) {W : E → ℝ} (hW : Integrable W (stdGaussian E)) (penm κ σ n : ℝ) (f : E) :
    Integrable (fun ξ : E ↦
      ‖f - U.starProjection f‖ ^ 2 / n + penm + κ * σ ^ 2 / n + κ / 4 * σ ^ 2 * W ξ / n +
        2 * σ * ⟪f - U.starProjection f, ξ⟫ / n) (stdGaussian E) :=
  ((integrable_const _).add ((hW.const_mul _).div_const n)).add
    ((((innerSL ℝ (f - U.starProjection f)).integrable_comp
      IsGaussian.integrable_id).const_mul _).div_const n)

private theorem integral_rhs_le [MeasurableSpace E] [BorelSpace E]
    (U : Submodule ℝ E) {W : E → ℝ} (hW : Integrable W (stdGaussian E))
    {s : ℝ} (hW_le : ∫ ξ, W ξ ∂stdGaussian E ≤ 4 * s)
    (penm κ σ : ℝ) (hκ : 0 ≤ κ) {n : ℝ} (hn : 0 < n) (f : E) :
    ∫ ξ : E, (‖f - U.starProjection f‖ ^ 2 / n + penm + κ * σ ^ 2 / n +
        κ / 4 * σ ^ 2 * W ξ / n + 2 * σ * ⟪f - U.starProjection f, ξ⟫ / n) ∂stdGaussian E ≤
      (‖f - U.starProjection f‖ ^ 2 / n + penm) + κ * (1 + s) * σ ^ 2 / n := by
  have h1 : Integrable (fun _ : E ↦ ‖f - U.starProjection f‖ ^ 2 / n + penm + κ * σ ^ 2 / n)
      (stdGaussian E) := integrable_const _
  have h2 : Integrable (fun ξ : E ↦ κ / 4 * σ ^ 2 * W ξ / n) (stdGaussian E) :=
    (hW.const_mul _).div_const n
  have h12 : Integrable
      (fun ξ : E ↦ ‖f - U.starProjection f‖ ^ 2 / n + penm + κ * σ ^ 2 / n +
        κ / 4 * σ ^ 2 * W ξ / n) (stdGaussian E) := h1.add h2
  have h3 : Integrable (fun ξ : E ↦ 2 * σ * ⟪f - U.starProjection f, ξ⟫ / n) (stdGaussian E) :=
    (((innerSL ℝ (f - U.starProjection f)).integrable_comp
      IsGaussian.integrable_id).const_mul _).div_const n
  have hzero : ∫ a, ⟪f - U.starProjection f, a⟫ ∂stdGaussian E = 0 :=
    integral_strongDual_stdGaussian (innerSL ℝ (f - U.starProjection f))
  rw [integral_add h12 h3, integral_add h1 h2, integral_const, probReal_univ, one_smul,
    integral_div, integral_div, integral_const_mul, integral_const_mul, hzero, mul_zero, zero_div,
    add_zero]
  have hW_scaled : κ / 4 * σ ^ 2 * (∫ ξ, W ξ ∂stdGaussian E) / n ≤ κ * s * σ ^ 2 / n :=
    (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hW_le (by positivity : 0 ≤ κ / 4 * σ ^ 2)) hn.le).trans_eq
      (by ring)
  linarith [show ‖f - U.starProjection f‖ ^ 2 / n + penm + κ * σ ^ 2 / n + κ * s * σ ^ 2 / n =
      (‖f - U.starProjection f‖ ^ 2 / n + penm) + κ * (1 + s) * σ ^ 2 / n by ring]

/-- Under the Birgé–Massart penalty condition with `κ > 4`, the squared estimation error
`‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2` of any measurable minimizer `mh` is
integrable under `stdGaussian E`. Neither `σ > 0`, `∑' m, π m ≤ 1`, nor `Nontrivial E` is
needed. -/
theorem integrable_sq_norm_starProjection_sub [MeasurableSpace E] [BorelSpace E]
    {M : Type*} [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (S : M → Submodule ℝ E) (π pen : M → ℝ) {κ : ℝ} (σ : ℝ) (f : E) (mh : E → M)
    (hκ : 4 < κ) (hπ : ∀ m, 0 < π m) (hsum : Summable π)
    (hpen : ∀ m, κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) /
      Module.finrank ℝ E ≤ pen m)
    (hmh : Measurable mh)
    (hmin : ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m) :
    Integrable (fun ξ ↦ ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2)
      (stdGaussian E) := by
  by_cases hdim : Module.finrank ℝ E = 0
  · have : Subsingleton E := Module.finrank_zero_iff.mp hdim
    refine (integrable_const (0 : ℝ)).congr (.of_forall fun ξ ↦ ?_)
    dsimp only; rw [Subsingleton.elim ((S (mh (f + σ • ξ))).starProjection _) f]; simp
  -- Dominate the squared error almost everywhere by `penalized_pointwise_bound` at `m₀ = mh 0`.
  have hdim_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hdim_pos
  obtain ⟨W, _, _, hW_int, _, hW_ae⟩ := exists_majorant_sup_starProjection S π f hπ hsum
  let m₀ : M := mh 0
  set c : ℝ := κ / (κ - 4) * n
  have hκ4 : 0 < κ - 4 := by linarith
  have hc_pos : 0 < c := by positivity
  have hproj_meas : Measurable fun Y : E ↦ (S (mh Y)).starProjection Y := by
    simpa only [Function.comp_def, id_eq] using
      (measurable_from_prod_countable_left (f := fun p : E × M ↦ (S p.2).starProjection p.1)
        fun m ↦ (S m).starProjection.continuous.measurable).comp (measurable_id.prodMk hmh)
  have hshift : Measurable fun ξ : E ↦ (S (mh (f + σ • ξ))).starProjection (f + σ • ξ) := by
    simpa only [Function.comp_def] using
      hproj_meas.comp (by fun_prop : Measurable fun ξ : E ↦ f + σ • ξ)
  refine Integrable.mono' ((integrable_rhs (S m₀) hW_int (pen m₀) κ σ n f).const_mul c)
    ((hshift.sub measurable_const).norm.pow_const 2).aestronglyMeasurable ?_
  filter_upwards [hW_ae] with ξ hξ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hpt := mul_le_mul_of_nonneg_left (penalized_pointwise_bound S π pen f mh hκ hdim_pos
    hpen hmin (hξ (mh (f + σ • ξ))) m₀) hc_pos.le
  have : c * ((κ - 4) / κ *
      (‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n)) =
      ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 := by
    have : κ ≠ 0 := by linarith
    have : κ - 4 ≠ 0 := hκ4.ne'
    have : n ≠ 0 := hn.ne'
    simp only [c]; field_simp
  linarith

/-- **Oracle inequality for penalized model selection** (Birgé–Massart; Giraud, Theorem 2.2):
for `κ > 4`, positive summable weights `π`, and any measurable minimizer `mh` of
`penalizedCriterion S pen Y`,
`𝔼 ‖f̂ - f‖ ^ 2 / n ≤ (κ / (κ - 4)) * (⨅ m, (‖f - P_{S_m} f‖ ^ 2 / n + pen m) +`
`κ * (1 + ∑' m, π m) * σ ^ 2 / n)`.
The leading constant `κ / (κ - 4)` approaches `1` as `κ → ∞`. Neither `σ > 0`, `∑' m, π m ≤ 1`,
nor `Nontrivial E` is required. -/
theorem penalized_model_selection [MeasurableSpace E] [BorelSpace E]
    {M : Type*} [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (S : M → Submodule ℝ E) (π pen : M → ℝ) {κ : ℝ} (σ : ℝ) (f : E) (mh : E → M)
    (hκ : 4 < κ) (hπ : ∀ m, 0 < π m) (hsum : Summable π)
    (hpen : ∀ m, κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) /
      Module.finrank ℝ E ≤ pen m)
    (hmh : Measurable mh)
    (hmin : ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m) :
    ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / Module.finrank ℝ E
        ∂stdGaussian E ≤
      κ / (κ - 4) *
        ((⨅ m, (‖f - (S m).starProjection f‖ ^ 2 / Module.finrank ℝ E + pen m)) +
          κ * (1 + ∑' m, π m) * σ ^ 2 / Module.finrank ℝ E) := by
  have hκ4 : 0 < κ - 4 := by linarith
  by_cases hdim : Module.finrank ℝ E = 0
  · simp only [hdim, Nat.cast_zero, div_zero, integral_zero, zero_add, add_zero]
    exact mul_nonneg (by positivity) (Real.iInf_nonneg fun m ↦ by simpa [hdim] using hpen m)
  have hdim_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hdim_pos
  have : Nonempty M := ⟨mh 0⟩
  have hg_int := (integrable_sq_norm_starProjection_sub S π pen σ f mh hκ hπ hsum hpen hmh
    hmin).div_const n
  obtain ⟨W, _, _, hW_int, hW_le, hW_ae⟩ := exists_majorant_sup_starProjection S π f hπ hsum
  -- Integrate `penalized_pointwise_bound` against `stdGaussian E` for each fixed competitor `m`,
  -- then take the infimum over `m` and multiply by `κ / (κ - 4)`.
  have hbound (m : M) :
      (κ - 4) / κ *
          ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n ∂stdGaussian E ≤
        (‖f - (S m).starProjection f‖ ^ 2 / n + pen m) + κ * (1 + ∑' m', π m') * σ ^ 2 / n := by
    rw [← integral_const_mul]
    exact (integral_mono_ae (hg_int.const_mul ((κ - 4) / κ))
      (integrable_rhs (S m) hW_int (pen m) κ σ n f)
      (hW_ae.mono fun ξ hξ ↦ penalized_pointwise_bound S π pen f mh hκ hdim_pos hpen hmin
        (hξ (mh (f + σ • ξ))) m)).trans
      (integral_rhs_le (S m) hW_int hW_le (pen m) κ σ (by linarith) hn f)
  have hstep :
      (κ - 4) / κ * ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n
          ∂stdGaussian E - κ * (1 + ∑' m', π m') * σ ^ 2 / n ≤
        ⨅ m, (‖f - (S m).starProjection f‖ ^ 2 / n + pen m) :=
    le_ciInf fun m ↦ sub_le_iff_le_add.mpr (hbound m)
  have hmul := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mp hstep)
    (by positivity : 0 ≤ κ / (κ - 4))
  have hcancel : κ / (κ - 4) * ((κ - 4) / κ) = 1 := by
    have : κ ≠ 0 := by linarith
    have : κ - 4 ≠ 0 := hκ4.ne'
    field_simp
  rwa [← mul_assoc, hcancel, one_mul] at hmul

end TauCeti
