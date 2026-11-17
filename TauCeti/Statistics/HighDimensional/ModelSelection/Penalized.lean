/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Logic.Encodable.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.Filter.Cofinite
import Mathlib.Probability.Distributions.Gaussian.Fernique
import TauCeti.Probability.Distributions.Gaussian.Projection

/-!
# Penalized model selection in the Gaussian regression model

Given a finite-dimensional real inner product space `E` of dimension `n = Module.finrank ℝ E` and a
countable family of linear models `(S m)_{m : M}`, the penalized empirical-risk criterion at an
observation `Y : E` with penalty `pen : M → ℝ` is

`penalizedCriterion S pen Y m = ‖Y - (S m).starProjection Y‖ ^ 2 / n + pen m`.

We prove two main results for Gaussian regression `Y = f + σ • ξ` with `ξ ~ stdGaussian E`:

1. **Existence of a measurable selector** (`exists_measurable_penalizedSelector_of_tendsto` and
   `exists_measurable_penalizedSelector`): whenever `pen` tends to `+∞` along the cofinite filter
   (in particular whenever `pen m ≥ κ * σ ^ 2 * (dim (S m) + log (1 / π m)) / n` for positive
   summable weights `π`, `κ > 0`, `σ ≠ 0`, and `Nontrivial E`), a measurable minimizer `mh : E → M`
   of `penalizedCriterion S pen Y` exists. Selecting the minimizer of smallest code under an
   encoding of `M` yields measurability for any `MeasurableSpace M` without assuming
   `MeasurableSingletonClass M`.
2. **Oracle inequality** (`integrable_sq_norm_starProjection_sub` and `penalized_model_selection`):
   for `κ > 4` and any measurable minimizer `mh`, the squared estimation error
   `‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2` is integrable and satisfies
   `𝔼 ‖f̂ - f‖ ^ 2 / n ≤ (κ / (κ - 4)) * (⨅ m, (‖f - P_{S_m} f‖ ^ 2 / n + pen m) +`
   `κ * (1 + ∑' m, π m) * σ ^ 2 / n)`.
   The leading constant `κ / (κ - 4)` approaches `1` as `κ → ∞`, and no assumptions `σ > 0`,
   `∑' m, π m ≤ 1`, or `Nontrivial E` are required.

The proof controls the chi-squared projections `‖(S m' ⊔ ℝ ∙ f).starProjection ξ‖ ^ 2` through the
exponential moment at rate `1 / 4`, avoiding Gaussian concentration while still achieving the sharp
threshold `κ₀ = 4`.

## Main definitions

* `TauCeti.penalizedCriterion`: the penalized empirical least-squares objective
  `‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m`.

## Main results

* `TauCeti.exists_measurable_penalizedSelector_of_tendsto`: a measurable minimizer exists whenever
  `Filter.Tendsto pen Filter.cofinite Filter.atTop`.
* `TauCeti.exists_measurable_penalizedSelector`: specialization to Birgé–Massart penalties
  `κ * σ ^ 2 * (dim (S m) + log (1 / π m)) / n`.
* `TauCeti.measurable_starProjection_apply`: measurability of `Y ↦ (S (mh Y)).starProjection Y`.
* `TauCeti.integrable_sq_norm_starProjection_sub`: integrability of the squared estimation error.
* `TauCeti.penalized_model_selection`: the Birgé–Massart / Giraud oracle inequality with `κ₀ = 4`.

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
`‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m`. When
`E = EuclideanSpace ℝ (Fin n)`, `Module.finrank ℝ E = n`. -/
def penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) : ℝ :=
  ‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m

/-- Unfolding lemma for `penalizedCriterion`. -/
theorem penalizedCriterion_def {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) :
    penalizedCriterion S pen Y m =
      ‖Y - (S m).starProjection Y‖ ^ 2 / Module.finrank ℝ E + pen m :=
  (rfl)

/-- If the observation `Y` already lies in `S m`, the penalized criterion reduces to `pen m`. -/
theorem penalizedCriterion_of_mem {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) {Y : E}
    {m : M} (hY : Y ∈ S m) :
    penalizedCriterion S pen Y m = pen m := by
  rw [penalizedCriterion_def, Submodule.starProjection_eq_self_iff.mpr hY, sub_self, norm_zero,
    zero_pow two_ne_zero, zero_div, zero_add]

/-- At the zero subspace `S m = ⊥`, the penalized criterion is
`‖Y‖ ^ 2 / Module.finrank ℝ E + pen m`. -/
theorem penalizedCriterion_of_eq_bot {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E)
    {m : M} (h : S m = ⊥) :
    penalizedCriterion S pen Y m = ‖Y‖ ^ 2 / Module.finrank ℝ E + pen m := by
  simp [penalizedCriterion_def, h]

/-- At the full space `S m = ⊤`, the penalized criterion is `pen m`. -/
theorem penalizedCriterion_of_eq_top {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E)
    {m : M} (h : S m = ⊤) :
    penalizedCriterion S pen Y m = pen m :=
  penalizedCriterion_of_mem S pen (h.symm ▸ Submodule.mem_top)

/-- The penalty lower-bounds the penalized criterion. -/
theorem le_penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (Y : E) (m : M) :
    pen m ≤ penalizedCriterion S pen Y m := by
  rw [penalizedCriterion_def]
  exact le_add_of_nonneg_left (by positivity)

/-- For each model `m`, the penalized criterion depends continuously on the observation `Y`. -/
@[fun_prop]
theorem continuous_penalizedCriterion {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (m : M) :
    Continuous fun Y ↦ penalizedCriterion S pen Y m := by
  unfold penalizedCriterion
  fun_prop

/-- For each model `m`, the penalized criterion is measurable in the observation `Y`. -/
@[fun_prop]
theorem measurable_penalizedCriterion [MeasurableSpace E] [OpensMeasurableSpace E]
    {M : Type*} (S : M → Submodule ℝ E) (pen : M → ℝ) (m : M) :
    Measurable fun Y ↦ penalizedCriterion S pen Y m :=
  (continuous_penalizedCriterion S pen m).measurable

/-! ### Existence of a measurable selector -/

/-- If `pen` tends to `+∞` along the cofinite filter on a countable nonempty index type `M`, then
`penalizedCriterion S pen Y` admits a measurable minimizer `mh : E → M`. No
`MeasurableSingletonClass M` assumption is needed: because `M` is countable, preimages of arbitrary
subsets are countable unions of singletons. -/
theorem exists_measurable_penalizedSelector_of_tendsto [MeasurableSpace E]
    [OpensMeasurableSpace E] {M : Type*} [Countable M] [Nonempty M] [MeasurableSpace M]
    (S : M → Submodule ℝ E) (pen : M → ℝ) (hpen : Tendsto pen cofinite atTop) :
    ∃ mh : E → M, Measurable mh ∧
      ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m := by
  classical
  let e : Encodable M := Encodable.ofCountable M
  have hex (Y : E) :
      ∃ k : ℕ, ∃ m : M, e.encode m = k ∧
        ∀ m', penalizedCriterion S pen Y m ≤ penalizedCriterion S pen Y m' := by
    have hcrit : Tendsto (penalizedCriterion S pen Y) cofinite atTop :=
      tendsto_atTop_mono (le_penalizedCriterion S pen Y) hpen
    obtain ⟨m, hm⟩ := hcrit.exists_forall_le
    exact ⟨e.encode m, m, rfl, hm⟩
  let mh : E → M := fun Y ↦ Classical.choose (Nat.find_spec (hex Y))
  have hmh_enc (Y : E) : e.encode (mh Y) = Nat.find (hex Y) :=
    (Classical.choose_spec (Nat.find_spec (hex Y))).1
  have hmh_min (Y : E) (m' : M) :
      penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m' :=
    (Classical.choose_spec (Nat.find_spec (hex Y))).2 m'
  have hchar (Y : E) (m : M) :
      mh Y = m ↔
        (∀ m', penalizedCriterion S pen Y m ≤ penalizedCriterion S pen Y m') ∧
        (∀ m', e.encode m' < e.encode m →
          penalizedCriterion S pen Y m < penalizedCriterion S pen Y m') := by
    constructor
    · rintro rfl
      refine ⟨hmh_min Y, fun m' hlt ↦ lt_of_not_ge fun hle ↦ ?_⟩
      have hm'_min : ∀ m'', penalizedCriterion S pen Y m' ≤ penalizedCriterion S pen Y m'' :=
        fun m'' ↦ hle.trans (hmh_min Y m'')
      have hfind : Nat.find (hex Y) ≤ e.encode m' := Nat.find_min' (hex Y) ⟨m', rfl, hm'_min⟩
      have := hmh_enc Y
      omega
    · rintro ⟨hm_min, hm_lt⟩
      have hfind : Nat.find (hex Y) ≤ e.encode m := Nat.find_min' (hex Y) ⟨m, rfl, hm_min⟩
      have heq : e.encode (mh Y) = e.encode m := by
        refine le_antisymm (hmh_enc Y ▸ hfind) (le_of_not_gt fun hlt ↦ ?_)
        exact not_le_of_gt (hm_lt (mh Y) hlt) (hmh_min Y m)
      exact e.encode_injective heq
  refine ⟨mh, fun s _ ↦ ?_, hmh_min⟩
  have hsingle (m : M) : MeasurableSet (mh ⁻¹' {m}) := by
    have hset : mh ⁻¹' {m} =
        (⋂ m' : M, {Y | penalizedCriterion S pen Y m ≤ penalizedCriterion S pen Y m'}) ∩
        (⋂ (m' : M) (_ : e.encode m' < e.encode m),
          {Y | penalizedCriterion S pen Y m < penalizedCriterion S pen Y m'}) := by
      ext Y
      simp [hchar Y m]
    rw [hset]
    refine MeasurableSet.inter (MeasurableSet.iInter fun m' ↦ ?_)
      (MeasurableSet.iInter fun m' ↦ MeasurableSet.iInter fun _ ↦ ?_)
    · exact measurableSet_le (measurable_penalizedCriterion S pen m)
        (measurable_penalizedCriterion S pen m')
    · exact measurableSet_lt (measurable_penalizedCriterion S pen m)
        (measurable_penalizedCriterion S pen m')
  have hpre : mh ⁻¹' s = ⋃ m ∈ s, mh ⁻¹' {m} := by
    ext Y
    simp
  rw [hpre]
  exact MeasurableSet.biUnion s.to_countable fun m _ ↦ hsingle m

/-- A measurable selector of a minimizer of the penalized criterion exists when `E` is nontrivial,
`κ > 0`, `σ ≠ 0`, `π` is positive and summable, and the penalty dominates
`κ * σ ^ 2 * (dim (S m) + log (1 / π m)) / Module.finrank ℝ E`. No assumption `∑' m, π m ≤ 1` or
`MeasurableSingletonClass M` is needed. -/
theorem exists_measurable_penalizedSelector [Nontrivial E] [MeasurableSpace E]
    [OpensMeasurableSpace E] {M : Type*} [Countable M] [Nonempty M] [MeasurableSpace M]
    (S : M → Submodule ℝ E) (π pen : M → ℝ) {κ σ : ℝ} (hκ : 0 < κ) (hσ : σ ≠ 0)
    (hπ : ∀ m, 0 < π m) (hsum : Summable π)
    (hpen : ∀ m, κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) /
      Module.finrank ℝ E ≤ pen m) :
    ∃ mh : E → M, Measurable mh ∧
      ∀ Y m, penalizedCriterion S pen Y (mh Y) ≤ penalizedCriterion S pen Y m := by
  apply exists_measurable_penalizedSelector_of_tendsto S pen
  rw [tendsto_atTop]
  intro C
  have hdim : (0 : ℝ) < Module.finrank ℝ E := Nat.cast_pos.mpr Module.finrank_pos
  have hc : 0 < κ * σ ^ 2 / Module.finrank ℝ E := by positivity
  set ε : ℝ := Real.exp (-((Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2)))
  have hε : 0 < ε := Real.exp_pos _
  have hev : ∀ᶠ m in cofinite, π m < ε :=
    hsum.tendsto_cofinite_zero.eventually (Iio_mem_nhds hε)
  refine hev.mono fun m hm ↦ ?_
  have hlog : Real.log (π m) < -((Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2)) := by
    have := Real.log_lt_log (hπ m) hm
    rwa [Real.log_exp] at this
  have hlog_inv : (Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2) < Real.log (1 / π m) := by
    rw [one_div, Real.log_inv]
    linarith
  have h1 : C ≤ κ * σ ^ 2 * Real.log (1 / π m) / Module.finrank ℝ E := by
    have hmul := mul_le_mul_of_nonneg_left hlog_inv.le hc.le
    have hlhs : κ * σ ^ 2 / Module.finrank ℝ E *
        ((Module.finrank ℝ E : ℝ) * C / (κ * σ ^ 2)) = C := by
      have : (Module.finrank ℝ E : ℝ) ≠ 0 := hdim.ne'
      have : κ * σ ^ 2 ≠ 0 := by positivity
      field_simp
    have hrhs : κ * σ ^ 2 / Module.finrank ℝ E * Real.log (1 / π m) =
        κ * σ ^ 2 * Real.log (1 / π m) / Module.finrank ℝ E := by ring
    linarith
  have h2 : κ * σ ^ 2 * Real.log (1 / π m) / Module.finrank ℝ E ≤
      κ * σ ^ 2 * (Module.finrank ℝ (S m) + Real.log (1 / π m)) / Module.finrank ℝ E := by
    gcongr
    linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (S m))]
  exact (h1.trans h2).trans (hpen m)

/-! ### Measurability and exponential-moment control -/

/-- If `mh : E → M` is measurable into a countable measurable space with measurable singletons,
then the selected orthogonal projection `Y ↦ (S (mh Y)).starProjection Y` is measurable. -/
@[fun_prop]
theorem measurable_starProjection_apply [MeasurableSpace E] [BorelSpace E]
    {M : Type*} [Countable M] [MeasurableSpace M] [MeasurableSingletonClass M]
    (S : M → Submodule ℝ E) {mh : E → M} (hmh : Measurable mh) :
    Measurable fun Y ↦ (S (mh Y)).starProjection Y := by
  intro s hs
  have hpre : (fun Y ↦ (S (mh Y)).starProjection Y) ⁻¹' s =
      ⋃ m : M, (mh ⁻¹' {m}) ∩ ((S m).starProjection ⁻¹' s) := by
    ext Y
    simp
  rw [hpre]
  exact MeasurableSet.iUnion fun m ↦
    (hmh (measurableSet_singleton m)).inter ((S m).starProjection.continuous.measurable hs)

/-- Auxiliary supremum majorant `W(ξ) = 4 * ∑' m', exp ((Z m' ξ - t m') / 4)` dominating all
shifted chi-squared projections `‖(S m' ⊔ ℝ ∙ f).starProjection ξ‖ ^ 2`. -/
private theorem exists_majorant_sup_starProjection [MeasurableSpace E] [BorelSpace E]
    {M : Type*} [Countable M] (S : M → Submodule ℝ E) (π : M → ℝ) (f : E)
    (hπ : ∀ m, 0 < π m) (hsum : Summable π) :
    ∃ W : E → ℝ, Measurable W ∧ (∀ ξ, 0 ≤ W ξ) ∧ Integrable W (stdGaussian E) ∧
      (∫ ξ, W ξ ∂stdGaussian E ≤ 4 * ∑' m, π m) ∧
      (∀ᵐ ξ ∂stdGaussian E, ∀ m : M,
        ‖(S m ⊔ Submodule.span ℝ {f}).starProjection ξ‖ ^ 2 ≤
          4 * (Module.finrank ℝ (S m) + 1 + Real.log (1 / π m)) + W ξ) := by
  let U : M → Submodule ℝ E := fun m ↦ S m ⊔ Submodule.span ℝ {f}
  let t : M → ℝ := fun m ↦ 4 * (Module.finrank ℝ (S m) + 1 + Real.log (1 / π m))
  let F : M → E → ℝ≥0∞ := fun m ξ ↦
    ENNReal.ofReal (Real.exp ((‖(U m).starProjection ξ‖ ^ 2 - t m) / 4))
  let Wₑ : E → ℝ≥0∞ := fun ξ ↦ 4 * ∑' m : M, F m ξ
  -- Step 1: measurability and dimension bound `dim (S m ⊔ ℝ ∙ f) ≤ dim (S m) + 1`.
  have hF_meas (m : M) : Measurable (F m) :=
    (ENNReal.continuous_ofReal.comp
      (Real.continuous_exp.comp
        ((((U m).starProjection.continuous.norm.pow 2).sub continuous_const).div_const 4))
    ).measurable
  have hWₑ_meas : Measurable Wₑ := Measurable.const_mul (Measurable.tsum hF_meas) 4
  have hU_dim (m : M) : Module.finrank ℝ (U m) ≤ Module.finrank ℝ (S m) + 1 := by
    have hsum_dim := Submodule.finrank_sup_add_finrank_inf_eq (S m) (Submodule.span ℝ {f})
    have hspan : Module.finrank ℝ (Submodule.span ℝ ({f} : Set E)) ≤ 1 := by
      by_cases hf : f = 0
      · rw [hf, Submodule.span_zero_singleton, finrank_bot]
        exact Nat.zero_le 1
      · rw [finrank_span_singleton hf]
    dsimp only [U]
    omega
  -- Step 2: per-model exponential moment bound `∫⁻ F m ≤ π m` via the Gaussian projection MGF.
  have hterm (m : M) : ∫⁻ ξ, F m ξ ∂stdGaussian E ≤ ENNReal.ofReal (π m) := by
    have hfact (ξ : E) :
        F m ξ = ENNReal.ofReal (Real.exp (-t m / 4)) *
          ENNReal.ofReal (Real.exp (‖(U m).starProjection ξ‖ ^ 2 / 4)) := by
      simp only [F]
      rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
      congr 2; ring
    have hexp_meas : Measurable fun ξ : E ↦
        ENNReal.ofReal (Real.exp (‖(U m).starProjection ξ‖ ^ 2 / 4)) :=
      (ENNReal.continuous_ofReal.comp
        (Real.continuous_exp.comp
          (((U m).starProjection.continuous.norm.pow 2).div_const 4))).measurable
    simp_rw [hfact]
    rw [lintegral_const_mul _ hexp_meas]
    have hle : ∫⁻ ξ, ENNReal.ofReal (Real.exp (‖(U m).starProjection ξ‖ ^ 2 / 4)) ∂stdGaussian E ≤
        ENNReal.ofReal (Real.exp (Module.finrank ℝ (U m))) := by
      have hint : Integrable (fun ξ : E ↦ Real.exp (‖(U m).starProjection ξ‖ ^ 2 / 4))
          (stdGaussian E) := by
        simpa [div_eq_mul_inv, mul_comm] using
          (U m).integrable_exp_mul_norm_sq_starProjection_stdGaussian (t := 1 / 4) (by norm_num)
      rw [← ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (Real.exp_pos _).le)]
      refine ENNReal.ofReal_le_ofReal ?_
      have hmgf : ∫ ξ : E, Real.exp (‖(U m).starProjection ξ‖ ^ 2 / 4) ∂stdGaussian E =
          (1 - 2 * (1 / 4 : ℝ)) ^ (-((Module.finrank ℝ (U m) : ℝ) / 2)) := by
        have h := (U m).mgf_norm_sq_starProjection_stdGaussian (t := 1 / 4) (by norm_num)
        simpa [mgf, div_eq_mul_inv, mul_comm] using h
      rw [hmgf]
      set k : ℝ := (Module.finrank ℝ (U m) : ℝ)
      have hhalf : (1 - 2 * (1 / 4 : ℝ)) = (2 : ℝ)⁻¹ := by norm_num
      rw [hhalf, Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num), inv_inv]
      have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        (2 : ℝ) ^ (k / 2) ≤ (Real.exp 1) ^ (k / 2) :=
          Real.rpow_le_rpow (by norm_num) h2e (by positivity)
        _ = Real.exp (k / 2) := by rw [← Real.exp_mul, one_mul]
        _ ≤ Real.exp k :=
          Real.exp_le_exp.mpr (by linarith [Nat.cast_nonneg (α := ℝ) (Module.finrank ℝ (U m))])
    refine (mul_le_mul_right hle _).trans ?_
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have hexp_t : Real.exp (-t m / 4) =
        Real.exp (-((Module.finrank ℝ (S m) : ℝ) + 1)) * π m := by
      have harg : -t m / 4 = -((Module.finrank ℝ (S m) : ℝ) + 1) + Real.log (π m) := by
        simp only [t, one_div, Real.log_inv]
        ring
      rw [harg, Real.exp_add, Real.exp_log (hπ m)]
    rw [hexp_t, mul_right_comm, ← Real.exp_add]
    have hdim_le : (Module.finrank ℝ (U m) : ℝ) ≤ Module.finrank ℝ (S m) + 1 := by
      exact_mod_cast hU_dim m
    have hexp_le : Real.exp (-((Module.finrank ℝ (S m) : ℝ) + 1) + Module.finrank ℝ (U m)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (by linarith)
    nlinarith [hπ m]
  -- Step 3: sum over `m : M` by Tonelli to show `Wₑ` is a.e. finite and integrable.
  have hlint_le : ∫⁻ ξ, Wₑ ξ ∂stdGaussian E ≤ ENNReal.ofReal (4 * ∑' m, π m) := by
    dsimp only [Wₑ]
    rw [lintegral_const_mul _ (Measurable.tsum hF_meas),
      lintegral_tsum fun m ↦ (hF_meas m).aemeasurable]
    calc
      4 * ∑' m, ∫⁻ ξ, F m ξ ∂stdGaussian E ≤ 4 * ∑' m, ENNReal.ofReal (π m) := by
        gcongr
        exact hterm _
      _ = 4 * ENNReal.ofReal (∑' m, π m) := by
        rw [ENNReal.ofReal_tsum_of_nonneg (fun m ↦ (hπ m).le) hsum]
      _ = ENNReal.ofReal (4 * ∑' m, π m) := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  have hlint_lt : ∫⁻ ξ, Wₑ ξ ∂stdGaussian E < ⊤ := hlint_le.trans_lt ENNReal.ofReal_lt_top
  have hae_fin : ∀ᵐ ξ ∂stdGaussian E, Wₑ ξ ≠ ⊤ :=
    (ae_lt_top hWₑ_meas hlint_lt.ne).mono fun _ h ↦ h.ne
  have hW_int : Integrable (fun ξ ↦ (Wₑ ξ).toReal) (stdGaussian E) := by
    refine ⟨hWₑ_meas.ennreal_toReal.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_def]
    refine (lintegral_mono fun ξ ↦ ?_).trans_lt hlint_lt
    rw [Real.eNorm_eq_ofReal ENNReal.toReal_nonneg]
    exact ENNReal.ofReal_toReal_le
  -- Step 4: conclude the integral bound and pointwise domination via `u ≤ exp u`.
  refine ⟨fun ξ ↦ (Wₑ ξ).toReal, hWₑ_meas.ennreal_toReal,
    fun _ ↦ ENNReal.toReal_nonneg, hW_int, ?_, ?_⟩
  · have hsum_nonneg : 0 ≤ 4 * ∑' m, π m :=
      mul_nonneg (by norm_num) (tsum_nonneg fun m ↦ (hπ m).le)
    rw [← ENNReal.ofReal_le_ofReal_iff hsum_nonneg,
      ofReal_integral_eq_lintegral_ofReal hW_int (.of_forall fun _ ↦ ENNReal.toReal_nonneg)]
    exact (lintegral_congr_ae (hae_fin.mono fun ξ hξ ↦ ENNReal.ofReal_toReal hξ)).le.trans hlint_le
  · refine hae_fin.mono fun ξ hξ m ↦ ?_
    set u : ℝ := (‖(U m).starProjection ξ‖ ^ 2 - t m) / 4
    have hu : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    have h4 : 4 * Real.exp u ≤ (Wₑ ξ).toReal := by
      have hterm_le : ENNReal.ofReal (4 * Real.exp u) ≤ Wₑ ξ := by
        rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
        dsimp only [Wₑ]
        have hFu : ENNReal.ofReal (Real.exp u) = F m ξ := rfl
        rw [hFu]
        gcongr
        exact le_tsum (fun m' ↦ F m' ξ) m
      have h := ENNReal.toReal_mono hξ hterm_le
      rwa [ENNReal.toReal_ofReal (by positivity)] at h
    have hdiff : ‖(U m).starProjection ξ‖ ^ 2 - t m = 4 * u := by
      dsimp only [u]
      ring
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
  -- By optimality of `mh Y` and the projection property `‖Y - P_{S_m} Y‖ ≤ ‖Y - fm‖`.
  have hproj_min : ‖Y - (S m).starProjection Y‖ ^ 2 ≤ ‖Y - fm‖ ^ 2 := by
    have hle : ‖Y - (S m).starProjection Y‖ ≤ ‖Y - fm‖ := by
      rw [(S m).starProjection_minimal Y]
      have hbdd : BddBelow (Set.range fun x : S m ↦ ‖Y - (x : E)‖) :=
        ⟨0, by rintro _ ⟨_, rfl⟩; exact norm_nonneg _⟩
      exact ciInf_le hbdd ⟨fm, (S m).starProjection_apply_mem f⟩
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hopt : ‖Y - fhat‖ ^ 2 / n + pen mhY ≤ ‖Y - fm‖ ^ 2 / n + pen m := by
    have h1 := hmin Y m
    rw [penalizedCriterion_def, penalizedCriterion_def] at h1
    exact h1.trans (by gcongr)
  -- Expand both squared norms around `Y = f + σ • ξ`.
  have hexp1 : ‖Y - fhat‖ ^ 2 =
      ‖fhat - f‖ ^ 2 - 2 * σ * ⟪fhat - f, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2 := by
    have heq : Y - fhat = σ • ξ - (fhat - f) := by simp [Y]; abel
    rw [heq, norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_left, real_inner_comm]
    ring
  have hexp2 : ‖Y - fm‖ ^ 2 =
      ‖f - fm‖ ^ 2 + 2 * σ * ⟪f - fm, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2 := by
    have heq : Y - fm = (f - fm) + σ • ξ := by simp [Y]; abel
    rw [heq, norm_add_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      real_inner_smul_right]
    ring
  -- `fhat - f` lies in `U := S mhY ⊔ span {f}`, so `⟪fhat - f, ξ⟫ = ⟪fhat - f, P_U ξ⟫`.
  set U : Submodule ℝ E := S mhY ⊔ Submodule.span ℝ {f}
  have hmemU : fhat - f ∈ U :=
    U.sub_mem (Submodule.mem_sup_left ((S mhY).starProjection_apply_mem Y))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self f))
  have hinner_eq : ⟪fhat - f, ξ⟫ = ⟪fhat - f, U.starProjection ξ⟫ := by
    rw [← U.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hmemU]
  -- Young's inequality with `α = κ / 4 > 1`:
  -- `2 * σ * ⟪fhat - f, ξ⟫ ≤ (4 / κ) * ‖fhat - f‖ ^ 2 + (κ / 4) * σ ^ 2 * ‖P_U ξ‖ ^ 2`.
  have hcs : |⟪fhat - f, U.starProjection ξ⟫| ≤ ‖fhat - f‖ * ‖U.starProjection ξ‖ :=
    abs_real_inner_le_norm _ _
  have hyoung : 2 * σ * ⟪fhat - f, ξ⟫ ≤
      4 / κ * ‖fhat - f‖ ^ 2 + κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 := by
    rw [hinner_eq]
    have habs : σ * ⟪fhat - f, U.starProjection ξ⟫ ≤
        |σ| * (‖fhat - f‖ * ‖U.starProjection ξ‖) :=
      (le_abs_self _).trans <| by
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left hcs (abs_nonneg σ)
    have hsq : 0 ≤ (4 * ‖fhat - f‖ - κ * |σ| * ‖U.starProjection ξ‖) ^ 2 / (4 * κ) := by
      have : 0 < κ := by linarith
      positivity
    have hsq_exp :
        (4 * ‖fhat - f‖ - κ * |σ| * ‖U.starProjection ξ‖) ^ 2 / (4 * κ) =
          4 / κ * ‖fhat - f‖ ^ 2 - 2 * |σ| * (‖fhat - f‖ * ‖U.starProjection ξ‖) +
            κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 := by
      have : κ ≠ 0 := by linarith
      field_simp
      rw [← sq_abs σ]
      ring
    linarith
  -- Combine `hopt`, `hexp1`, `hexp2`, `hyoung`, `hw`, and the penalty lower bound `hpen mhY`.
  have hpen_mh : κ * σ ^ 2 * (Module.finrank ℝ (S mhY) + Real.log (1 / π mhY)) / n ≤ pen mhY :=
    hpen mhY
  have hw_scaled : κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 / n ≤
      κ * σ ^ 2 * (Module.finrank ℝ (S mhY) + Real.log (1 / π mhY)) / n +
        κ * σ ^ 2 / n + κ / 4 * σ ^ 2 * w / n := by
    have hmul := mul_le_mul_of_nonneg_left hw (by positivity : 0 ≤ κ / 4 * σ ^ 2)
    have hdiv := div_le_div_of_nonneg_right hmul hn.le
    calc
      κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 / n
          ≤ κ / 4 * σ ^ 2 * (4 * (Module.finrank ℝ (S mhY) + 1 + Real.log (1 / π mhY)) + w) / n :=
        hdiv
      _ = κ * σ ^ 2 * (Module.finrank ℝ (S mhY) + Real.log (1 / π mhY)) / n +
            κ * σ ^ 2 / n + κ / 4 * σ ^ 2 * w / n := by ring
  have hstep : ‖fhat - f‖ ^ 2 / n + pen mhY ≤
      ‖f - fm‖ ^ 2 / n + pen m + 2 * σ * ⟪fhat - f, ξ⟫ / n +
        2 * σ * ⟪f - fm, ξ⟫ / n := by
    rw [hexp1, hexp2] at hopt
    have hsub1 : (‖fhat - f‖ ^ 2 - 2 * σ * ⟪fhat - f, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2) / n =
        ‖fhat - f‖ ^ 2 / n - 2 * σ * ⟪fhat - f, ξ⟫ / n + σ ^ 2 * ‖ξ‖ ^ 2 / n := by ring
    have hsub2 : (‖f - fm‖ ^ 2 + 2 * σ * ⟪f - fm, ξ⟫ + σ ^ 2 * ‖ξ‖ ^ 2) / n =
        ‖f - fm‖ ^ 2 / n + 2 * σ * ⟪f - fm, ξ⟫ / n + σ ^ 2 * ‖ξ‖ ^ 2 / n := by ring
    linarith
  have hyoung_div : 2 * σ * ⟪fhat - f, ξ⟫ / n ≤
      4 / κ * (‖fhat - f‖ ^ 2 / n) + κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 / n := by
    have := div_le_div_of_nonneg_right hyoung hn.le
    calc
      2 * σ * ⟪fhat - f, ξ⟫ / n
          ≤ (4 / κ * ‖fhat - f‖ ^ 2 + κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2) / n := this
      _ = 4 / κ * (‖fhat - f‖ ^ 2 / n) + κ / 4 * σ ^ 2 * ‖U.starProjection ξ‖ ^ 2 / n := by ring
  have hcoeff : (κ - 4) / κ * (‖fhat - f‖ ^ 2 / n) =
      ‖fhat - f‖ ^ 2 / n - 4 / κ * (‖fhat - f‖ ^ 2 / n) := by
    have : κ ≠ 0 := by linarith
    field_simp
  linarith

/-! ### Integrability and oracle inequality -/

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
    have hzero : (fun ξ : E ↦ ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2) =
        fun _ ↦ 0 := by
      funext ξ
      rw [Subsingleton.elim ((S (mh (f + σ • ξ))).starProjection (f + σ • ξ)) f]
      simp
    rw [hzero]
    exact integrable_const 0
  have hdim_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hdim_pos
  obtain ⟨W, _, _, hW_int, _, hW_ae⟩ := exists_majorant_sup_starProjection S π f hπ hsum
  let m₀ : M := mh 0
  set g : E → ℝ := fun ξ ↦ ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2
  have hg_meas : Measurable g :=
    ((((measurable_starProjection_apply S hmh).comp
      (continuous_const.add (continuous_const.smul continuous_id)).measurable).sub
      measurable_const).norm).pow_const 2
  set c : ℝ := κ / (κ - 4) * n
  have hc_pos : 0 < c := by
    have : 0 < κ - 4 := by linarith
    positivity
  let rhs : E → ℝ := fun ξ ↦
    c * (‖f - (S m₀).starProjection f‖ ^ 2 / n + pen m₀ + κ * σ ^ 2 / n +
      κ / 4 * σ ^ 2 * W ξ / n + 2 * σ * ⟪f - (S m₀).starProjection f, ξ⟫ / n)
  have hinner_int : Integrable (fun ξ : E ↦ ⟪f - (S m₀).starProjection f, ξ⟫) (stdGaussian E) :=
    (innerSL ℝ (f - (S m₀).starProjection f)).integrable_comp IsGaussian.integrable_id
  have hrhs_int : Integrable rhs (stdGaussian E) := by
    have h1 : Integrable (fun _ : E ↦ ‖f - (S m₀).starProjection f‖ ^ 2 / n + pen m₀ +
        κ * σ ^ 2 / n) (stdGaussian E) := integrable_const _
    have h2 : Integrable (fun ξ ↦ κ / 4 * σ ^ 2 * W ξ / n) (stdGaussian E) :=
      (hW_int.const_mul (κ / 4 * σ ^ 2)).div_const n
    have h3 : Integrable (fun ξ ↦ 2 * σ * ⟪f - (S m₀).starProjection f, ξ⟫ / n)
        (stdGaussian E) :=
      (hinner_int.const_mul (2 * σ)).div_const n
    exact ((h1.add h2).add h3).const_mul c
  refine Integrable.mono' hrhs_int hg_meas.aestronglyMeasurable ?_
  filter_upwards [hW_ae] with ξ hξ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hpt := penalized_pointwise_bound S π pen f mh hκ hdim_pos hpen hmin
    (hξ (mh (f + σ • ξ))) m₀
  have hmul := mul_le_mul_of_nonneg_left hpt hc_pos.le
  have hlhs : c * ((κ - 4) / κ * (g ξ / n)) = g ξ := by
    have : κ ≠ 0 := by linarith
    have : κ - 4 ≠ 0 := by linarith
    have : n ≠ 0 := hn.ne'
    simp only [c]
    field_simp
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
    refine mul_nonneg (by positivity) (Real.iInf_nonneg fun m ↦ ?_)
    simpa [hdim] using hpen m
  have hdim_pos : 0 < Module.finrank ℝ E := Nat.pos_of_ne_zero hdim
  set n : ℝ := (Module.finrank ℝ E : ℝ)
  have hn : 0 < n := Nat.cast_pos.mpr hdim_pos
  have : Nonempty M := ⟨mh 0⟩
  have hg_int : Integrable
      (fun ξ ↦ ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n) (stdGaussian E) :=
    (integrable_sq_norm_starProjection_sub S π pen σ f mh hκ hπ hsum hpen hmh hmin).div_const n
  obtain ⟨W, _, _, hW_int, hW_le, hW_ae⟩ := exists_majorant_sup_starProjection S π f hπ hsum
  -- Prove the bound against every fixed competitor `m : M`.
  have hbound (m : M) :
      (κ - 4) / κ *
          ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n ∂stdGaussian E ≤
        (‖f - (S m).starProjection f‖ ^ 2 / n + pen m) + κ * (1 + ∑' m', π m') * σ ^ 2 / n := by
    have hinner_int : Integrable (fun ξ : E ↦ ⟪f - (S m).starProjection f, ξ⟫) (stdGaussian E) :=
      (innerSL ℝ (f - (S m).starProjection f)).integrable_comp IsGaussian.integrable_id
    have hinner_zero : ∫ ξ : E, ⟪f - (S m).starProjection f, ξ⟫ ∂stdGaussian E = 0 :=
      integral_strongDual_stdGaussian (innerSL ℝ (f - (S m).starProjection f))
    let rhs : E → ℝ := fun ξ ↦
      ‖f - (S m).starProjection f‖ ^ 2 / n + pen m + κ * σ ^ 2 / n +
        κ / 4 * σ ^ 2 * W ξ / n + 2 * σ * ⟪f - (S m).starProjection f, ξ⟫ / n
    have h1 : Integrable (fun _ : E ↦ ‖f - (S m).starProjection f‖ ^ 2 / n + pen m +
        κ * σ ^ 2 / n) (stdGaussian E) := integrable_const _
    have h2 : Integrable (fun ξ ↦ κ / 4 * σ ^ 2 * W ξ / n) (stdGaussian E) :=
      (hW_int.const_mul (κ / 4 * σ ^ 2)).div_const n
    have h12 : Integrable (fun ξ ↦ ‖f - (S m).starProjection f‖ ^ 2 / n + pen m +
        κ * σ ^ 2 / n + κ / 4 * σ ^ 2 * W ξ / n) (stdGaussian E) := h1.add h2
    have h3 : Integrable (fun ξ ↦ 2 * σ * ⟪f - (S m).starProjection f, ξ⟫ / n)
        (stdGaussian E) :=
      (hinner_int.const_mul (2 * σ)).div_const n
    have hrhs_int : Integrable rhs (stdGaussian E) := h12.add h3
    have hae : ∀ᵐ ξ ∂stdGaussian E,
        (κ - 4) / κ * (‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n) ≤ rhs ξ :=
      hW_ae.mono fun ξ hξ ↦ penalized_pointwise_bound S π pen f mh hκ hdim_pos hpen hmin
        (hξ (mh (f + σ • ξ))) m
    have hint_le := integral_mono_ae (hg_int.const_mul ((κ - 4) / κ)) hrhs_int hae
    have hlhs : ∫ ξ, (κ - 4) / κ *
        (‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n) ∂stdGaussian E =
        (κ - 4) / κ * ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n
          ∂stdGaussian E := integral_const_mul _ _
    have hrhs_eq : ∫ ξ, rhs ξ ∂stdGaussian E =
        ‖f - (S m).starProjection f‖ ^ 2 / n + pen m + κ * σ ^ 2 / n +
          κ / 4 * σ ^ 2 * (∫ ξ, W ξ ∂stdGaussian E) / n := by
      dsimp only [rhs]
      rw [integral_add h12 h3, integral_add h1 h2, integral_const]
      simp only [probReal_univ, one_smul]
      rw [integral_div, integral_const_mul, integral_div, integral_const_mul, hinner_zero]
      ring
    rw [hlhs, hrhs_eq] at hint_le
    have hW_scaled : κ / 4 * σ ^ 2 * (∫ ξ, W ξ ∂stdGaussian E) / n ≤
        κ * (∑' m', π m') * σ ^ 2 / n := by
      have hmul := mul_le_mul_of_nonneg_left hW_le (by positivity : 0 ≤ κ / 4 * σ ^ 2)
      have hdiv := div_le_div_of_nonneg_right hmul hn.le
      calc
        κ / 4 * σ ^ 2 * (∫ ξ, W ξ ∂stdGaussian E) / n
            ≤ κ / 4 * σ ^ 2 * (4 * ∑' m', π m') / n := hdiv
        _ = κ * (∑' m', π m') * σ ^ 2 / n := by ring
    calc
      (κ - 4) / κ * _ ≤ ‖f - (S m).starProjection f‖ ^ 2 / n + pen m + κ * σ ^ 2 / n +
          κ * (∑' m', π m') * σ ^ 2 / n := by linarith
      _ = (‖f - (S m).starProjection f‖ ^ 2 / n + pen m) +
          κ * (1 + ∑' m', π m') * σ ^ 2 / n := by ring
  -- Take the infimum over `m : M` and divide by `(κ - 4) / κ`.
  have hstep :
      (κ - 4) / κ * ∫ ξ, ‖(S (mh (f + σ • ξ))).starProjection (f + σ • ξ) - f‖ ^ 2 / n
          ∂stdGaussian E - κ * (1 + ∑' m', π m') * σ ^ 2 / n ≤
        ⨅ m, (‖f - (S m).starProjection f‖ ^ 2 / n + pen m) :=
    le_ciInf fun m ↦ sub_le_iff_le_add.mpr (hbound m)
  have hinv : 0 < κ / (κ - 4) := by positivity
  have hmul := mul_le_mul_of_nonneg_left (sub_le_iff_le_add.mp hstep) hinv.le
  have hcancel : κ / (κ - 4) * ((κ - 4) / κ) = 1 := by
    have : κ ≠ 0 := by linarith
    have : κ - 4 ≠ 0 := hκ4.ne'
    field_simp
  rwa [← mul_assoc, hcancel, one_mul] at hmul

end TauCeti
