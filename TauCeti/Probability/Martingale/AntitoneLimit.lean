module

public import Mathlib.Probability.Martingale.Convergence
import TauCeti.Probability.Martingale.Crossings.Bounds

/-!
# Antitone-filtration limit existence

Reverse-martingale infrastructure: a.e. existence of the limit of `μ[f | 𝔽 n]` along an antitone
filtration. Identifying this limit as `μ[f | ⨅ n, 𝔽 n]` (Lévy's downward theorem) is a forthcoming
Layer-4 result that will consume this existence lemma.

## Main results

- `exists_integrable_tendsto_ae_condExp_of_antitone` (roadmap alias
  `condExp_exists_ae_limit_of_antitone`): a.e. limit existence for antitone filtrations.

Adapted from `cameronfreer/exchangeability`
(`Probability/Martingale/Crossings/AntitoneLimit.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter Set Function

open scoped Topology ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Reverse-martingale upcrossing bound: for real `a < b`, the expected number of upcrossings of
`n ↦ μ[f | 𝔽 n]` on `[a, b]` is finite, so the upcrossings are a.e. finite. -/
private lemma ae_upcrossings_condExp_lt_top
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂μ, upcrossings a b (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
  -- The genuine antitone-sequence upcrossing bound: `∫⁻ upcrossings (μ[f|𝔽·]) ≤ C < ⊤`.
  obtain ⟨C, hC_finite, hC⟩ :=
    exists_lintegral_upcrossings_condExp_le (μ := μ) h_antitone h_le f hf a b hab
  -- `μ[f | 𝔽 n]` is adapted to the constant ambient filtration, giving measurability of
  -- `ω ↦ upcrossings a b (μ[f|𝔽·]) ω`.
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Ω) le_rfl
  have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
    fun n => stronglyMeasurable_condExp.mono (h_le n)
  -- Finite integral (`exists_lintegral_upcrossings_condExp_le`) ⇒ a.e. finite (`ae_lt_top`).
  exact ae_lt_top (h_adapted.measurable_upcrossings hab) (lt_of_le_of_lt hC hC_finite).ne

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration. -/
-- The proof applies the upcrossing inequality to the time-reversed martingales to show that the
-- original sequence has finitely many upcrossings and downcrossings a.e., hence converges a.e.
lemma exists_integrable_tendsto_ae_condExp_of_antitone
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
  by_cases hf : Integrable f μ
  swap
  · -- Non-integrable `f`: `μ[f | 𝔽 n] = 0` for all `n`, so the constant limit `0` works.
    refine ⟨0, integrable_zero Ω ℝ μ, ?_⟩
    filter_upwards with ω
    simp only [condExp_of_not_integrable hf, Pi.zero_apply]
    exact tendsto_const_nhds
  -- Integrable `f`: the genuine reverse-martingale a.e. limit.
  -- L¹ bound and its finite `NNReal` form.
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := (memLp_one_iff_integrable.2 hf).eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm
  -- Step 1: the liminf of the norms is a.e. finite.
  have hbdd_liminf : ∀ᵐ ω ∂μ, (liminf (fun n => ENorm.enorm (μ[f | 𝔽 n] ω)) atTop) < ⊤ := by
    refine ae_bdd_liminf_atTop_of_eLpNorm_bdd (R := R) one_ne_zero (fun n => ?_) (fun n => ?_)
    · exact stronglyMeasurable_condExp.measurable.mono (h_le n) le_rfl
    · simpa [hR] using hL1_bdd n
  -- Step 2: finitely many upcrossings a.e. for every rational interval.
  have hupcross : ∀ᵐ ω ∂μ, ∀ a b : ℚ, a < b →
      upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
    simp only [ae_all_iff, eventually_imp_distrib_left]
    intro a b hab
    exact ae_upcrossings_condExp_lt_top h_antitone h_le f hf (Rat.cast_lt.2 hab)
  -- Step 3: pointwise convergence from the bounded liminf and finitely many upcrossings.
  have h_ae_conv : ∀ᵐ ω ∂μ, ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c) := by
    filter_upwards [hbdd_liminf, hupcross] with ω hω₁ hω₂
    have hω₁' : (liminf (fun n => ENNReal.ofNNReal (nnnorm (μ[f | 𝔽 n] ω))) atTop) < ⊤ := by
      simpa only [enorm_eq_nnnorm] using hω₁
    exact tendsto_of_uncrossing_lt_top hω₁' hω₂
  -- Step 4: choose the limit and read off its two properties.
  classical
  let Xlim : Ω → ℝ := fun ω =>
    if h : ∃ c, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 c)
    then Classical.choose h
    else 0
  have h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω)) := by
    filter_upwards [h_ae_conv] with ω hω
    simpa [Xlim, hω] using Classical.choose_spec hω
  exact ⟨Xlim, (hf.uniformIntegrable_condExp h_le).integrable_of_ae_tendsto h_ae_tendsto,
    h_ae_tendsto⟩

/-- Roadmap Layer 4 target name for `exists_integrable_tendsto_ae_condExp_of_antitone`. -/
alias condExp_exists_ae_limit_of_antitone := exists_integrable_tendsto_ae_condExp_of_antitone

end MeasureTheory
