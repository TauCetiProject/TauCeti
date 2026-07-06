module

public import Mathlib.Probability.Martingale.Convergence
import TauCeti.Probability.Martingale.Crossings.Bounds

/-!
# Crossings: antitone-filtration limit existence

Reverse-martingale infrastructure: a.e. existence of the limit of `μ[f | 𝔽 n]` along an antitone
filtration. The identification of this limit as `μ[f | ⨅ n, 𝔽 n]` (Lévy's downward theorem) is the
flagship result in `Martingale/Convergence.lean`, which consumes this file.

## Main results

- `condExp_exists_ae_limit_antitone`: a.e. limit existence for antitone filtrations.

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

/-- The a.e. limit of `n ↦ μ[f | 𝔽 n]` along an antitone filtration is integrable. -/
-- Fatou (`lintegral_liminf_le'`) plus the uniform L¹ bound `‖μ[f | 𝔽 n]‖₁ ≤ ‖f‖₁`.
private lemma integrable_of_ae_tendsto_condExp
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) {Xlim : Ω → ℝ}
    (h_ae_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) :
    Integrable Xlim μ := by
  have hL1_bdd : ∀ n, eLpNorm (μ[f | 𝔽 n]) 1 μ ≤ eLpNorm f 1 μ :=
    fun n => eLpNorm_one_condExp_le_eLpNorm _
  have hf_Lp_ne_top : eLpNorm f 1 μ ≠ ⊤ := (memLp_one_iff_integrable.2 hf).eLpNorm_ne_top
  set R := (eLpNorm f 1 μ).toNNReal with hR_def
  have hR : eLpNorm f 1 μ = ↑R := (ENNReal.coe_toNNReal hf_Lp_ne_top).symm
  -- `Xlim` is `AEStronglyMeasurable` as an a.e. limit of measurable functions.
  have hXlim_ae_meas : AEStronglyMeasurable Xlim μ := by
    refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n => μ[f | 𝔽 n]) (fun n => ?_)
      h_ae_tendsto
    exact (stronglyMeasurable_condExp.mono (h_le n)).aestronglyMeasurable
  -- Finite integral via Fatou and the uniform L¹ bound.
  have hXlim_norm : HasFiniteIntegral Xlim μ := by
    rw [hasFiniteIntegral_iff_norm]
    have hmeas_n : ∀ n, AEMeasurable (fun ω => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) μ := fun n =>
      ((stronglyMeasurable_condExp (f := f) (m := 𝔽 n) (μ := μ)).mono
        (h_le n)).norm.measurable.ennreal_ofReal.aemeasurable
    calc
      ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
          ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop := by
            -- Fatou along the a.e. limit: rewrite ‖Xlim‖ as the a.e. `liminf` of ‖μ[f|𝔽 n]‖
            -- (via `Tendsto.liminf_eq`), then apply Mathlib's `lintegral_liminf_le'`.
            have hae_ofReal : ∀ᵐ ω ∂μ,
                Tendsto (fun n => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) atTop
                  (nhds (ENNReal.ofReal ‖Xlim ω‖)) :=
              h_ae_tendsto.mono fun ω hω =>
                ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hω
            calc ∫⁻ ω, ENNReal.ofReal ‖Xlim ω‖ ∂μ
                = ∫⁻ ω, liminf (fun n => ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖) atTop ∂μ :=
                  lintegral_congr_ae (hae_ofReal.mono fun ω hω => hω.liminf_eq.symm)
              _ ≤ liminf (fun n => ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ) atTop :=
                  lintegral_liminf_le' hmeas_n
      _ ≤ ↑R := by
            rw [liminf_le_iff]
            intro c hc
            apply Eventually.frequently
            rw [eventually_atTop]
            refine ⟨0, fun n _ => ?_⟩
            calc ∫⁻ ω, ENNReal.ofReal ‖μ[f | 𝔽 n] ω‖ ∂μ
                = ∫⁻ ω, ‖μ[f | 𝔽 n] ω‖ₑ ∂μ := by
                  congr 1; ext ω
                  rw [Real.enorm_eq_ofReal_abs]
                  simp only [Real.norm_eq_abs]
              _ = eLpNorm (μ[f | 𝔽 n]) 1 μ := MeasureTheory.eLpNorm_one_eq_lintegral_enorm.symm
              _ ≤ eLpNorm f 1 μ := hL1_bdd n
              _ = ↑R := hR
              _ < c := hc
      _ < ⊤ := ENNReal.coe_lt_top
  exact ⟨hXlim_ae_meas, hXlim_norm⟩

/-- A.S. existence of the limit of `μ[f | 𝔽 n]` along an antitone filtration. -/
-- The proof applies the upcrossing inequality to the time-reversed martingales to show that the
-- original sequence has finitely many upcrossings and downcrossings a.e., hence converges a.e.
lemma condExp_exists_ae_limit_antitone
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) :
    ∃ Xlim, (Integrable Xlim μ ∧
           ∀ᵐ ω ∂μ, Tendsto (fun n => μ[f | 𝔽 n] ω) atTop (𝓝 (Xlim ω))) := by
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
  exact ⟨Xlim, integrable_of_ae_tendsto_condExp h_le f hf h_ae_tendsto, h_ae_tendsto⟩

end MeasureTheory
