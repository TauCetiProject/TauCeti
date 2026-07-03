module

public import Mathlib.Probability.Martingale.Convergence
import TauCeti.Probability.Martingale.Crossings.Bounds

/-!
# Crossings: antitone-filtration limit existence

Reverse-martingale infrastructure: a.e. existence of the limit of `μ[f | 𝔽 n]` along an antitone
filtration. The identification of this limit as `μ[f | ⨅ n, 𝔽 n]` (Lévy's downward theorem) is the
flagship `tendsto_ae_condExp_iInf` in `Martingale/Convergence.lean`, which consumes this file.

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

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Pathwise comparison: the upcrossings of `n ↦ μ[f | 𝔽 n]` on `[a, b]` before time `N` are
bounded by the total upcrossings on `[-b, -a]` of the negated finite-horizon reverse process. -/
private lemma upcrossingsBefore_condExp_le_upcrossings_negProcess_revCondExpFinite
    (f : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ upcrossings (-b) (-a) (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := by
  -- The `N + 1` horizon on the reversed side lets crossings completing exactly at `N` count.
  have h_orig_le : upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
      ≤ downcrossingsBefore a b (revProcess (fun n => μ[f | 𝔽 n]) N) (N + 1) ω :=
    upcrossingsBefore_le_downcrossingsBefore_revProcess_succ (fun n => μ[f | 𝔽 n]) a b hab N ω
  simp only [downcrossingsBefore_eq] at h_orig_le
  have h_rev_eq : negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)
                = negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) := by
    funext n ω; simp only [negProcess_apply, revProcess_apply, revCondExpFinite_apply]
  -- Pick the index `N + 1` out of the supremum defining `upcrossings`.
  have h_to_iSup :
      ↑(upcrossingsBefore (-b) (-a)
          (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) (N + 1) ω)
        ≤ upcrossings (-b) (-a) (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := by
    simp only [MeasureTheory.upcrossings]
    apply le_iSup (fun M => (upcrossingsBefore (-b) (-a)
        (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) M ω : ℝ≥0∞)) (N + 1)
  calc ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ ↑(upcrossingsBefore (-b) (-a)
            (negProcess (revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω) :=
        Nat.cast_le.mpr h_orig_le
    _ = ↑(upcrossingsBefore (-b) (-a)
            (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) (N + 1) ω) := by rw [h_rev_eq]
    _ ≤ upcrossings (-b) (-a)
            (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω := h_to_iSup

/-- Finite-horizon integral step: negating commutes a.e. with the reverse conditional-expectation
process (via `condExp_neg`), so the upcrossing integrals of the negated process and of the reverse
process of `-f` agree. -/
private lemma lintegral_upcrossings_negProcess_revCondExpFinite_eq
    (f : Ω → ℝ) (a b : ℝ) (N : ℕ) :
    ∫⁻ ω, upcrossings (-b) (-a)
        (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω ∂μ
      = ∫⁻ ω, upcrossings (-b) (-a)
          (fun n => revCondExpFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ := by
  apply lintegral_congr_ae
  -- The two processes agree a.e. at every time index (countable intersection via `ae_all_iff`).
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
      negProcess (fun m => revCondExpFinite (μ := μ) f 𝔽 N m) n ω =
      revCondExpFinite (μ := μ) (fun x => -f x) 𝔽 N n ω := by
    rw [ae_all_iff]
    intro n
    simp only [negProcess_apply, revCondExpFinite_apply]
    exact (condExp_neg f (𝔽 (N - n))).symm
  filter_upwards [h_ae_eq] with ω hω
  simp [MeasureTheory.upcrossings, upcrossingsBefore_congr (fun k _ => hω k)]

/-- Reverse-martingale upcrossing bound: for real `a < b`, the expected number of upcrossings of
`n ↦ μ[f | 𝔽 n]` on `[a, b]` is finite, so the upcrossings are a.e. finite. -/
private lemma ae_upcrossings_condExp_lt_top
    [IsFiniteMeasure μ] {𝔽 : ℕ → MeasurableSpace Ω}
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂μ, upcrossings a b (fun n => μ[f | 𝔽 n]) ω < ⊤ := by
  -- Get bound for upcrossings (forward direction)
  obtain ⟨C_up, h_C_up_finite, hC_up⟩ :=
    upcrossings_bdd_uniform h_antitone h_le f hf (a) (b) hab
  -- Get bound for downcrossings via negated process (backward direction)
  obtain ⟨C_down, h_C_down_finite, hC_down⟩ := upcrossings_bdd_uniform h_antitone h_le
      (fun ω => -f ω) hf.neg (-b) (-a) (by linarith)
  -- Use max of both bounds as the uniform constant
  set C := max C_up C_down with hC_def
  have h_C_finite : C < ⊤ := max_lt h_C_up_finite h_C_down_finite
  -- Per-horizon `L¹` bound: compose the pathwise comparison with the negation-commutes step.
  have h_N_bound : ∀ N,
      ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C := fun N =>
    calc ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ
        ≤ ∫⁻ ω, upcrossings (-b) (-a)
              (negProcess (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)) ω ∂μ :=
          lintegral_mono
            (upcrossingsBefore_condExp_le_upcrossings_negProcess_revCondExpFinite f hab N)
      _ = ∫⁻ ω, upcrossings (-b) (-a)
            (fun n => revCondExpFinite (μ := μ) (fun x => -f x) 𝔽 N n) ω ∂μ :=
          lintegral_upcrossings_negProcess_revCondExpFinite_eq f a b N
      _ ≤ C_down := hC_down N
      _ ≤ C := le_max_right C_up C_down
  -- The sequence `μ[f | 𝔽 n]` is adapted to the constant ambient filtration; used
  -- below for both `measurable_upcrossingsBefore` and `measurable_upcrossings`.
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Ω) le_rfl
  have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
    fun n => stronglyMeasurable_condExp.mono (h_le n)
  -- Use monotone convergence on the ORIGINAL process (which IS monotone in N)
  have h_exp_orig : ∫⁻ ω, upcrossings (a) (b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
    -- Set U N ω := upcrossingsBefore for the original process
    set U : ℕ → Ω → ℝ≥0∞ :=
      fun N ω => (upcrossingsBefore (a) (b) (fun n => μ[f | 𝔽 n]) N ω : ℝ≥0∞) with hU
    -- Monotonicity in N (pathwise): more time allows more completed crossings
    have hU_mono : Monotone U := by
      intro m n hmn ω
      simp only [hU]
      have := upcrossingsBefore_mono (f := fun n => μ[f | 𝔽 n]) hab hmn ω
      exact Nat.cast_le.2 this
    -- Measurability (via the constant filtration `ℱ` set up above)
    have hU_meas : ∀ N, Measurable (U N) := fun _ =>
      measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab)
    -- Apply monotone convergence theorem
    have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := lintegral_iSup hU_meas hU_mono
    -- Bound the supremum of integrals
    have : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := iSup_le h_N_bound
    -- Conclude: upcrossings = ⨆ N, upcrossingsBefore N
    simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans this
  -- Apply ae_lt_top: measurable function with finite expectation is a.e. finite
  refine ae_lt_top ?_ (lt_of_le_of_lt h_exp_orig h_C_finite).ne
  exact h_adapted.measurable_upcrossings hab

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

end ProbabilityTheory
