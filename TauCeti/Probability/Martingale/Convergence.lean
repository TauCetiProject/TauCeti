module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Process.Filtration
public import TauCeti.Probability.Martingale.Crossings.AntitoneLimit
-- Non-public: the generic `AEStronglyMeasurable` σ-algebra helpers are used only in the proof of
-- `aestronglyMeasurable_iInf_of_tendsto_ae_antitone`, so they are not re-exported through the
-- flagship path.
import TauCeti.MeasureTheory.Function.AEStronglyMeasurable

/-!
# Martingale convergence theorems

Lévy's downward theorem for conditional expectations along a decreasing filtration.

This is the flagship of the reverse-martingale infrastructure: the finite-horizon reversal
(`Martingale/Reverse.lean`), the pathwise crossing adapters (`Martingale/Crossings/`), the
reverse-martingale upcrossing bound (`Crossings/Bounds.lean`), and the antitone-limit existence
result (`Crossings/AntitoneLimit.lean`) all feed into `tendsto_ae_condExp_iInf`.

## Main results

- `tendsto_ae_condExp_iInf`: Lévy's downward theorem — for antitone `𝔽` and integrable `f`, the
  sequence `μ[f | 𝔽 n]` converges a.e. to `μ[f | ⨅ n, 𝔽 n]`.

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Convergence.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

open TauCeti.MeasureTheory

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A.e. limit of an adapted antitone sequence is `⨅ n, 𝔽 n`-`AEStronglyMeasurable`.

For antitone `𝔽`, if each `g n` is `𝔽 n`-strongly-measurable and `g n → Xlim` a.e., then `Xlim`
is `AEStronglyMeasurable[⨅ n, 𝔽 n]`. -/
private lemma aestronglyMeasurable_iInf_of_tendsto_ae_antitone
    {𝔽 : ℕ → MeasurableSpace Ω} (h_antitone : Antitone 𝔽)
    {g : ℕ → Ω → ℝ} {Xlim : Ω → ℝ}
    (hg_meas : ∀ n, StronglyMeasurable[𝔽 n] (g n))
    (h_tendsto : ∀ᵐ ω ∂μ, Tendsto (fun n => g n ω) atTop (𝓝 (Xlim ω))) :
    AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ := by
  -- Compose the two `AEStronglyMeasurable` helper lemmas: first show
  -- `AEStronglyMeasurable[𝔽 N] Xlim` for each `N` by feeding the shifted
  -- sequence `g (n + N)` into `aestronglyMeasurable_of_tendsto_ae'`; then
  -- combine over `N` via `aestronglyMeasurable_iInf_of_antitone`.
  refine aestronglyMeasurable_iInf_of_antitone (μ := μ) h_antitone Xlim (fun N => ?_)
  refine aestronglyMeasurable_of_tendsto_ae' (μ := μ) (f := fun n => g (n + N))
    (fun n => (hg_meas (n + N)).measurable.mono
      (h_antitone (Nat.le_add_left N n)) le_rfl) ?_
  filter_upwards [h_tendsto] with ω hω
  exact hω.comp (Filter.tendsto_add_atTop_nat N)

/-- L¹-continuity/tower identification: if `Xn → Xlim` in `L¹` (in `eLpNorm`) and each conditional
expectation `μ[Xn n | F]` agrees a.e. with a fixed `Y`, then `μ[Xlim | F]` agrees a.e. with `Y`. -/
-- Bound `‖μ[Xlim | F] - Y‖₁` by `‖Xlim - Xn n‖₁` (triangle inequality, `condExp_sub` linearity, the
-- L¹ contraction `eLpNorm_one_condExp_le_eLpNorm`, and the vanishing `μ[Xn n | F] - Y` term), then
-- let `n → ∞`.
private lemma condExp_ae_eq_of_tendsto_eLpNorm
    {F : MeasurableSpace Ω} {Xlim Y : Ω → ℝ} {Xn : ℕ → Ω → ℝ}
    (hXlimint : Integrable Xlim μ) (hXn_int : ∀ n, Integrable (Xn n) μ)
    (h_condExp : ∀ n, μ[Xn n | F] =ᵐ[μ] Y)
    (hL1 : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0)) :
    μ[Xlim | F] =ᵐ[μ] Y := by
  -- `Y` inherits (ambient) a.e.-strong-measurability from the conditional expectations it equals.
  -- (No type ascription: it would force the measurability σ-algebra to `F` instead of the ambient.)
  have hY_meas := integrable_condExp.aestronglyMeasurable.congr (h_condExp 0)
  -- Key inequality: `‖μ[Xlim | F] - Y‖₁ ≤ ‖Xlim - Xn n‖₁` for every `n`.
  have h_bound (n : ℕ) : eLpNorm (μ[Xlim | F] - Y) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
    -- Triangle: `(μ[Xlim|F] - Y) = (μ[Xlim|F] - μ[Xn|F]) + (μ[Xn|F] - Y)`.
    have htri : eLpNorm (μ[Xlim | F] - Y) 1 μ
                ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ
                  + eLpNorm (μ[Xn n | F] - Y) 1 μ := by
      have : μ[Xlim | F] - Y = (μ[Xlim | F] - μ[Xn n | F]) + (μ[Xn n | F] - Y) := by ring
      rw [this]
      refine eLpNorm_add_le ?_ ?_ ?_
      · exact (integrable_condExp.sub integrable_condExp).aestronglyMeasurable
      · exact integrable_condExp.aestronglyMeasurable.sub hY_meas
      · norm_num
    -- Second term is `0` since `μ[Xn n | F] =ᵐ Y`.
    have hzero : eLpNorm (μ[Xn n | F] - Y) 1 μ = 0 := by
      have h0 : μ[Xn n | F] - Y =ᵐ[μ] 0 := by
        filter_upwards [h_condExp n] with ω hω; simp [hω]
      rw [eLpNorm_congr_ae h0]; simp
    -- First term `≤ ‖Xlim - Xn‖₁` by `condExp_sub` linearity + the L¹ contraction.
    have hfirst : eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ ≤ eLpNorm (Xlim - Xn n) 1 μ := by
      have hsub : μ[Xlim | F] - μ[Xn n | F] =ᵐ[μ] μ[Xlim - Xn n | F] :=
        (condExp_sub hXlimint (hXn_int n) F).symm
      rw [eLpNorm_congr_ae hsub]
      exact eLpNorm_one_condExp_le_eLpNorm _
    calc eLpNorm (μ[Xlim | F] - Y) 1 μ
        ≤ eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ + eLpNorm (μ[Xn n | F] - Y) 1 μ := htri
      _ = eLpNorm (μ[Xlim | F] - μ[Xn n | F]) 1 μ := by rw [hzero]; ring
      _ ≤ eLpNorm (Xlim - Xn n) 1 μ := hfirst
  -- Let `n → ∞`: the constant LHS is `≤` a sequence tending to `0`, hence it is `0`.
  have h_norm_zero : eLpNorm (μ[Xlim | F] - Y) 1 μ = 0 :=
    le_antisymm
      (le_of_tendsto_of_tendsto tendsto_const_nhds hL1 (Eventually.of_forall h_bound)) bot_le
  rw [eLpNorm_eq_zero_iff (integrable_condExp.aestronglyMeasurable.sub hY_meas)
    one_ne_zero] at h_norm_zero
  filter_upwards [h_norm_zero] with ω hω
  simp only [Pi.zero_apply] at hω
  exact sub_eq_zero.mp hω

/-- Integrable case of Lévy's downward theorem: for integrable `f`, `μ[f | 𝔽 n]` converges a.e. to
`μ[f | ⨅ n, 𝔽 n]`. -/
private lemma tendsto_ae_condExp_iInf_of_integrable
    [IsFiniteMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  classical
  -- We follow the upcrossing-inequality route rather than reindexing by `ℕᵒᵈ`: for antitone `𝔽`,
  -- `⨆ i : ℕᵒᵈ, 𝔽 i.ofDual = 𝔽 0`, so dualising and applying Lévy's *upward* theorem would converge
  -- to the wrong limit `μ[f | 𝔽 0]` instead of `μ[f | ⨅ n, 𝔽 n]`.
  -- 1) A.s. limit `Xlim` exists (upcrossing bounds on the time-reversed martingales).
  obtain ⟨Xlim, hXlimint, h_tendsto⟩ :=
    condExp_exists_ae_limit_antitone (μ := μ) h_filtration h_le f h_f_int
  -- 2) Uniform integrability upgrades a.e. convergence to `L¹` convergence (Vitali).
  have hUI : UniformIntegrable (fun n => μ[f | 𝔽 n]) 1 μ := h_f_int.uniformIntegrable_condExp h_le
  have hL1_conv : Tendsto (fun n => eLpNorm (μ[f | 𝔽 n] - Xlim) 1 μ) atTop (𝓝 0) := by
    apply tendsto_Lp_finite_of_tendsto_ae (hp := le_refl 1) (hp' := ENNReal.one_ne_top)
    · intro n; exact integrable_condExp.aestronglyMeasurable
    · exact memLp_one_iff_integrable.2 hXlimint
    · exact hUI.unifIntegrable
    · exact h_tendsto
  -- `Xlim` is `AEStronglyMeasurable[⨅ n, 𝔽 n]` (a.e. limit of `𝔽 n`-strongly-measurable functions).
  have hXlim_iInf_meas : AEStronglyMeasurable[⨅ n, 𝔽 n] Xlim μ :=
    aestronglyMeasurable_iInf_of_tendsto_ae_antitone h_filtration
      (fun n => stronglyMeasurable_condExp) h_tendsto
  -- 3) Pass the limit through `condExp` at `⨅ n, 𝔽 n`. We work with the raw `⨅ n, 𝔽 n` rather than
  -- a `set` alias: a local of type `MeasurableSpace Ω` shadows the ambient σ-algebra during the
  -- instance synthesis triggered by the call to `condExp_ae_eq_of_tendsto_eLpNorm`.
  -- Tower property: for every `n`, `μ[μ[f | 𝔽 n] | ⨅ n, 𝔽 n] =ᵐ μ[f | ⨅ n, 𝔽 n]`.
  have h_tower : ∀ n, μ[μ[f | 𝔽 n] | ⨅ n, 𝔽 n] =ᵐ[μ] μ[f | ⨅ n, 𝔽 n] :=
    fun n => condExp_condExp_of_le (iInf_le 𝔽 n) (h_le n)
  have hiInf_le : (⨅ n, 𝔽 n) ≤ (inferInstance : MeasurableSpace Ω) :=
    le_trans (iInf_le 𝔽 0) (h_le 0)
  set Xn : ℕ → Ω → ℝ := fun n => μ[f | 𝔽 n] with hXn_def
  -- Rephrase the L¹ convergence with the `Xn` abbreviation.
  have hL1_conv_Xn : Tendsto (fun n => eLpNorm (Xlim - Xn n) 1 μ) atTop (𝓝 0) := by
    simpa [hXn_def, eLpNorm_sub_comm] using hL1_conv
  -- Identify `μ[Xlim | ⨅ n, 𝔽 n]` with `μ[f | ⨅ n, 𝔽 n]` by L¹-continuity of conditional
  -- expectation (the tower property gives `μ[Xn n | ⨅ n, 𝔽 n] =ᵐ μ[f | ⨅ n, 𝔽 n]`).
  have hCE_eqY : μ[Xlim | ⨅ n, 𝔽 n] =ᵐ[μ] μ[f | ⨅ n, 𝔽 n] :=
    condExp_ae_eq_of_tendsto_eLpNorm hXlimint (fun _ => integrable_condExp) h_tower hL1_conv_Xn
  -- `Xlim` is `AEStronglyMeasurable[⨅ n, 𝔽 n]` (a.e. limit of `⨅ n, 𝔽 n`-measurable functions), so
  -- `μ[Xlim | ⨅ n, 𝔽 n] =ᵐ Xlim`; combined with `hCE_eqY` this identifies `μ[f | ⨅ n, 𝔽 n]`.
  have hXlim_eq : μ[f | ⨅ n, 𝔽 n] =ᵐ[μ] Xlim := by
    have hXlim_condExp_self : μ[Xlim | ⨅ n, 𝔽 n] =ᵐ[μ] Xlim :=
      condExp_of_aestronglyMeasurable' hiInf_le hXlim_iInf_meas hXlimint
    exact hCE_eqY.symm.trans hXlim_condExp_self
  -- Combine `h_tendsto : μ[f | 𝔽 n] → Xlim` with `hXlim_eq : μ[f | ⨅ n, 𝔽 n] =ᵐ Xlim`.
  filter_upwards [h_tendsto, hXlim_eq] with ω h_tend h_eq
  rw [h_eq]
  exact h_tend

/-- **Conditional expectation converges along a decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration `𝔽ₙ`, the sequence `μ[f | 𝔽ₙ]` converges almost surely to
`μ[f | ⨅ₙ 𝔽ₙ]`. No integrability hypothesis is needed: when `f` is not integrable both
`μ[f | 𝔽ₙ]` and `μ[f | ⨅ₙ 𝔽ₙ]` are `0`, so the limit is the constant `0`. -/
theorem tendsto_ae_condExp_iInf
    [IsFiniteMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) := by
  by_cases hf : Integrable f μ
  · exact tendsto_ae_condExp_iInf_of_integrable h_filtration h_le f hf
  · -- Non-integrable `f`: `condExp` is `0` at every σ-algebra, so both sides are `0`.
    filter_upwards with ω
    simp only [condExp_of_not_integrable hf, Pi.zero_apply]
    exact tendsto_const_nhds

end ProbabilityTheory
