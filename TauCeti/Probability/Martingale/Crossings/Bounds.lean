/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Martingale.Upcrossing
import TauCeti.Probability.Martingale.Reverse
import TauCeti.Probability.Martingale.Crossings.Pathwise
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import TauCeti.MeasureTheory.Function.ConditionalExpectation

/-!
# Crossings: uniform upcrossing bound for reverse martingales

The L¹-uniform upcrossing bound used in the reverse-martingale antitone-limit argument. Built on
top of `Pathwise.lean` and `Reverse.lean`.

## Main results

- `exists_lintegral_upcrossings_condExp_le`: a uniform crossing bound for the antitone
  conditional-expectation sequence `n ↦ μ[f | 𝔽 n]`, for integrable `f`.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings/Bounds.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory TauCeti.MeasureTheory

open scoped ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Surrogate bound (kept private): uniform (in `N`) bound on upcrossings for the reversed
conditional-expectation process.

For an integrable `f` and the process obtained by reversing an antitone filtration, the expected
number of upcrossings is uniformly bounded, independent of the time horizon `N`, by Doob's
upcrossing inequality. The public `exists_lintegral_upcrossings_condExp_le` transfers this
surrogate bound to the genuine antitone sequence `n ↦ μ[f | 𝔽 n]`. -/
private lemma lintegral_upcrossings_condExp_rev_bdd [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω) ∂μ ≤ C := by
  -- `C = (‖f‖₁ + |a| · μ(univ)) / (b - a)` via Doob's upcrossing inequality.
  set C := (eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ) / ENNReal.ofReal (b - a)
  have hC_finite : C < ⊤ := by
    refine ENNReal.div_lt_top ?h1 ?h2
    · -- Numerator ≠ ⊤ (finite measure keeps `μ Set.univ < ⊤`)
      refine (ENNReal.add_lt_top.2 ⟨?_, ?_⟩).ne
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
      · exact ENNReal.mul_lt_top enorm_lt_top (measure_lt_top μ Set.univ)
    · -- Denominator ≠ 0
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  refine ⟨C, hC_finite, fun N => ?_⟩
  -- Doob's upcrossing inequality for the reversed submartingale, then bound the supremum with
  -- the positive-part L¹ estimate.
  have hsub := (martingale_condExp f (revFiltration 𝔽 h_antitone h_le N) μ).submartingale
  have key := hsub.mul_lintegral_upcrossings_le_lintegral_pos_part a b
  simp only [revFiltration_apply] at key
  have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ
      ≤ eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ :=
    iSup_le fun M => lintegral_ofReal_posPart_condExp_sub_le f a
  have step1 : (∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω ∂μ)
      * ENNReal.ofReal (b - a)
      ≤ ⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ := by
    rw [mul_comm]; exact key
  calc ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 (N - n)]) ω ∂μ
      ≤ (⨆ M, ∫⁻ ω, ENNReal.ofReal ((μ[f | 𝔽 (N - M)] ω - a)⁺) ∂μ)
          / ENNReal.ofReal (b - a) := by
        refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 step1
        · left; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
        · left; exact ENNReal.ofReal_ne_top
    _ ≤ (eLpNorm f 1 μ + ‖a‖ₑ * μ Set.univ) / ENNReal.ofReal (b - a) := by
        gcongr
    _ = C := rfl

/-- Pathwise comparison: the upcrossings of `n ↦ μ[f | 𝔽 n]` on `[a, b]` before time `N` are
bounded by the total upcrossings on `[-b, -a]` of the negated finite-horizon reverse process. -/
private lemma upcrossingsBefore_condExp_le_upcrossings_neg_condExp_rev
    (f : Ω → ℝ) {a b : ℝ} (hab : a < b) (N : ℕ) (ω : Ω) :
    ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ upcrossings (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) ω := by
  -- `revProcess (μ[f|𝔽·]) N` and `n ↦ μ[f | 𝔽 (N - n)]` agree on `[0, N]` (below the horizon,
  -- `Polynomial.revAt N` is genuine subtraction). The `N + 1` reversed horizon lets crossings
  -- completing exactly at `N` count, but the extra index `N + 1` is a *free boundary*: it never
  -- affects the crossing count (`upcrossingsBefore_succ_congr`), so we may swap the two processes
  -- there even though they differ at `N + 1`.
  have h_agree : ∀ n ≤ N, (-(revProcess (fun n => μ[f | 𝔽 n]) N)) n ω
      = (-(fun n => μ[f | 𝔽 (N - n)])) n ω := by
    intro n hn
    simp only [Pi.neg_apply, revProcess_apply_of_le _ hn]
  have hle : upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
      ≤ upcrossingsBefore (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω :=
    calc upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω
        ≤ upcrossingsBefore (-b) (-a) (-(revProcess (fun n => μ[f | 𝔽 n]) N)) (N + 1) ω :=
          upcrossingsBefore_le_upcrossingsBefore_neg_revProcess_succ _ a b hab N ω
      _ = upcrossingsBefore (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω :=
          upcrossingsBefore_succ_congr h_agree
  calc ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω)
      ≤ ↑(upcrossingsBefore (-b) (-a)
            (-(fun n => μ[f | 𝔽 (N - n)])) (N + 1) ω) := Nat.cast_le.mpr hle
    _ ≤ upcrossings (-b) (-a) (-(fun n => μ[f | 𝔽 (N - n)])) ω := by
        simp only [MeasureTheory.upcrossings]
        exact le_iSup (fun M => (upcrossingsBefore (-b) (-a)
          (-(fun n => μ[f | 𝔽 (N - n)])) M ω : ℝ≥0∞)) (N + 1)

/-- Finite-horizon integral step: negating commutes a.e. with the reverse conditional-expectation
process (via `condExp_neg`), so the upcrossing integrals of the negated process and of the reverse
process of `-f` agree. -/
private lemma lintegral_upcrossings_neg_condExp_rev_eq (f : Ω → ℝ) (a b : ℝ) (N : ℕ) :
    ∫⁻ ω, upcrossings (-b) (-a)
        (-(fun n => μ[f | 𝔽 (N - n)])) ω ∂μ
      = ∫⁻ ω, upcrossings (-b) (-a)
          (fun n => μ[(fun x => -f x) | 𝔽 (N - n)]) ω ∂μ := by
  apply lintegral_congr_ae
  -- The two processes agree a.e. at every time index (countable intersection via `ae_all_iff`).
  have h_ae_eq : ∀ᵐ ω ∂μ, ∀ n,
      (-(fun m => μ[f | 𝔽 (N - m)])) n ω =
      μ[(fun x => -f x) | 𝔽 (N - n)] ω := by
    rw [ae_all_iff]
    intro n
    simp only [Pi.neg_apply]
    exact (condExp_neg f (𝔽 (N - n))).symm
  filter_upwards [h_ae_eq] with ω hω
  simp only [MeasureTheory.upcrossings]
  refine iSup_congr fun M => ?_
  rw [upcrossingsBefore_congr (fun k _ => hω k)]

/-- Upgrade a uniform-in-`N` bound on the per-horizon `upcrossingsBefore` integrals to a bound on
the total `upcrossings` integral, by monotone convergence in the horizon `N`. The adapted process
`g` supplies the measurability of each `upcrossingsBefore` count. -/
private lemma lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le
    {g : ℕ → Ω → ℝ} {a b : ℝ} {C : ℝ≥0∞} {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}
    (h_adapted : StronglyAdapted ℱ g) (hab : a < b)
    (h_N_bound : ∀ N, ∫⁻ ω, ↑(upcrossingsBefore a b g N ω) ∂μ ≤ C) :
    ∫⁻ ω, upcrossings a b g ω ∂μ ≤ C := by
  -- Set `U N ω := upcrossingsBefore` (as `ℝ≥0∞`) for the process `g`.
  set U : ℕ → Ω → ℝ≥0∞ := fun N ω => (upcrossingsBefore a b g N ω : ℝ≥0∞) with hU
  -- Monotonicity in `N` (pathwise): more time allows more completed crossings.
  have hU_mono : Monotone U := by
    intro m n hmn ω
    simp only [hU]
    exact Nat.cast_le.2 (upcrossingsBefore_mono (f := g) hab hmn ω)
  -- Measurability of each `U N` via the adaptedness hypothesis.
  have hU_meas : ∀ N, Measurable (U N) := fun _ =>
    measurable_from_top.comp (h_adapted.measurable_upcrossingsBefore hab)
  -- Monotone convergence, then bound the supremum of integrals by `C`.
  have h_iSup : ∫⁻ ω, (⨆ N, U N ω) ∂μ = ⨆ N, ∫⁻ ω, U N ω ∂μ := lintegral_iSup hU_meas hU_mono
  have hbound : (⨆ N, ∫⁻ ω, U N ω ∂μ) ≤ C := iSup_le h_N_bound
  -- Conclude via `upcrossings = ⨆ N, upcrossingsBefore N`.
  simpa [MeasureTheory.upcrossings, hU] using h_iSup.le.trans hbound

/-- Uniform crossing bound for the antitone conditional-expectation sequence.

For an antitone filtration `𝔽` and integrable `f`, the expected number of upcrossings of the
conditional-expectation process `n ↦ μ[f | 𝔽 n]` on any interval `[a, b]` is finite — the L¹
reverse-martingale upcrossing bound. This is the crossing bound consumed by the antitone-limit
(Lévy downward) argument. -/
theorem exists_lintegral_upcrossings_condExp_le [IsFiniteMeasure μ] (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → ℝ) (hf : Integrable f μ)
    (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => μ[f | 𝔽 n]) ω ∂μ ≤ C := by
  -- Downcrossings-side surrogate bound: apply the (private) reversed-process bound to `-f` on the
  -- reflected interval `[-b, -a]`. This yields the constant `C_down` used throughout.
  obtain ⟨C_down, h_C_down_finite, hC_down⟩ :=
    lintegral_upcrossings_condExp_rev_bdd (μ := μ) h_antitone h_le
      (fun ω => -f ω) hf.neg (-b) (-a) (by linarith)
  refine ⟨C_down, h_C_down_finite, ?_⟩
  -- Per-horizon `L¹` bound: compose the pathwise comparison with the negation-commutes step, then
  -- discharge with the surrogate bound `hC_down`.
  have h_N_bound : ∀ N,
      ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ ≤ C_down := fun N =>
    calc ∫⁻ ω, ↑(upcrossingsBefore a b (fun n => μ[f | 𝔽 n]) N ω) ∂μ
        ≤ ∫⁻ ω, upcrossings (-b) (-a)
              (-(fun n => μ[f | 𝔽 (N - n)])) ω ∂μ :=
          lintegral_mono
            (upcrossingsBefore_condExp_le_upcrossings_neg_condExp_rev f hab N)
      _ = ∫⁻ ω, upcrossings (-b) (-a)
            (fun n => μ[(fun x => -f x) | 𝔽 (N - n)]) ω ∂μ :=
          lintegral_upcrossings_neg_condExp_rev_eq f a b N
      _ ≤ C_down := hC_down N
  -- The sequence `μ[f | 𝔽 n]` is adapted to the constant ambient filtration, supplying the
  -- measurability needed for the monotone-convergence upgrade.
  let ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω) :=
    Filtration.const ℕ (inferInstance : MeasurableSpace Ω) le_rfl
  have h_adapted : StronglyAdapted ℱ (fun n => μ[f | 𝔽 n]) :=
    fun n => stronglyMeasurable_condExp.mono (h_le n)
  -- Upgrade the per-horizon bound to the total upcrossings integral (monotone convergence in `N`).
  exact lintegral_upcrossings_le_of_forall_lintegral_upcrossingsBefore_le h_adapted hab h_N_bound

end MeasureTheory
