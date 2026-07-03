module

public import TauCeti.Probability.Martingale.Reverse
public import TauCeti.Probability.Martingale.Crossings.Pathwise
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Crossings: uniform upcrossing bound for reverse martingales

The L¹-uniform upcrossing bound used in the reverse-martingale antitone-limit argument. Built on
top of `Pathwise.lean` and `Reverse.lean`.

## Main results

- `upcrossings_bdd_uniform`: uniform-in-`N` bound on the expected number of upcrossings for the
  reversed conditional-expectation process along an antitone filtration.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Crossings/Bounds.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
variable {𝔽 : ℕ → MeasurableSpace Ω}

/-- Positive-part L¹ bound for the reversed conditional-expectation process: for integrable `f`,
the integral of `(revCondExpFinite f 𝔽 N M · - a)⁺` is bounded by `‖f‖₁ + |a| · μ(univ)`,
uniformly in the horizon `N` and the time `M`. -/
private lemma lintegral_pos_part_revCondExpFinite_le
    (f : Ω → ℝ) (hf : Integrable f μ) (a : ℝ) (N M : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ := by
  -- Use (x - a)⁺ ≤ |x - a| ≤ |x| + |a|, integrate, then convert to `eLpNorm` and apply the
  -- L¹ contraction of conditional expectation.
  calc ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ∫⁻ ω, ENNReal.ofReal (|revCondExpFinite (μ := μ) f 𝔽 N M ω| + |a|) ∂μ := by
        apply lintegral_mono
        intro ω
        apply ENNReal.ofReal_le_ofReal
        calc (revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺
            = max (revCondExpFinite (μ := μ) f 𝔽 N M ω - a) 0 := rfl
          _ ≤ |revCondExpFinite (μ := μ) f 𝔽 N M ω - a| := by
              simp only [le_abs_self, max_le_iff, abs_nonneg, and_self]
          _ ≤ |revCondExpFinite (μ := μ) f 𝔽 N M ω| + |a| := by
              rw [sub_eq_add_neg]
              simpa using abs_add_le (revCondExpFinite (μ := μ) f 𝔽 N M ω) (-a)
    _ = ∫⁻ ω, (ENNReal.ofReal |revCondExpFinite (μ := μ) f 𝔽 N M ω| + ENNReal.ofReal |a|) ∂μ := by
        simp [ENNReal.ofReal_add]
    _ = ∫⁻ ω, ENNReal.ofReal |revCondExpFinite (μ := μ) f 𝔽 N M ω| ∂μ
          + ENNReal.ofReal |a| * μ Set.univ := by
        rw [lintegral_add_right _ measurable_const, lintegral_const]
    _ ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ := by
        gcongr
        have hconv : ∫⁻ ω, ENNReal.ofReal |revCondExpFinite (μ := μ) f 𝔽 N M ω| ∂μ =
            eLpNorm (revCondExpFinite (μ := μ) f 𝔽 N M) 1 μ := by
          rw [eLpNorm_one_eq_lintegral_enorm]
          congr 1; ext ω
          exact (Real.enorm_eq_ofReal_abs _).symm
        rw [hconv]
        calc eLpNorm (revCondExpFinite (μ := μ) f 𝔽 N M) 1 μ
            ≤ eLpNorm f 1 μ := by
                rw [revCondExpFinite_apply]; exact eLpNorm_one_condExp_le_eLpNorm f
          _ = ENNReal.ofReal (eLpNorm f 1 μ).toReal := by
              rw [ENNReal.ofReal_toReal]
              exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top

omit [MeasurableSpace Ω] in
/-- A process constant in time has no upcrossings: for `a < b`, the identically-zero process has
zero upcrossings of `[a, b]`. This makes the reverse-martingale bound hold trivially when `f` is not
integrable, since the reversed conditional expectations then all vanish. -/
private lemma upcrossings_zero_eq {a b : ℝ} (hab : a < b) (ω : Ω) :
    upcrossings a b (fun (_ : ℕ) => (0 : Ω → ℝ)) ω = 0 := by
  have hub : ∀ N, upcrossingsBefore a b (fun (_ : ℕ) => (0 : Ω → ℝ)) N ω = 0 := by
    intro N
    rcases Nat.eq_zero_or_pos N with hN | hN
    · rw [hN]; exact upcrossingsBefore_zero
    · refine Nat.eq_zero_of_le_zero (csSup_le ⟨0, ?_⟩ ?_)
      · simp only [Set.mem_setOf_eq, upperCrossingTime_zero, Pi.bot_apply, bot_eq_zero']
        exact hN
      · rintro n hn
        rcases n with _ | m
        · exact le_refl 0
        · exfalso
          rw [Set.mem_setOf_eq] at hn
          have huc_ne : upperCrossingTime a b (fun (_ : ℕ) => (0 : Ω → ℝ)) N (m + 1) ω ≠ N :=
            ne_of_lt hn
          have hb : b ≤ (0 : ℝ) := by
            have := stoppedValue_upperCrossingTime huc_ne
            simpa [stoppedValue] using this
          have hlt : lowerCrossingTime a b (fun (_ : ℕ) => (0 : Ω → ℝ)) N m ω
              < upperCrossingTime a b (fun (_ : ℕ) => (0 : Ω → ℝ)) N (m + 1) ω :=
            lowerCrossingTime_lt_upperCrossingTime hab huc_ne
          have hlow_ne : lowerCrossingTime a b (fun (_ : ℕ) => (0 : Ω → ℝ)) N m ω ≠ N :=
            ne_of_lt (lt_trans hlt hn)
          have ha : (0 : ℝ) ≤ a := by
            have := stoppedValue_lowerCrossingTime hlow_ne
            simpa [stoppedValue] using this
          linarith
  simp [MeasureTheory.upcrossings, hub]

/-- Uniform (in `N`) bound on upcrossings for the reversed conditional-expectation process.

For the process obtained by reversing an antitone filtration, the expected number of upcrossings is
uniformly bounded, independent of the time horizon `N`. No integrability hypothesis is needed: when
`f` is not integrable the reversed conditional expectations all vanish, so the bound holds with
`C = 0`. -/
lemma upcrossings_bdd_uniform
    [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C := by
  by_cases hf : Integrable f μ
  · -- Integrable `f`: `C = (‖f‖₁ + |a| · μ(univ)) / (b - a)` via Doob's upcrossing inequality.
    set C := (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ)
        / ENNReal.ofReal (b - a)
    have hC_finite : C < ⊤ := by
      refine ENNReal.div_lt_top ?h1 ?h2
      · -- Numerator ≠ ⊤ (finite measure keeps `μ Set.univ < ⊤`)
        refine (ENNReal.add_lt_top.2 ⟨?_, ?_⟩).ne
        · rw [ENNReal.ofReal_toReal]
          · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
          · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
        · exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ Set.univ)
      · -- Denominator ≠ 0
        exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
    refine ⟨C, hC_finite, fun N => ?_⟩
    -- Doob's upcrossing inequality for the reversed submartingale, then bound the supremum with
    -- the positive-part L¹ estimate.
    have hsub := submartingale_revCondExpFinite (μ := μ) h_antitone h_le f N
    have key := hsub.mul_lintegral_upcrossings_le_lintegral_pos_part a b
    have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
        ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ :=
      iSup_le fun M => lintegral_pos_part_revCondExpFinite_le f hf a N M
    have step1 : (∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω ∂μ)
        * ENNReal.ofReal (b - a)
        ≤ ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ := by
      rw [mul_comm]; exact key
    calc ∫⁻ ω, upcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω ∂μ
        ≤ (⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ)
            / ENNReal.ofReal (b - a) := by
          refine (ENNReal.le_div_iff_mul_le ?_ ?_).2 step1
          · left; exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
          · left; exact ENNReal.ofReal_ne_top
      _ ≤ (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| * μ Set.univ)
            / ENNReal.ofReal (b - a) := by
          gcongr
      _ = C := rfl
  · -- Non-integrable `f`: `revCondExpFinite f 𝔽 N n = μ[f | 𝔽 (N - n)] = 0`, so the reversed
    -- process is identically `0` and has no upcrossings; the bound holds with `C = 0`.
    refine ⟨0, ENNReal.zero_lt_top, fun N => ?_⟩
    have hzero : (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) = fun _ => (0 : Ω → ℝ) := by
      funext n; rw [revCondExpFinite_apply]; exact condExp_of_not_integrable hf
    rw [hzero]
    simp only [upcrossings_zero_eq hab, lintegral_zero, le_refl]

end ProbabilityTheory
