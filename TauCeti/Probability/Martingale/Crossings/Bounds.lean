module

public import TauCeti.Probability.Martingale.Reverse
public import TauCeti.Probability.Martingale.Crossings.Pathwise

/-!
# Crossings: uniform upcrossing bound for reverse martingales

The L¹-uniform upcrossing bound used in the reverse-martingale antitone-limit argument. Built on
top of `Pathwise.lean` and `Reverse.lean`.

## Main results

- `upcrossings_bdd_uniform`: uniform-in-`N` bound on the expected number of upcrossings for the
  reverse martingale of an L¹-bounded `f` along an antitone filtration.

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

/-- Uniform (in `N`) bound on upcrossings for the reverse martingale.

For an L¹-bounded martingale obtained by reversing an antitone filtration, the expected number of
upcrossings is uniformly bounded, independent of the time horizon `N`. -/
lemma upcrossings_bdd_uniform
    [IsProbabilityMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (hf : Integrable f μ) (a b : ℝ) (hab : a < b) :
    ∃ C : ENNReal, C < ⊤ ∧ ∀ N,
      ∫⁻ ω, (upcrossings (↑a) (↑b) (fun n => revCondExpFinite (μ := μ) f 𝔽 N n) ω) ∂μ ≤ C := by
  -- The L¹ norm of revCondExpFinite is uniformly bounded by ‖f‖₁
  have hL1_bdd : ∀ N n, eLpNorm (revCondExpFinite (μ := μ) f 𝔽 N n) 1 μ ≤ eLpNorm f 1 μ := by
    intro N n
    exact eLpNorm_one_condExp_le_eLpNorm f
  -- For each N, revCondExpFinite is a martingale, hence a submartingale
  have h_submart : ∀ N, Submartingale (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)
      (revFiltration 𝔽 h_antitone h_le N) μ :=
    fun N => (revCondExpFinite_martingale (μ := μ) h_antitone h_le f hf N).submartingale
  -- For each fixed N and M, we can bound E[(f_M - a)⁺] by ‖f‖₁ + |a|
  have h_bound : ∀ N M, ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
    intro N M
    -- Use (x - a)⁺ ≤ |x - a| ≤ |x| + |a|, then integrate
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
      _ = ∫⁻ ω, ENNReal.ofReal |revCondExpFinite (μ := μ) f 𝔽 N M ω| ∂μ + ENNReal.ofReal |a| := by
          simp [lintegral_add_right, lintegral_const, IsProbabilityMeasure.measure_univ]
      _ ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
          gcongr
          -- Convert lintegral to eLpNorm and use hL1_bdd
          have hconv : ∫⁻ ω, ENNReal.ofReal |revCondExpFinite (μ := μ) f 𝔽 N M ω| ∂μ =
              eLpNorm (revCondExpFinite (μ := μ) f 𝔽 N M) 1 μ := by
            rw [eLpNorm_one_eq_lintegral_enorm]
            congr 1; ext ω
            exact (Real.enorm_eq_ofReal_abs _).symm
          rw [hconv]
          calc eLpNorm (revCondExpFinite (μ := μ) f 𝔽 N M) 1 μ
              ≤ eLpNorm f 1 μ := hL1_bdd N M
            _ = ENNReal.ofReal (eLpNorm f 1 μ).toReal := by
                rw [ENNReal.ofReal_toReal]
                exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
  -- Define C as the bound divided by (b - a)
  set C := (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a|) / ENNReal.ofReal (b - a)
  -- Prove C < ⊤
  have hC_finite : C < ⊤ := by
    refine ENNReal.div_lt_top ?h1 ?h2
    · -- Numerator ≠ ⊤
      refine ENNReal.add_lt_top.2 ⟨?_, ENNReal.ofReal_lt_top⟩ |>.ne
      rw [ENNReal.ofReal_toReal]
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_lt_top
      · exact (memLp_one_iff_integrable.mpr hf).eLpNorm_ne_top
    · -- Denominator ≠ 0
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 hab)).ne'
  refine ⟨C, hC_finite, fun N => ?_⟩
  -- Apply the submartingale upcrossing inequality
  have key := (h_submart N).mul_lintegral_upcrossings_le_lintegral_pos_part a b
  -- Bound the supremum using h_bound
  have sup_bdd : ⨆ M, ∫⁻ ω, ENNReal.ofReal ((revCondExpFinite (μ := μ) f 𝔽 N M ω - a)⁺) ∂μ
      ≤ ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a| := by
    apply iSup_le
    intro M
    exact h_bound N M
  -- Combine: (b - a) * E[upcrossings] ≤ sup ≤ bound, so E[upcrossings] ≤ C
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
    _ ≤ (ENNReal.ofReal (eLpNorm f 1 μ).toReal + ENNReal.ofReal |a|) / ENNReal.ofReal (b - a) := by
        gcongr
    _ = C := rfl

end ProbabilityTheory
