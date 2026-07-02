module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Process.Filtration
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Reverse martingale infrastructure

To prove Lévy's downward (reverse martingale) convergence theorem, we reverse time on finite
horizons to turn the antitone conditional-expectation process into a forward martingale, then feed
it to the upcrossing inequality.

## Main definitions

- `revFiltration`: the time-reversed filtration on a finite horizon `N` (`k ↦ 𝔽 (N - k)`).
- `revCondExpFinite`: the time-reversed conditional-expectation process (`n ↦ μ[f | 𝔽 (N - n)]`).

## Main results

- `revCondExpFinite_martingale`: the reversed process is a forward martingale for `revFiltration`.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Reverse.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {𝔽 : ℕ → MeasurableSpace Ω}

/-- Reverse filtration on a finite horizon `N`.

For an antitone family `𝔽`, set `𝔾ₖ := 𝔽 (N - k)`. Since `k ≤ ℓ` gives `N - ℓ ≤ N - k`, antitonicity
of `𝔽` yields `𝔽 (N - k) ≤ 𝔽 (N - ℓ)`, so `𝔾` is a forward (increasing) filtration. -/
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := fun n => 𝔽 (N - n)
  mono' := by
    intro i j hij
    exact h_antitone (tsub_le_tsub_left hij N)
  le' := fun _ => h_le _

/-- Reverse conditional-expectation process at finite horizon `N`: for `n ≤ N` this is
`μ[f | 𝔽 (N - n)]`. -/
noncomputable def revCondExpFinite (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    Ω → ℝ :=
  μ[f | 𝔽 (N - n)]

/-- Defining equation for `revCondExpFinite` (whose body is deliberately not `@[expose]`d). -/
lemma revCondExpFinite_apply (f : Ω → ℝ) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    revCondExpFinite (μ := μ) f 𝔽 N n = μ[f | 𝔽 (N - n)] := by rfl

/-- The reversed process `revCondExpFinite f 𝔽 N` is a martingale for `revFiltration 𝔽 N`: by
the tower property, `μ[μ[f | 𝔽 (N - j)] | 𝔽 (N - i)] = μ[f | 𝔽 (N - i)]` whenever `i ≤ j`. -/
lemma revCondExpFinite_martingale [IsFiniteMeasure μ]
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (N : ℕ) :
    Martingale (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)
      (revFiltration 𝔽 h_antitone h_le N) μ := by
  constructor
  · intro n
    exact stronglyMeasurable_condExp
  · intro i j hij
    simp only [revCondExpFinite, revFiltration]
    exact condExp_condExp_of_le (h_antitone (tsub_le_tsub_left hij N)) (h_le (N - j))

end ProbabilityTheory
