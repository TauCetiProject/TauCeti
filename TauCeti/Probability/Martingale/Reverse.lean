module

public import Mathlib.Probability.Martingale.Basic

/-!
# Reverse martingale infrastructure (finite horizon)

Reversing time on a finite horizon `N` turns an antitone family of σ-algebras `𝔽`, and its
conditional-expectation process `n ↦ μ[f | 𝔽 n]`, into a *forward* filtration and a genuine forward
martingale. This finite-horizon reversal is the base step of the reverse (Lévy-downward) martingale
convergence argument.

## Main definitions

- `revFiltration`: the time-reversed filtration on a finite horizon `N` (`k ↦ 𝔽 (N - k)`).
- `revCondExpFinite`: the time-reversed conditional-expectation process (`n ↦ μ[f | 𝔽 (N - n)]`),
  for a Banach-space-valued `f`.

## Main results

- `martingale_revCondExpFinite`: the reversed conditional-expectation process is a martingale for
  `revFiltration`.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Reverse.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

namespace MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {𝔽 : ℕ → MeasurableSpace Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reverse filtration on a finite horizon `N`: its level `n` is `𝔽 (N - n)`. Used for
finite-horizon time reversal of an antitone family `𝔽`. -/
-- This is a (forward, increasing) filtration because `k ≤ ℓ` gives `N - ℓ ≤ N - k`, so
-- antitonicity of `𝔽` yields `𝔽 (N - k) ≤ 𝔽 (N - ℓ)`.
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (N : ℕ) : Filtration ℕ (inferInstance : MeasurableSpace Ω) where
  seq := fun n => 𝔽 (N - n)
  mono' := by
    intro i j hij
    exact h_antitone (tsub_le_tsub_left hij N)
  le' := fun _ => h_le _

/-- Reverse conditional-expectation process at finite horizon `N`: for `n ≤ N` this is
`μ[f | 𝔽 (N - n)]`, for a Banach-space-valued `f`. -/
noncomputable def revCondExpFinite (f : Ω → E) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    Ω → E :=
  μ[f | 𝔽 (N - n)]

omit [CompleteSpace E] in
/-- Defining equation for `revCondExpFinite` (whose body is deliberately not `@[expose]`d). -/
@[simp]
lemma revCondExpFinite_apply (f : Ω → E) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    revCondExpFinite (μ := μ) f 𝔽 N n = μ[f | 𝔽 (N - n)] := by rfl

/-- Levels of the reverse filtration: `revFiltration 𝔽 … N` at `n` is `𝔽 (N - n)`. -/
@[simp]
lemma revFiltration_apply (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) (N n : ℕ) :
    (revFiltration 𝔽 h_antitone h_le N) n = 𝔽 (N - n) := by
  simp only [revFiltration]

/-- The reversed conditional-expectation process `revCondExpFinite f 𝔽 N` is a martingale for the
forward filtration `revFiltration 𝔽 … N`: reversing time on a finite horizon turns the antitone
conditional-expectation family into a genuine (forward) martingale. -/
lemma martingale_revCondExpFinite (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) (f : Ω → E) (N : ℕ)
    [SigmaFiniteFiltration μ (revFiltration 𝔽 h_antitone h_le N)] :
    Martingale (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)
      (revFiltration 𝔽 h_antitone h_le N) μ := by
  have hfun : (fun n => revCondExpFinite (μ := μ) f 𝔽 N n)
      = fun n => μ[f | (revFiltration 𝔽 h_antitone h_le N) n] := by
    funext n; rw [revCondExpFinite_apply, revFiltration_apply]
  rw [hfun]
  exact martingale_condExp f (revFiltration 𝔽 h_antitone h_le N) μ

end MeasureTheory
