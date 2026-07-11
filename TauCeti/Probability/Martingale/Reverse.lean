module

public import Mathlib.Probability.Martingale.Basic

/-!
# Reverse martingale infrastructure (finite horizon)

Reversing time on a finite horizon `N` turns an antitone family of σ-algebras `𝔽`, and its
conditional-expectation process `n ↦ μ[f | 𝔽 n]`, into a *forward* filtration `revFiltration` on
which the conditional-expectation process is a genuine forward martingale (via Mathlib's
`martingale_condExp`). This finite-horizon reversal is the base step of the reverse (Lévy-downward)
martingale convergence argument.

## Main definitions

- `revFiltration`: the time-reversed filtration on a finite horizon `N` (`k ↦ 𝔽 (N - k)`).
- `revCEFinite`: the time-reversed conditional-expectation process (`n ↦ μ[f | 𝔽 (N - n)]`),
  for a Banach-space-valued `f`.

## Main results

- `iInf_revFiltration_zero`: the infimum of the time-zero levels of the finite-horizon reverse
  filtrations is the infimum of the original antitone family.
- `revCEFinite_martingale`: the reversed conditional-expectation process is a forward martingale for
  `revFiltration` (the finite-horizon reversal adapter for Mathlib's `martingale_condExp`).

`revFiltration_apply` / `revCEFinite_apply` are the `@[simp]` defining equations.

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Reverse.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

namespace MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure[m0] Ω} {𝔽 : ℕ → MeasurableSpace Ω}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Reverse filtration on a finite horizon `N`: its level `n` is `𝔽 (N - n)`. Used for
finite-horizon time reversal of an antitone family `𝔽`. -/
-- This is a (forward, increasing) filtration because `k ≤ ℓ` gives `N - ℓ ≤ N - k`, so
-- antitonicity of `𝔽` yields `𝔽 (N - k) ≤ 𝔽 (N - ℓ)`.
def revFiltration (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0)
    (N : ℕ) : Filtration ℕ m0 where
  seq := fun n => 𝔽 (N - n)
  mono' := by
    intro i j hij
    exact h_antitone (tsub_le_tsub_left hij N)
  le' := fun _ => h_le _

/-- Reverse conditional-expectation process at finite horizon `N`: for `n ≤ N` this is
`μ[f | 𝔽 (N - n)]`, for a Banach-space-valued `f`. -/
noncomputable def revCEFinite (f : Ω → E) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    Ω → E :=
  μ[f | 𝔽 (N - n)]

omit [CompleteSpace E] in
/-- Defining equation for `revCEFinite` (whose body is deliberately not `@[expose]`d). -/
@[simp]
lemma revCEFinite_apply (f : Ω → E) (𝔽 : ℕ → MeasurableSpace Ω) (N n : ℕ) :
    revCEFinite (μ := μ) f 𝔽 N n = μ[f | 𝔽 (N - n)] := by rfl

/-- Levels of the reverse filtration: `revFiltration 𝔽 … N` at `n` is `𝔽 (N - n)`. -/
@[simp]
lemma revFiltration_apply (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0) (N n : ℕ) :
    (revFiltration 𝔽 h_antitone h_le N) n = 𝔽 (N - n) := by
  simp only [revFiltration]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
/-- The infimum of the time-zero levels of finite-horizon reverse filtrations recovers the
infimum of the original antitone family. -/
lemma iInf_revFiltration_zero (𝔽 : ℕ → MeasurableSpace Ω) (h_antitone : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ m0) :
    (⨅ N : ℕ, (revFiltration 𝔽 h_antitone h_le N) 0) = ⨅ N : ℕ, 𝔽 N := by
  simp [revFiltration_apply]

/-- Finite-horizon reversal adapter for Mathlib's `martingale_condExp`: the reversed
conditional-expectation process `revCEFinite … N` is a genuine (forward) martingale for the forward
filtration `revFiltration 𝔽 … N`. -/
theorem revCEFinite_martingale (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ m0) (f : Ω → E)
    (N : ℕ) [SigmaFiniteFiltration μ (revFiltration 𝔽 h_antitone h_le N)] :
    Martingale (fun n => revCEFinite (μ := μ) f 𝔽 N n) (revFiltration 𝔽 h_antitone h_le N) μ := by
  simpa only [revCEFinite_apply, revFiltration_apply] using
    martingale_condExp f (revFiltration 𝔽 h_antitone h_le N) μ

end MeasureTheory
