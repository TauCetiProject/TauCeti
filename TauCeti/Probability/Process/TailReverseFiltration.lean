module

public import TauCeti.Probability.Process.Tail
public import TauCeti.Probability.Martingale.Reverse

/-!
# Process tails as infima of reverse filtrations

This file records the Exchangeability roadmap Layer 2 adapter identifying the process tail
σ-algebra as the infimum of the time-zero levels of the generic finite-horizon reverse
filtrations applied to `tailFamily X`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω : Type*} {β : ℕ → Type*} [MeasurableSpace Ω] [∀ k, MeasurableSpace (β k)]

private theorem iInf_revFiltration_zero (𝔽 : ℕ → MeasurableSpace Ω)
    (h_antitone : Antitone 𝔽) (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω)) :
    (⨅ N : ℕ, (MeasureTheory.revFiltration 𝔽 h_antitone h_le N :
        Filtration ℕ (inferInstance : MeasurableSpace Ω)) 0) = ⨅ N : ℕ, 𝔽 N := by
  simp only [MeasureTheory.revFiltration_apply, tsub_zero]

/-- The process tail is the infimum of the time-zero levels of the finite-horizon reverse
filtrations attached to `tailFamily X`. -/
theorem tailProcess_eq_iInf_revFiltration (X : (k : ℕ) → Ω → β k)
    (hX : ∀ k, Measurable (X k)) :
    tailProcess X =
      ⨅ N : ℕ,
        (MeasureTheory.revFiltration (tailFamily X) (tailFamily_antitone X)
          (fun n => tailFamily_le_ambient n fun k _ => hX k) N :
          Filtration ℕ (inferInstance : MeasurableSpace Ω)) 0 := by
  rw [tailProcess_eq_iInf_tailFamily]
  exact (iInf_revFiltration_zero (tailFamily X) (tailFamily_antitone X)
    (fun n => tailFamily_le_ambient n fun k _ => hX k)).symm

end Probability

end TauCeti
