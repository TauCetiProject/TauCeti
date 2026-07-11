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

/-- The process tail is the infimum of the time-zero levels of the finite-horizon reverse
filtrations attached to `tailFamily X`. -/
theorem tailProcess_eq_iInf_revFiltration_zero (X : (k : ℕ) → Ω → β k)
    (hX : ∀ k, Measurable (X k)) :
    tailProcess X =
      ⨅ N : ℕ,
        (MeasureTheory.revFiltration (tailFamily X) (tailFamily_antitone X)
          (fun n => tailFamily_le_ambient n fun k _ => hX k) N :
          Filtration ℕ (inferInstance : MeasurableSpace Ω)) 0 := by
  rw [tailProcess_eq_iInf_tailFamily, MeasureTheory.iInf_revFiltration_zero]

end Probability

end TauCeti
