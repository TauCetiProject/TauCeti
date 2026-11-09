/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Normalizability

/-!
# Beta-gas normalizability tests

Smoke tests for the general-potential logarithmic-growth API.
-/

public section

namespace TauCeti.Probability

open MeasureTheory Real

variable {n : ℕ} {β β' : ℝ} {V : ℝ → ℝ}
variable (hβ : 0 < β) (hβ' : 1 < β') (hββ' : β ≤ β') (hV : Continuous V)
variable (hliminf :
  ((2 * β' / β : ℝ) : EReal) <
    Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
      (Filter.comap (fun x : ℝ => |x|) Filter.atTop))

example : Integrable (betaGasWeight n β V)
    (Measure.pi fun _ : Fin n => (volume : Measure ℝ)) :=
  integrable_betaGasWeight_of_log_growth n hβ hβ' hββ' hV hliminf

example : 0 < betaGasPartitionFunction n β V :=
  betaGasPartitionFunction_pos_of_log_growth n hβ hβ' hββ' hV hliminf

example : IsProbabilityMeasure (betaGasMeasure n β V) :=
  isProbabilityMeasure_betaGasMeasure_of_log_growth n hβ hβ' hββ' hV hliminf

end TauCeti.Probability
