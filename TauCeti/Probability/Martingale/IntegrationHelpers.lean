module

public import Mathlib.MeasureTheory.Integral.Lebesgue.Add
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# Integration helper lemmas

A Fatou-type lemma used by the reverse-martingale antitone-limit argument to bound the L¹ norm of
an a.e. pointwise limit.

## Main results

- `lintegral_fatou_ofReal_norm`: if `u n x → g x` a.e., then
  `∫⁻ ‖g‖ ≤ liminf (∫⁻ ‖u n‖)`.

Adapted from `cameronfreer/exchangeability` (`Probability/IntegrationHelpers.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Only the Fatou lemma needed downstream is retained;
the remaining reference lemmas have Mathlib equivalents or belong to unrelated developments.
Written Mathlib-shaped for eventual upstreaming.
-/

public section

open MeasureTheory Filter Topology

namespace ProbabilityTheory.IntegrationHelpers

/-- Fatou's lemma along an a.e. pointwise limit, for `ENNReal.ofReal ∘ ‖·‖`.

If `u n x → g x` a.e., then `∫⁻ ‖g‖ ≤ liminf (∫⁻ ‖u n‖)`. -/
lemma lintegral_fatou_ofReal_norm
    {α β : Type*} [MeasurableSpace α] {μ : Measure α}
    [MeasurableSpace β] [NormedAddCommGroup β] [BorelSpace β]
    {u : ℕ → α → β} {g : α → β}
    (hae : ∀ᵐ x ∂μ, Tendsto (fun n => u n x) atTop (nhds (g x)))
    (hu_meas : ∀ n, AEMeasurable (fun x => ENNReal.ofReal ‖u n x‖) μ)
    (_hg_meas : AEMeasurable (fun x => ENNReal.ofReal ‖g x‖) μ) :
    ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop := by
  have hae_ofReal :
      ∀ᵐ x ∂μ,
        Tendsto (fun n => ENNReal.ofReal ‖u n x‖) atTop
                (nhds (ENNReal.ofReal ‖g x‖)) :=
    hae.mono (fun x hx =>
      ((ENNReal.continuous_ofReal.comp continuous_norm).tendsto _).comp hx)
  calc ∫⁻ x, ENNReal.ofReal ‖g x‖ ∂μ
      = ∫⁻ x, liminf (fun n => ENNReal.ofReal ‖u n x‖) atTop ∂μ :=
          lintegral_congr_ae (hae_ofReal.mono fun x hx => hx.liminf_eq.symm)
    _ ≤ liminf (fun n => ∫⁻ x, ENNReal.ofReal ‖u n x‖ ∂μ) atTop :=
          lintegral_liminf_le' hu_meas

end ProbabilityTheory.IntegrationHelpers
