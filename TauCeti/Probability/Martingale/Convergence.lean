module

public import Mathlib.Probability.Martingale.Basic
public import Mathlib.Probability.Martingale.Convergence
public import Mathlib.Probability.Process.Filtration
-- The crossing/reverse-martingale implementation chain is imported non-publicly, so downstream
-- users of this module see `tendsto_ae_condExp_iInf` but not the internal helpers
-- (`condExp_exists_ae_limit_antitone`, `upcrossings_bdd_uniform`, `downcrossings`, ...). The
-- `AntitoneLimit` module transitively pulls in `Bounds` and `Pathwise`.
import TauCeti.Probability.Martingale.Crossings.AntitoneLimit

/-!
# Martingale convergence theorems

Lévy's downward theorem for conditional expectations along a decreasing filtration.

## Main results

- `tendsto_ae_condExp_iInf`: Lévy's downward theorem — for antitone `𝔽` and integrable `f`, the
  sequence `μ[f | 𝔽 n]` converges a.e. to `μ[f | ⨅ n, 𝔽 n]`.

## References

* Kallenberg, *Probabilistic Symmetries and Invariance Principles* (2005), Section 1
* Durrett, *Probability: Theory and Examples* (2019), Section 5.5
* Williams, *Probability with Martingales* (1991), Theorem 12.12

Adapted from `cameronfreer/exchangeability` (`Probability/Martingale/Convergence.lean`, pin
`e0532e59ceff23edab44dda9ab0655debbc9cc22`). Written Mathlib-shaped for eventual upstreaming.
-/

public section

noncomputable section

open MeasureTheory Filter

open scoped Topology ENNReal

namespace ProbabilityTheory

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Conditional expectation converges along a decreasing filtration (Lévy's downward theorem).**

For a decreasing filtration `𝔽ₙ` and integrable `f`, the sequence `Mₙ := μ[f | 𝔽ₙ]` converges a.s.
to `μ[f | ⨅ₙ 𝔽ₙ]`.

**Proof strategy:** the upcrossing inequality approach:
1. Define upcrossings for an interval `[a,b]`.
2. Prove the upcrossing inequality: `E[# upcrossings] ≤ E[|X₀ - a|] / (b - a)`.
3. Show finitely many upcrossings a.e. for all rational `[a,b]`.
4. Deduce that `μ[f | 𝔽 n]` converges a.e.
5. Identify the limit as `μ[f | ⨅ 𝔽 n]` using the tower property.

**Why not use OrderDual reindexing?** For antitone `F`, the supremum `⨆ i : ℕᵒᵈ, F i.ofDual`
equals `F 0` (since `F 0` is the largest element of the chain), not `⨅ n, F n`. So applying
Lévy's upward theorem to the dualised filtration would give convergence to `μ[f | F 0]`, the wrong
limit. -/
theorem tendsto_ae_condExp_iInf
    [IsProbabilityMeasure μ]
    {𝔽 : ℕ → MeasurableSpace Ω}
    (h_filtration : Antitone 𝔽)
    (h_le : ∀ n, 𝔽 n ≤ (inferInstance : MeasurableSpace Ω))
    (f : Ω → ℝ) (h_f_int : Integrable f μ) :
    ∀ᵐ ω ∂μ, Tendsto
      (fun n => μ[f | 𝔽 n] ω)
      atTop
      (𝓝 (μ[f | ⨅ n, 𝔽 n] ω)) :=
  tendsto_ae_condExp_iInf_aux h_filtration h_le f h_f_int

/-! ## Implementation notes

`tendsto_ae_condExp_iInf` is proved via the chain:

1. `revFiltration`, `revCondExpFinite`: time-reversal infrastructure (`Martingale/Reverse.lean`).
2. `revCondExpFinite_martingale`: the reversed process is a forward martingale.
3. `condExp_exists_ae_limit_antitone`: a.s. existence via upcrossing bounds
   (`Martingale/Crossings.lean`).
4. `Integrable.uniformIntegrable_condExp` (Mathlib): uniform integrability of conditional
   expectations.
5. `tendsto_ae_condExp_iInf_aux`: limit identification via Vitali convergence + tower property.
6. `tendsto_ae_condExp_iInf`: wraps step 5.

Mathlib dependencies: `Filtration`, `condExp_condExp_of_le` (tower property). Reverse-martingale
convergence is *not* available in Mathlib; the chain above proves it locally for the Lévy downward
case. -/

end ProbabilityTheory
