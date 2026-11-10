/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.RellichKondrachov
public import TauCeti.Analysis.Sobolev.Wkp.Basic
import TauCeti.Analysis.Sobolev.Wkp.Compactness

/-!
# Higher-order Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E`, `1 ≤ p ≤ ∞` and every natural `k`, forgetting the
highest weak derivative is a compact operator `W^{k+1,p}(Ω) → W^{k,p}(Ω)`. Unlike the interior
statement `TauCeti.Wkp.isCompactOperator_restrictL_lowerOrderL`, no restriction to a compactly
contained subdomain is needed: the estimate holds up to the boundary.

The proof applies the domain-independent lifting
`TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isCompactOperator_valueL` to the first-order theorem
`TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`. That lifting inducts on the order:
the lower-order component is compact by induction, and the highest retained derivative field is
compact coordinatewise, since each scalar coordinate is a `W^{1,p}(Ω)` function.

## Main declarations

* `TauCeti.Wkp.isCompactOperator_lowerOrderL_of_isLipschitzDomainWith`: compactness of
  `W^{k+1,p}(Ω) → W^{k,p}(Ω)`.
* `TauCeti.Wkp.exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith`: a bounded sequence in
  `W^{k+1,p}(Ω)` has a subsequence converging in `W^{k,p}(Ω)`.

## References

* R. A. Adams and J. J. F. Fournier, *Sobolev Spaces*, 2nd ed., Theorem 6.3, part I; the
  higher-order statement follows by applying the first-order theorem to the weak derivatives.
-/

public section

noncomputable section

namespace TauCeti

open Bornology Filter MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

namespace Wkp

/-- **Higher-order Rellich–Kondrachov on bounded Lipschitz domains.** If `Ω` is a bounded
Lipschitz domain and `1 ≤ p ≤ ∞`, forgetting the highest weak derivative is a compact operator
`W^{k+1,p}(Ω) → W^{k,p}(Ω)` for every `k`. -/
theorem isCompactOperator_lowerOrderL_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    ∀ k : ℕ, IsCompactOperator (lowerOrderL (mu := volume) (Omega := Ω) (p := p) k) :=
  isCompactOperator_lowerOrderL_of_isCompactOperator_valueL
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb)

/-- On a bounded Lipschitz domain, a bounded sequence in `W^{k+1,p}(Ω)` has a subsequence whose
lower-order parts converge in `W^{k,p}(Ω)`, for `1 ≤ p ≤ ∞`. -/
theorem exists_subseq_tendsto_lowerOrder_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) (k : ℕ)
    {u : ℕ → Wkp volume Ω p (k + 1)} {R : ℝ} (hu : ∀ n, ‖u n‖ ≤ R) :
    ∃ w : Wkp volume Ω p k, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n ↦ lowerOrder k (u (φ n))) atTop (𝓝 w) := by
  obtain ⟨w, φ, hφ, hw⟩ :=
    (isCompactOperator_lowerOrderL_of_isLipschitzDomainWith hΩ hb k).exists_subseq_tendsto hu
  refine ⟨w, φ, hφ, ?_⟩
  simpa only [ContinuousLinearMap.coe_coe, lowerOrderL_apply k (u (φ _))] using hw

end Wkp

end TauCeti
