/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Compactness
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness

/-!
# Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `1 ≤ p < ∞`, the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. Unlike `TauCeti.W1p0.isCompactOperator_valueL`, this
concerns the whole Sobolev space, with no vanishing boundary values. The boundary regularity enters
only through the extension operator `TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the
value map factors as extension to the whole space followed by restriction to `Ω`, and the latter is
compact by local Rellich compactness (`TauCeti.W1p.isCompactOperator_valueL_restrictL`), since
`closure Ω` is compact.

Compactness then gives the Poincaré–Wirtinger inequality on bounded connected Lipschitz domains,
with a constant that is not explicit.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`.
* `TauCeti.W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith`: the
  Poincaré–Wirtinger inequality on a bounded connected Lipschitz domain.

## References

* L. C. Evans, *Partial Differential Equations*, 2nd ed., §5.7, Theorem 1, and §5.8.1, Theorem 1.
-/

public section

noncomputable section

open Bornology MeasureTheory Set TopologicalSpace
open scoped ENNReal NNReal

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {Ω : Opens (WithLp 2 (ℝ × E))} {L : ℝ≥0} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **Rellich–Kondrachov on bounded Lipschitz domains.** If `Ω` is a bounded Lipschitz domain and
`1 ≤ p < ∞`, the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hK := W1p.isCompactOperator_valueL_restrictL (mu := volume) (Omega := ⊤) (V := Ω) hp
    hb.isCompact_closure (subset_univ _)
  -- The value map is the value of the restriction of the extension.
  have heq : W1p.valueL (mu := volume) (Omega := Ω) (p := p) =
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)).comp T := by
    rw [ContinuousLinearMap.comp_assoc, hT, ContinuousLinearMap.comp_id]
  rw [heq]
  exact hK.comp_clm T

/-- **The Poincaré–Wirtinger inequality on bounded connected Lipschitz domains.** Let `Ω` be a
bounded, preconnected Lipschitz domain, let `S ⊆ Ω` have positive measure, and let `1 ≤ p < ∞`.
There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at
most `C` times the `Lᵖ` norm of its weak gradient. -/
theorem W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith (hp : p ≠ ∞)
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    {S : Set (WithLp 2 (ℝ × E))} (hS : S ⊆ Ω) (hS0 : volume S ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p volume Ω p,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y) p (volume.restrict Ω) ≤
        ENNReal.ofReal C * ‖W1p.gradient u‖ₑ :=
  W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hp hΩ hb) hconn
    hb.measure_lt_top.ne hS hS0

end TauCeti

end
