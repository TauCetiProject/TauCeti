/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.LipschitzDomain.GlobalExtension
public import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Compactness
public import TauCeti.Analysis.Sobolev.GraphStep.ScalarProjection
import TauCeti.Analysis.Sobolev.W1p.LocalCompactness
import TauCeti.MeasureTheory.Function.Lp.FiniteDimensional

/-!
# Rellich–Kondrachov on bounded Lipschitz domains

For a bounded Lipschitz domain `Ω ⊆ ℝ × E` and `1 ≤ p ≤ ∞`, the value map
`W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. Unlike `TauCeti.W1p0.isCompactOperator_valueL`, this
concerns the whole Sobolev space, with no vanishing boundary values. The boundary regularity enters
only through the extension operator `TauCeti.W1p.exists_extensionL_of_isLipschitzDomainWith`: the
value map factors as extension to the whole space followed by restriction to `Ω`, and the latter is
compact by local Rellich compactness (`TauCeti.W1p.isCompactOperator_valueL_restrictL`), since
`closure Ω` is compact. At `p = ∞`, the local compactness theorem uses Arzelà–Ascoli for
the uniformly bounded equi-Lipschitz whole-space representatives.

Applied coordinatewise through the scalar projections `TauCeti.WeakDerivStep.toW1pL`, the same
compactness holds for the field selected by a weak-derivative graph space with finite-dimensional
target. This is the input for the higher-order statement.

Compactness then gives the Poincaré–Wirtinger inequality on bounded connected Lipschitz domains,
with a constant that is not explicit.

## Main declarations

* `TauCeti.W1p.isCompactOperator_valueL_of_isLipschitzDomainWith`: Rellich–Kondrachov
  compactness of `W^{1,p}(Ω) → Lᵖ(Ω)`.
* `TauCeti.WeakDerivStep.isCompactOperator_comp_prevL_of_isLipschitzDomainWith`: compactness of a
  finite-dimensional weak-derivative graph field into `Lᵖ(Ω; F)`.
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
`1 ≤ p ≤ ∞`, the value map `W^{1,p}(Ω) → Lᵖ(Ω)` is a compact operator. -/
theorem W1p.isCompactOperator_valueL_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (W1p.valueL (mu := volume) (Omega := Ω) (p := p)) := by
  obtain ⟨T, hT⟩ := W1p.exists_extensionL_of_isLipschitzDomainWith (p := p) hΩ hb
  have hK : IsCompactOperator
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)) :=
    W1p.isCompactOperator_valueL_restrictL hb.isCompact_closure (subset_univ _)
  -- The value map is the value of the restriction of the extension.
  have heq : W1p.valueL (mu := volume) (Omega := Ω) (p := p) =
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (W1p.restrictL le_top)).comp T := by
    rw [ContinuousLinearMap.comp_assoc, hT, ContinuousLinearMap.comp_id]
  rw [heq]
  exact hK.comp_clm T

namespace WeakDerivStep

variable {F X : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [SeminormedAddCommGroup X] [NormedSpace ℝ X]

/-- On a bounded Lipschitz domain, the field selected by `base` is compact as a map from the
weak-derivative graph space into `Lᵖ(Ω; F)`, for finite-dimensional `F` and `1 ≤ p ≤ ∞`. -/
theorem isCompactOperator_comp_prevL_of_isLipschitzDomainWith
    (base : X →L[ℝ] Lp F p (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E)))) :
    IsCompactOperator (base.comp (prevL base)) := by
  classical
  let b := Module.finBasis ℝ F
  let ℓ := fun i ↦ (b.coord i).toContinuousLinearMap
  let C := fun i ↦ ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL
    p (volume.restrict (Ω : Set (WithLp 2 (ℝ × E))))).comp
      ((W1p.valueL (mu := volume) (Omega := Ω) (p := p)).comp (toW1pL base (ℓ i)))
  have hC (i) : IsCompactOperator (C i) :=
    ((W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb).comp_clm
      (toW1pL base (ℓ i))).clm_comp
        ((ContinuousLinearMap.toSpanSingleton ℝ (b i)).compLpL p
          (volume.restrict (Ω : Set (WithLp 2 (ℝ × E)))))
  have heq : base.comp (prevL base) = ∑ i, C i := by
    apply ContinuousLinearMap.ext
    intro u
    simpa only [sum_apply, C, ContinuousLinearMap.comp_apply,
      W1p.valueL_apply, value_toW1pL, prevL_apply, ℓ] using
      eq_sum_basis_compLpL b (base (prev base u))
  rw [heq]
  -- Compact operators form a submodule, so finite coordinate reconstruction preserves compactness.
  exact (compactOperator (RingHom.id ℝ) _ _).sum_mem fun i _ ↦ hC i

end WeakDerivStep

/-- **The Poincaré–Wirtinger inequality on bounded connected Lipschitz domains.** Let `Ω` be a
bounded, preconnected Lipschitz domain, let `S ⊆ Ω` have positive measure, and let `1 ≤ p ≤ ∞`.
There is a constant `C` such that every `u ∈ W^{1,p}(Ω)` deviates from its mean over `S` by at
most `C` times the `Lᵖ` norm of its weak gradient. -/
theorem W1p.exists_eLpNorm_value_sub_setAverage_le_of_isLipschitzDomainWith
    (hΩ : (Ω : Set (WithLp 2 (ℝ × E))).IsLipschitzDomainWith L)
    (hb : IsBounded (Ω : Set (WithLp 2 (ℝ × E))))
    (hconn : IsPreconnected (Ω : Set (WithLp 2 (ℝ × E))))
    {S : Set (WithLp 2 (ℝ × E))} (hS : S ⊆ Ω) (hS0 : volume S ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : W1p volume Ω p,
      eLpNorm (fun x ↦ W1p.value u x - ⨍ y in S, W1p.value u y) p (volume.restrict Ω) ≤
        ENNReal.ofReal C * ‖W1p.gradient u‖ₑ :=
  W1p.exists_eLpNorm_value_sub_setAverage_le_of_isCompactOperator
    (W1p.isCompactOperator_valueL_of_isLipschitzDomainWith hΩ hb) hconn
    hb.measure_lt_top.ne hS hS0

end TauCeti

end
