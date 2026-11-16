/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Order
public import TauCeti.Geometry.Manifold.VectorBundle.Sobolev.Rellich

/-!
# Rellich compactness between any two orders

Let `M` be a smooth Hausdorff manifold without boundary modelled on a finite-dimensional real inner
product space `E`, let `V → M` be a smooth real vector bundle with finite-dimensional model fibre
`F`, and let `A` be a finite bundle atlas, so that `M` is compact. For `1 ≤ p < ∞` and orders
`l < k`, the inclusion `W^{k,p}(V) → W^{l,p}(V)` of `TauCeti.SectionChartData.ofOrderLEL` is a
compact operator. It is the one-step inclusion `W^{k,p}(V) → W^{k-1,p}(V)`, compact by Rellich's
theorem `TauCeti.SobolevSection.isCompactOperator_lowerOrderL`, followed by the continuous
inclusion `W^{k-1,p}(V) → W^{l,p}(V)`.

Composing further with the continuous inclusion `W^{k,q}(V) → W^{k,p}(V)` for `p ≤ q` of
`TauCeti.SectionChartData.ofExponentLEL` gives the compact inclusion `W^{k,q}(V) → W^{l,p}(V)`, for
any exponent `q ≥ p`, possibly `q = ∞`. With `l = 0` this is the compactness of
`W^{k,q}(V) → Lᵖ(V)` that turns an elliptic estimate into closed range and finite-dimensional
kernel.

## Main results

* `TauCeti.SobolevSection.isCompactOperator_ofOrderLEL`: **Rellich's theorem**, `W^{k,p}(V) →
  W^{l,p}(V)` is compact for `l < k`.
* `TauCeti.SobolevSection.isCompactOperator_ofOrderLEL_comp_ofExponentLEL`: `W^{k,q}(V) →
  W^{l,p}(V)` is compact for `l < k` and `p ≤ q`.

## References

* R. S. Palais, *Foundations of Global Non-linear Analysis*, Benjamin (1968), §9.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry*, Princeton (1989), Chapter III, Theorem 2.6.
-/

public section

noncomputable section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

universe u

namespace TauCeti

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {M : Type*}
  [TopologicalSpace M] [ChartedSpace E M] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)] [∀ x, TopologicalSpace (V x)]
  [FiberBundle F V] (A : FiniteBundleAtlas E M F V)

variable [IsManifold 𝓘(ℝ, E) ∞ M]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ F]
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [VectorBundle ℝ F V]
  [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, E)]

variable (μ : Measure E) [μ.IsAddHaarMeasure] {p : ℝ≥0∞} [Fact (1 ≤ p)] {l k : ℕ}

namespace SobolevSection

/-- **Rellich's theorem between any two orders.** On a compact manifold without boundary, given by
a finite bundle atlas of a Hausdorff manifold, the inclusion `W^{k,p}(V) → W^{l,p}(V)` is a compact
operator for all orders `l < k` and every `1 ≤ p < ∞`. -/
theorem isCompactOperator_ofOrderLEL [T2Space M] (hp : p ≠ ⊤) (hlk : l < k) :
    IsCompactOperator (A.sectionChartData.ofOrderLEL μ p hlk.le) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hlk)
  have hl : l ≤ k := Nat.le_of_lt_succ hlk
  convert (isCompactOperator_lowerOrderL A μ p k hp).clm_comp
    (A.sectionChartData.ofOrderLEL μ p hl) using 1
  funext w
  exact (SectionChartData.ofOrderLEL_lowerOrderL hl w).symm

/-- **Rellich's theorem with a change of exponent.** On a compact manifold without boundary, given
by a finite bundle atlas of a Hausdorff manifold, the inclusion `W^{k,q}(V) → W^{l,p}(V)` is a
compact operator for all orders `l < k` and exponents `1 ≤ p ≤ q` with `p < ∞`. -/
theorem isCompactOperator_ofOrderLEL_comp_ofExponentLEL [T2Space M] {q : ℝ≥0∞} [Fact (1 ≤ q)]
    (hp : p ≠ ⊤) (hpq : p ≤ q) (hlk : l < k) :
    IsCompactOperator ((A.sectionChartData.ofOrderLEL μ p hlk.le).comp
      (A.sectionChartData.ofExponentLEL μ k hpq)) :=
  (isCompactOperator_ofOrderLEL A μ hp hlk).comp_clm _

end SobolevSection

end TauCeti
