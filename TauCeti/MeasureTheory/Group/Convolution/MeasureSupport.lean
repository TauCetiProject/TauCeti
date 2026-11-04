/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.MeasureTheory.Group.Convolution.Power
public import TauCeti.MeasureTheory.Measure.Dirac

/-!
# Topological support of measure convolution

The support of a multiplicative convolution is the closure of the pointwise product of the
two supports, provided those supports have full measure. The additive versions give the
corresponding statements for sums. A concentration lemma transports almost-everywhere
membership through convolution. This permits support arguments for sums of independent jumps
without moment or density assumptions.
Finite sums of support points lie in the support of the matching convolution power.
-/

public section

open MeasureTheory Set Topology
open scoped Pointwise

namespace MeasureTheory.Measure

variable {M : Type*} [Monoid M] [MeasurableSpace M] [MeasurableMul₂ M]
  {μ ν : Measure M} [SFinite ν]

/-- Multiplicative convolution concentrates on any measurable set containing the pointwise
product of sets on which its factors concentrate. -/
@[to_additive /-- Additive convolution concentrates on any measurable set containing the
pointwise sum of sets on which its factors concentrate. -/]
theorem ae_mem_mconv_of_ae_mem {S T C : Set M} (hC : MeasurableSet C) (hST : S * T ⊆ C)
    (hS : ∀ᵐ x ∂μ, x ∈ S) (hT : ∀ᵐ y ∂ν, y ∈ T) : ∀ᵐ z ∂μ ∗ₘ ν, z ∈ C := by
  rw [mconv]
  apply (ae_map_iff measurable_mul.aemeasurable hC).2
  apply (ae_prod_iff_ae_ae (hC.preimage measurable_mul)).2
  filter_upwards [hS] with x hx
  exact hT.mono fun y hy ↦ hST (Set.mul_mem_mul hx hy)

variable [TopologicalSpace M] [ContinuousMul M] [OpensMeasurableSpace M]

/-- A product of support points belongs to the support of the multiplicative convolution. -/
@[to_additive /-- A sum of support points belongs to the support of the convolution. -/]
theorem mul_mem_support_mconv {x y : M} (hx : x ∈ μ.support) (hy : y ∈ ν.support) :
    x * y ∈ (μ ∗ₘ ν).support := by
  rw [support_eq_forall_isOpen]
  intro U hxy hU
  have hpre : (fun p : M × M ↦ p.1 * p.2) ⁻¹' U ∈ 𝓝 (x, y) :=
    continuous_mul.continuousAt.preimage_mem_nhds (hU.mem_nhds hxy)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hpre
  rw [mconv, map_apply measurable_mul hU.measurableSet]
  have hp : 0 < (μ.prod ν) (s ×ˢ t) := by
    rw [prod_prod]
    exact ENNReal.mul_pos ((mem_support_iff_forall x).mp hx s hs).ne'
      ((mem_support_iff_forall y).mp hy t ht).ne'
  exact hp.trans_le (measure_mono hst)

/-- When the factor supports are conull, the multiplicative convolution support is the closure
of their pointwise product. -/
@[to_additive /-- When the factor supports are conull, the convolution support is the closure
of their pointwise sum. The closure is necessary even for finite measures on the real line. -/]
theorem support_mconv (hμ : μ.support ∈ ae μ) (hν : ν.support ∈ ae ν) :
    (μ ∗ₘ ν).support = closure (μ.support * ν.support) := by
  apply Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    exact ae_mem_mconv_of_ae_mem isClosed_closure.measurableSet subset_closure hμ hν
  · apply closure_minimal _ isClosed_support
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact mul_mem_support_mconv hx hy

variable {A : Type*} [AddMonoid A] [TopologicalSpace A] [ContinuousAdd A]
  [MeasurableSpace A] [OpensMeasurableSpace A] [MeasurableAdd₂ A]

/-- A finite sum of support points of `μ` belongs to the support of
`μ.convolutionPower l.length`; the empty list gives the zeroth power (`dirac 0`). -/
theorem list_sum_mem_support_convolutionPower (μ : Measure A) [SFinite μ] (l : List A) :
    (∀ x ∈ l, x ∈ μ.support) → l.sum ∈ (μ.convolutionPower l.length).support := by
  induction l with
  | nil =>
    intro _
    simp only [List.sum_nil, List.length_nil, convolutionPower_zero, support_dirac]
    exact subset_closure (mem_singleton 0)
  | cons x l ih =>
    intro hl
    rw [List.sum_cons, List.length_cons, convolutionPower_succ']
    exact add_mem_support_conv (hl x List.mem_cons_self)
      (ih fun y hy ↦ hl y (List.mem_cons_of_mem x hy))

end MeasureTheory.Measure
