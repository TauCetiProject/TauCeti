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

The support of a convolution is the closure of the pointwise sum of the two supports,
provided those supports have full measure. In particular, every sum of two support points
has positive mass in each neighbourhood. This permits support arguments for sums of
independent jumps without moment or density assumptions.
-/

public section

open MeasureTheory Set Topology
open scoped Pointwise

namespace MeasureTheory.Measure

variable {A : Type*} [AddMonoid A] [TopologicalSpace A] [ContinuousAdd A]
  [MeasurableSpace A] [OpensMeasurableSpace A] [MeasurableAdd₂ A]
  {μ ν : Measure A} [SFinite ν]

/-- A sum of support points belongs to the support of the convolution. -/
theorem add_mem_support_conv {x y : A} (hx : x ∈ μ.support) (hy : y ∈ ν.support) :
    x + y ∈ (μ ∗ ν).support := by
  rw [support_eq_forall_isOpen]
  intro U hxy hU
  have hpre : (fun p : A × A ↦ p.1 + p.2) ⁻¹' U ∈ 𝓝 (x, y) :=
    continuous_add.continuousAt.preimage_mem_nhds (hU.mem_nhds hxy)
  obtain ⟨s, hs, t, ht, hst⟩ := mem_nhds_prod_iff.mp hpre
  rw [conv, map_apply measurable_add hU.measurableSet]
  have hp : 0 < (μ.prod ν) (s ×ˢ t) := by
    rw [prod_prod]
    exact ENNReal.mul_pos ((mem_support_iff_forall x).mp hx s hs).ne'
      ((mem_support_iff_forall y).mp hy t ht).ne'
  exact hp.trans_le (measure_mono hst)

/-- When the factor supports are conull, the convolution support is the closure of their
pointwise sum. The closure is necessary even for finite measures on the real line. -/
theorem support_conv (hμ : μ.support ∈ ae μ) (hν : ν.support ∈ ae ν) :
    (μ ∗ ν).support = closure (μ.support + ν.support) := by
  apply Subset.antisymm
  · apply support_subset_of_isClosed isClosed_closure
    rw [conv]
    apply (ae_map_iff (p := fun z ↦ z ∈ closure (μ.support + ν.support))
      measurable_add.aemeasurable isClosed_closure.measurableSet).2
    apply (ae_prod_iff_ae_ae (isClosed_closure.measurableSet.preimage measurable_add)).2
    filter_upwards [Filter.eventually_mem_set.mpr hμ] with x hx
    exact (Filter.eventually_mem_set.mpr hν).mono fun y hy ↦
      subset_closure (Set.add_mem_add hx hy)
  · apply closure_minimal _ isClosed_support
    rintro _ ⟨x, hx, y, hy, rfl⟩
    exact add_mem_support_conv hx hy

/-- A finite sum of jump-support points belongs to the support of the corresponding
convolution power, with the empty list giving the zeroth power. -/
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
