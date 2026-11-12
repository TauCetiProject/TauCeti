/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Topology.Order.OrderStatistic
public import TauCeti.MeasureTheory.Measure.Support

/-!
# Topological support of iid order statistics

Sorting an iid sample gives precisely the monotone tuples with entries in the source support
as the topological support of its joint law. This description retains ties and boundary points,
even for an atomless source, and applies to disconnected and unbounded supports. The joint
statement includes the empty sample. Each individual order statistic has the same support as
the source law.

The results hold for sigma-finite measures, without probability or atomlessness assumptions.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §2.1.
-/

public section

open MeasureTheory Set TauCeti

namespace MeasureTheory.Measure

variable {α : Type*} [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
  [SecondCountableTopology α] [MeasurableSpace α] [BorelSpace α]
  {n : ℕ} (μ : Measure α) [SigmaFinite μ]

/-- The joint support of the sorted iid sample consists of all monotone tuples in the source
support. In particular ties remain in the support, even when they have probability zero. -/
@[simp]
theorem support_map_orderStatistics_pi :
    ((Measure.pi fun _ : Fin n ↦ μ).map (fun x i ↦ orderStatistic i x)).support =
      {x | Monotone x ∧ ∀ i, x i ∈ μ.support} := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae (by fun_prop),
    Measure.support_pi]
  have himage : (fun x i ↦ orderStatistic i x) '' (univ.pi fun _ : Fin n ↦ μ.support) =
      {x | Monotone x ∧ ∀ i, x i ∈ μ.support} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [orderStatistic_def, mem_ofPred_eq, Function.comp_def] using
        And.intro (Tuple.monotone_sort y) (fun i ↦ (mem_univ_pi.mp hy) (Tuple.sort y i))
    · rintro ⟨hx, hs⟩
      refine ⟨x, mem_univ_pi.mpr hs, ?_⟩
      funext i
      simpa only [orderStatistic_def, Function.comp_apply, Equiv.coe_refl, id_eq] using
        congrFun (Tuple.unique_monotone (τ := Equiv.refl _) (Tuple.monotone_sort x) hx) i
  rw [himage]
  have hclosed : IsClosed {x : Fin n → α | Monotone x ∧ ∀ i, x i ∈ μ.support} := by
    simpa only [ofPred_and, ofPred_forall, preimage] using isClosed_monotone.inter
      (isClosed_iInter fun i : Fin n ↦ μ.isClosed_support.preimage (continuous_apply i))
  exact hclosed.closure_eq

/-- Every individual iid order statistic has exactly the source law's topological support.
The index guarantees that the sample is nonempty. -/
@[simp]
theorem support_map_orderStatistic_pi (k : Fin n) :
    ((Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic k)).support = μ.support := by
  rw [Measure.support_map_eq_closure_image _ Measure.support_mem_ae
    (continuous_orderStatistic k), Measure.support_pi]
  have himage : orderStatistic k '' (univ.pi fun _ : Fin n ↦ μ.support) = μ.support := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [orderStatistic_def] using (mem_univ_pi.mp hy) (Tuple.sort y k)
    · intro hx
      exact ⟨fun _ ↦ x, mem_univ_pi.mpr (fun _ ↦ hx), by simp [orderStatistic_def]⟩
  rw [himage, μ.isClosed_support.closure_eq]

end MeasureTheory.Measure
