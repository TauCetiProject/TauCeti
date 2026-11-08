/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.LKJ.Basic
public import Mathlib.MeasureTheory.Measure.Support

/-!
# Topological support of the LKJ law

At positive shape, the LKJ law on `p × p` symmetric matrices has topological support the set of
correlation matrices: the positive-semidefinite symmetric matrices with unit diagonal. The law is
concentrated on the positive-definite correlation matrices, and its density is positive there,
but its support also contains the singular correlation matrices on the boundary.

In strictly lower correlation coordinates, the density is positive exactly on the open region
`TauCeti.posDefCorrelationRegion p`, and the closure of that region is the region of
positive-semidefinite correlation matrices (`TauCeti.closure_posDefCorrelationRegion`).

## References

* D. Lewandowski, D. Kurowicka, H. Joe, *Generating random correlation matrices based on vines
  and extended onion method*, J. Multivariate Anal. 100 (2009), 1989--2001.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti.Probability

variable {p : ℕ} {η : ℝ}

/-- At positive shape, the topological support of the LKJ law is the set of correlation
matrices: the positive-semidefinite symmetric matrices with unit diagonal. -/
@[simp]
theorem support_lkjMeasure (hη : 0 < η) :
    (lkjMeasure p η).support =
      {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1} := by
  refine Subset.antisymm ?_ ?_
  · have hclosed : IsClosed {R : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) |
        (R : Matrix (Fin p) (Fin p) ℝ).PosSemidef ∧
          ∀ i, (R : Matrix (Fin p) (Fin p) ℝ) i i = 1} := by
      simp only [ofPred_and, ofPred_forall]
      exact (isClosed_setOfPred_posSemidef.preimage continuous_subtype_val).inter <|
        isClosed_iInter fun i ↦ isClosed_eq (continuous_subtype_val.matrix_elem i i)
          continuous_const
    refine Measure.support_subset_of_isClosed hclosed ?_
    filter_upwards [ae_posDef_lkjMeasure p η, ae_diag_eq_one_lkjMeasure p η] with R hR hdiag
    exact ⟨hR.posSemidef, hdiag⟩
  · rintro R ⟨hR, hdiag⟩
    obtain ⟨x, rfl⟩ : R ∈ range (correlationMatrix p) := by
      rw [range_correlationMatrix]
      exact hdiag
    have hx : x ∈ closure (posDefCorrelationRegion p) := by
      rw [closure_posDefCorrelationRegion]
      exact hR
    rw [Measure.mem_support_iff_forall]
    intro U hU
    obtain ⟨V, hVU, hV, hxV⟩ := mem_nhds_iff.mp
      ((correlationMatrix p).continuous.continuousAt.preimage_mem_nhds hU)
    obtain ⟨y, hyV, hy⟩ := mem_closure_iff.mp hx V hV hxV
    rw [lkjMeasure_of_pos hη, pos_iff_ne_zero, Ne,
      withDensity_apply_eq_zero (measurable_lkjPDF p η), correlationLebesgue_apply]
    refine ((hV.inter (isOpen_posDefCorrelationRegion p)).measure_ne_zero volume
      ⟨y, hyV, hy⟩) ∘ measure_mono_null fun z hz ↦ ?_
    exact ⟨(lkjPDF_pos_iff hη).mpr (mem_posDefCorrelationRegion.mp hz.2) |>.ne', hVU hz.1⟩

end TauCeti.Probability
