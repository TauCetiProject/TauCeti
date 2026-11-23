/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Orthogonal countable splitting for projection-valued measures

For a countable measurable partition, the squared extended norms of the
spectral projections of a Hilbert-space vector sum to the squared extended norm
of the original vector (`tsum_enorm_sq_proj`). The identity applies to
projection-valued measures on arbitrary measurable spaces.

Adapted from Kitware's DKPS formalization in
`ForTauCeti/Analysis/InnerProductSpace/ProjValMeasure/Additivity.lean`.
-/

public section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

namespace ProjValMeasure

/-- For a countable measurable partition, the squared extended norms of the
projected components sum to the squared extended norm of the original vector. -/
theorem tsum_enorm_sq_proj (P : ProjValMeasure X H) {ι : Type*} [Countable ι]
    (B : ι → Set X) (hB : ∀ k, MeasurableSet (B k))
    (hdisj : Pairwise (Function.onFun Disjoint B)) (hcov : (⋃ k, B k) = Set.univ)
    (ξ : H) :
    ∑' k, ‖P.proj (B k) (hB k) ξ‖ₑ ^ 2 = ‖ξ‖ₑ ^ 2 := by
  calc
    ∑' k, ‖P.proj (B k) (hB k) ξ‖ₑ ^ 2 = ∑' k, (P.diag ξ) (B k) := by
      exact tsum_congr (fun k => P.enorm_sq_proj_apply (B k) (hB k) ξ)
    _ = (P.diag ξ) (⋃ k, B k) := (measure_iUnion hdisj hB).symm
    _ = (P.diag ξ) Set.univ := by rw [hcov]
    _ = ‖ξ‖ₑ ^ 2 := P.diag_univ ξ

end ProjValMeasure
end TauCeti
