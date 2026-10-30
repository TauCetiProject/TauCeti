/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import TauCeti.Analysis.InnerProductSpace.ProjValMeasure.Basic

/-!
# Orthogonal countable splitting for projection-valued measures

The diagonal scalar measure records the squared norm of the projection of a
Hilbert-space vector onto a measurable spectral region. For a countable
measurable partition, these squared norms sum to the squared norm of the
original vector. The identity applies to projection-valued measures on
arbitrary measurable spaces.

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

/-- Squared extended norm of a spectral projection equals the diagonal mass
of the corresponding measurable set. -/
@[simp]
theorem enorm_sq_proj_apply (P : ProjValMeasure X H) (B : Set X)
    (hB : MeasurableSet B) (ξ : H) :
    ‖P.proj B hB ξ‖ₑ ^ 2 = (P.diag ξ) B := by
  have hfin : (P.diag ξ) B ≠ ⊤ :=
    measure_ne_top (μ := P.diag ξ) (s := B)
  calc
    ‖P.proj B hB ξ‖ₑ ^ 2 = ENNReal.ofReal (‖P.proj B hB ξ‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    _ = ENNReal.ofReal (((P.diag ξ) B).toReal) := by
      rw [P.norm_sq_proj_apply B hB ξ]
    _ = (P.diag ξ) B := ENNReal.ofReal_toReal hfin

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
