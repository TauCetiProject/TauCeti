/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.RowCompact
public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.BaseChange

/-!
# Row compactness under coefficient extension

Extending an operator on `C₀` along a bounded unital coefficient homomorphism multiplies each
row norm by at most the homomorphism bound and preserves row compactness.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS **12** (1962), 69–85, §§2–3.
-/

public section

open Filter Topology
open scoped ZeroAtInfty NNReal

namespace ContinuousLinearMap

variable {I J R S : Type*}
  [TopologicalSpace I] [DiscreteTopology I]
  [TopologicalSpace J] [DiscreteTopology J] [DecidableEq J]
  [NormedCommRing R] [TauCeti.NormedRing.IsTate R]
  [NormedCommRing S] [IsUltrametricDist S] [CompleteSpace S]

/-- Coefficient extension multiplies each row norm by at most the homomorphism bound. -/
theorem rowNorm_mapCoeffs_le (u : C₀(J, R) →L[R] C₀(I, R)) (f : R →+* S)
    (C : ℝ≥0) (hf : ∀ r, ‖f r‖ ≤ C * ‖r‖) (i : I) :
    (u.mapCoeffs f ⟨C, hf⟩).rowNorm i ≤ C * u.rowNorm i := by
  apply rowNorm_le_of_forall_le (mul_nonneg C.coe_nonneg (u.rowNorm_nonneg i))
  intro j
  exact (u.norm_matrixCoeff_mapCoeffs_le f C hf i j).trans
    (mul_le_mul_of_nonneg_left (u.norm_matrixCoeff_le_rowNorm i j) C.coe_nonneg)

/-- Row compactness is preserved by bounded coefficient extension. -/
theorem IsRowCompact.mapCoeffs {u : C₀(J, R) →L[R] C₀(I, R)} (hu : u.IsRowCompact)
    (f : R →+* S) (hf : ∃ C : ℝ≥0, ∀ r, ‖f r‖ ≤ C * ‖r‖) :
    (u.mapCoeffs f hf).IsRowCompact := by
  obtain ⟨C, hC⟩ := hf
  apply isRowCompact_of_norm_matrixCoeff_le
    (by simpa using hu.tendsto_rowNorm.const_mul (C : ℝ))
  intro i j
  exact (u.norm_matrixCoeff_mapCoeffs_le f C hC i j).trans
    (mul_le_mul_of_nonneg_left (hu.norm_matrixCoeff_le_rowNorm i j) C.coe_nonneg)

end ContinuousLinearMap
