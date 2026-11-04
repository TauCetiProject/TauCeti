/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Pi.Norm
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Gauss norms and finite-coordinate presentations

Separating a finite tuple of coefficients is an isometry for the weighted Gauss norm and the
maximum norm on tuples of restricted series, and for ring-valued coordinates it identifies
restricted families with a finite free module over the native restricted-series ring
(`TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss.piRingLinearIsometryEquiv`, in
`TauCeti.RingTheory.MvPowerSeries.TateAlgebra.Module.Pi.Norm`).

Coefficient matrices act through the same matrices after this comparison, with entries included
as constant series. Thus finite free coefficient-module presentations can be transported to
Gauss-topological restricted families without changing their matrices or norms. These results
extend the algebraic comparisons in `Module.Pi`; no completeness is needed.

## References

* S. Bosch, U. Güntzer and R. Remmert, *Non-Archimedean Analysis*, §5.1.1.
-/

public section

noncomputable section

namespace TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss

open _root_.MvPowerSeries

variable {σ ι : Type*} [Fintype ι] {c : σ → ℝ} [∀ i, Fact (0 < c i)]

section Matrices

variable {κ K : Type*} [Fintype κ] [NormedCommRing K] [IsUltrametricDist K]

/-- A bounded coefficient matrix induces the same matrix on restricted series, with each
entry included as a constant series. This identifies the matrix in a transported finite free
presentation. The bound is on the coefficient map, not on individual entries. -/
theorem _root_.Matrix.piRingLinearIsometryEquiv_mapLinearMap (A : Matrix κ ι K) {C : ℝ}
    (hA : ∀ x, ‖A.mulVecLin x‖ ≤ C * ‖x‖) (a : Gauss c (ι → K)) :
    piRingLinearIsometryEquiv K c (mapLinearMap A.mulVecLin hA a) =
      (A.map (algebraMap K (IsRestricted.subring (R := K) c))).mulVec
        (piRingLinearIsometryEquiv K c a) := by
  ext i t
  simp [Matrix.mulVec, dotProduct, coe_algebraMap_isRestrictedSubring,
    _root_.MvPowerSeries.coeff_C_mul]

end Matrices

end TauCeti.MvPowerSeries.IsRestrictedFamily.Gauss
