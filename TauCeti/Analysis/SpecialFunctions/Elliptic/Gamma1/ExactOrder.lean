/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.Pointed
import TauCeti.Analysis.SpecialFunctions.Elliptic.Torsion

/-!
# The marked point of an upper-half-plane point has exact order `N`

At positive level `N`, the point given by `1 / N` on `E_z = ℂ / (ℤ z + ℤ)` has exact order `N`
(`UpperHalfPlane.addOrderOf_weierstrassPoint_one_div`), so the marked lattice curve
`UpperHalfPlane.pointedWeierstrassCurve N z` belongs to
`TauCeti.PointedWeierstrassCurve.exactOrder ℂ N`
(`UpperHalfPlane.pointedWeierstrassCurve_mem_exactOrder`). Both follow from the order of the
division points of a basis period (`PeriodPair.addOrderOf_weierstrassPoint_latticeBasis_div`).
-/

public section

open Complex TauCeti

namespace UpperHalfPlane

variable {N : ℕ}

/-- The point of `1 / N` on `E_z` has exact order `N`. -/
theorem addOrderOf_weierstrassPoint_one_div [NeZero N] (z : ℍ) :
    addOrderOf (z.periodPair.weierstrassPoint (1 / N)) = N := by
  simpa using z.periodPair.addOrderOf_weierstrassPoint_latticeBasis_div N 1

/-- The pair `(E_z, P_z)` is an elliptic curve with a point of exact order `N`. -/
theorem pointedWeierstrassCurve_mem_exactOrder [NeZero N] (z : ℍ) :
    z.pointedWeierstrassCurve N ∈ PointedWeierstrassCurve.exactOrder ℂ N := by
  rw [pointedWeierstrassCurve_def, PointedWeierstrassCurve.mem_exactOrder_iff]
  exact ⟨inferInstanceAs z.periodPair.weierstrassCurve.IsElliptic,
    addOrderOf_weierstrassPoint_one_div z⟩

end UpperHalfPlane
