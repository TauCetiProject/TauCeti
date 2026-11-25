/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Elliptic.AdditionTheorem

/-!
# The marked lattice curve of an upper-half-plane point

For `z ∈ ℍ`, the Weierstrass model of `ℂ / (ℤ z + ℤ)` with the point represented by `1 / N`
is `UpperHalfPlane.pointedWeierstrassCurve N z`. This representative construction is shared by
the moduli comparison and Tate uniformization. That the marked point has exact order `N` at
positive level is in `TauCeti.Analysis.SpecialFunctions.Elliptic.Gamma1.ExactOrder`.
-/

public section

open Complex TauCeti

namespace UpperHalfPlane

variable {N : ℕ}

variable (N) in
/-- The complex elliptic curve `E_z = ℂ / (ℤ z + ℤ)`, in its Weierstrass model
`y² = x³ - (g₂ / 4) x - g₃ / 4`, with the point given by `1 / N`. For `N ≠ 0` this point has exact
order `N` (`UpperHalfPlane.addOrderOf_weierstrassPoint_one_div`). -/
noncomputable def pointedWeierstrassCurve (z : ℍ) : PointedWeierstrassCurve ℂ :=
  ⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (1 / N)⟩

/-- The defining equation of `UpperHalfPlane.pointedWeierstrassCurve`. -/
theorem pointedWeierstrassCurve_def (z : ℍ) :
    z.pointedWeierstrassCurve N =
      ⟨z.periodPair.weierstrassCurve, z.periodPair.weierstrassPoint (1 / N)⟩ :=
  (rfl)

@[simp]
theorem pointedWeierstrassCurve_curve (z : ℍ) :
    (z.pointedWeierstrassCurve N).curve = z.periodPair.weierstrassCurve :=
  (rfl)

/-- The marked point of `UpperHalfPlane.pointedWeierstrassCurve` is the point of `1 / N`, after
transport along `UpperHalfPlane.pointedWeierstrassCurve_curve`. -/
theorem pointedWeierstrassCurve_point (z : ℍ) :
    cast (congrArg (fun V : WeierstrassCurve ℂ ↦ V.toAffine.Point)
        (pointedWeierstrassCurve_curve (N := N) z)) (z.pointedWeierstrassCurve N).point =
      z.periodPair.weierstrassPoint (1 / N) :=
  (rfl)

end UpperHalfPlane
