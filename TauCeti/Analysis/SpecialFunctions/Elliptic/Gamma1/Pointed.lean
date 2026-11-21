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
is `UpperHalfPlane.pointedWeierstrassCurve N z`. At positive level the marked point has exact
order `N`, so the curve belongs to `TauCeti.PointedWeierstrassCurve.exactOrder ℂ N`.
This representative construction is shared by the moduli comparison and Tate uniformization.
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

/-- The point of `1 / N` on `E_z` has exact order `N`. -/
theorem addOrderOf_weierstrassPoint_one_div [NeZero N] (z : ℍ) :
    addOrderOf (z.periodPair.weierstrassPoint (1 / N)) = N := by
  have hN : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne N)
  refine (addOrderOf_eq_iff (Nat.pos_of_neZero N)).mpr ⟨?_, fun m hm hm₀ ↦ ?_⟩
  · rw [PeriodPair.nsmul_weierstrassPoint, mul_one_div_cancel hN,
      PeriodPair.weierstrassPoint_eq_zero_iff]
    simpa using z.periodPair.ω₂_mem_lattice
  · rw [PeriodPair.nsmul_weierstrassPoint, Ne, PeriodPair.weierstrassPoint_eq_zero_iff]
    intro hmem
    have h := congrFun (intCast_comp_eq_zero_of_div_mem_lattice_periodPair (N := N) (b := ![0, m])
      (z := z) (by convert hmem using 1; simp [div_eq_mul_inv])) 1
    simp only [Function.comp_apply, Matrix.cons_val_one, Matrix.cons_val_fin_one, Int.cast_natCast,
      Pi.zero_apply, ZMod.natCast_eq_zero_iff] at h
    exact absurd (Nat.le_of_dvd hm₀ h) (not_le.mpr hm)

/-- The pair `(E_z, P_z)` is an elliptic curve with a point of exact order `N`. -/
theorem pointedWeierstrassCurve_mem_exactOrder [NeZero N] (z : ℍ) :
    z.pointedWeierstrassCurve N ∈ PointedWeierstrassCurve.exactOrder ℂ N :=
  (PointedWeierstrassCurve.mem_exactOrder_iff _).mpr
    ⟨inferInstanceAs z.periodPair.weierstrassCurve.IsElliptic,
      addOrderOf_weierstrassPoint_one_div z⟩

end UpperHalfPlane
