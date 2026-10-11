/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CrossProduct

/-!
# Vectors with vanishing cross product

Complements to `Mathlib.LinearAlgebra.CrossProduct`. Over a field, two nonzero vectors of `K³`
have vanishing cross product exactly when they are proportional
(`Projectivization.mk_eq_mk_iff_crossProduct_eq_zero`). Over a commutative ring `R`, the
coordinates of `v ⨯₃ w` are the `2 × 2` minors of the matrix with rows `v` and `w`, and when they
vanish and both vectors have a unit coordinate, `v` is a unit multiple of `w`.

## Main results

* `TauCeti.exists_eq_units_smul_of_crossProduct_eq_zero`: if `v ⨯₃ w = 0` and `v` and `w` each
  have a unit coordinate, then `v = u • w` for a unit `u`.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/AdditionChartGlue.lean`: `ratio_eq_of_minor`
and `isUnit_of_minor`, combined as `exists_eq_units_smul_of_crossProduct_eq_zero`. Here the
vanishing of the `2 × 2` minors is stated as the vanishing of the cross product.
-/

public section

open Matrix

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- Let `v` and `w` be vectors of `R³`, over a commutative ring `R`, each with a unit coordinate.
If `v ⨯₃ w = 0`, then `v` is a unit multiple of `w`. -/
theorem exists_eq_units_smul_of_crossProduct_eq_zero {v w : Fin 3 → R} (h : v ⨯₃ w = 0)
    {k l : Fin 3} (hv : IsUnit (v k)) (hw : IsUnit (w l)) : ∃ u : Rˣ, v = u • w := by
  -- the coordinates of `v ⨯₃ w` are the `2 × 2` minors of the matrix with rows `v` and `w`
  have hvw (a : Fin 3) : v a * w l = v l * w a := by
    simp only [cross_apply, cons_eq_zero_iff] at h
    fin_cases a <;> fin_cases l <;> grind
  -- hence `v = (v l / w l) • w`
  have hu : v = (v l * ↑hw.unit⁻¹) • w := funext fun a ↦ by
    rw [Pi.smul_apply, smul_eq_mul, mul_right_comm, ← hvw a, mul_assoc, hw.mul_val_inv, mul_one]
  -- and `v l / w l` is a unit since `v k = (v l / w l) * w k` is
  exact ⟨(isUnit_of_mul_isUnit_left (congrFun hu k ▸ hv)).unit, hu⟩

end TauCeti
