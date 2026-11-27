/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Group.Prod

/-!
# Shears preserve Lebesgue measure on `ℝ × ℝ` and `ℝ × ℝ × ℝ`

A shear adds to one coordinate a multiple of another, which leaves Lebesgue measure unchanged:
on each fibre it is a translation. Composed with a translation, it gives an affine map of
determinant one. These are the coordinate forms of left and right multiplication in the real
Heisenberg group. All three results specialise `TauCeti.measurePreserving_skew_add_right`.

## Main results

* `TauCeti.measurePreserving_prod_add_shear`: `(y, z) ↦ (y + b, z + c + a y)` preserves Lebesgue
  measure on `ℝ × ℝ`.
* `TauCeti.measurePreserving_prod3_add_shear_fst`: `(x, y, z) ↦ (x + a, y + b, z + c + d x)`
  preserves Lebesgue measure on `ℝ × ℝ × ℝ`.
* `TauCeti.measurePreserving_prod3_add_shear_snd`: `(x, y, z) ↦ (x + a, y + b, z + c + d y)`
  preserves Lebesgue measure on `ℝ × ℝ × ℝ`.
-/

public section

open MeasureTheory

namespace TauCeti

/-- On `ℝ × ℝ`, the translated shear `(y, z) ↦ (y + b, z + c + a y)` preserves Lebesgue measure. -/
theorem measurePreserving_prod_add_shear (a b c : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + b, q.2 + c + a * q.1)) volume volume := by
  simp_rw [add_assoc _ c, Measure.volume_eq_prod]
  exact measurePreserving_skew_add_right volume volume b (g := fun y ↦ c + a * y) (by fun_prop)

/-- On `ℝ × ℝ × ℝ`, the translated shear `(x, y, z) ↦ (x + a, y + b, z + c + d x)`, sheared along
the first coordinate, preserves Lebesgue measure: on each fibre over `x` it is a translation of
`ℝ × ℝ`. -/
theorem measurePreserving_prod3_add_shear_fst (a b c d : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + d * p.1))
      volume volume := by
  have h := measurePreserving_skew_add_right volume ((volume : Measure ℝ).prod volume) a
    (g := fun x ↦ (b, c + d * x)) (by fun_prop)
  rw [← Measure.volume_eq_prod, ← Measure.volume_eq_prod] at h
  convert h using 2 with p
  simp [Prod.ext_iff, add_assoc]

/-- On `ℝ × ℝ × ℝ`, the translated shear `(x, y, z) ↦ (x + a, y + b, z + c + d y)`, sheared along
the second coordinate, preserves Lebesgue measure: it is the product of a translation of `x` and
the shear `measurePreserving_prod_add_shear` of `(y, z)`. -/
theorem measurePreserving_prod3_add_shear_snd (a b c d : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + d * p.2.1))
      volume volume := by
  rw [Measure.volume_eq_prod]
  exact (measurePreserving_add_right volume a).prod (measurePreserving_prod_add_shear d b c)

end TauCeti
