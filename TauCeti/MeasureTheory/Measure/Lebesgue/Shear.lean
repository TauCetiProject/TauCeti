/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Shears preserve Lebesgue measure on `ℝ × ℝ` and `ℝ × ℝ × ℝ`

A shear adds to one coordinate a multiple of another, which leaves Lebesgue measure unchanged:
on each fibre it is a translation. Composed with a translation, it gives an affine map of
determinant one. These are the coordinate forms of left and right multiplication in the real
Heisenberg group.

## Main results

* `TauCeti.measurePreserving_shear`: `(y, z) ↦ (y + b, z + c + a y)` preserves Lebesgue measure
  on `ℝ × ℝ`.
* `TauCeti.measurePreserving_affine`: `(x, y, z) ↦ (x + a, y + b, z + c + d x)` preserves Lebesgue
  measure on `ℝ × ℝ × ℝ`.
* `TauCeti.measurePreserving_affine'`: `(x, y, z) ↦ (x + a, y + b, z + c + d y)` preserves
  Lebesgue measure on `ℝ × ℝ × ℝ`.
-/

public section

open MeasureTheory

namespace TauCeti

/-- On `ℝ × ℝ`, the shear `(y, z) ↦ (y + b, z + c + a y)` preserves Lebesgue measure. -/
theorem measurePreserving_shear (a b c : ℝ) :
    MeasurePreserving (fun q : ℝ × ℝ ↦ (q.1 + b, q.2 + c + a * q.1)) volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) b).skew_product
    (μc := (volume : Measure ℝ)) (μd := (volume : Measure ℝ))
    (g := fun (y z : ℝ) ↦ z + (c + a * y)) (by fun_prop)
    (Filter.Eventually.of_forall fun y ↦ (measurePreserving_add_right volume _).map_eq)
  rw [← Measure.volume_eq_prod] at h
  convert h using 2 with q
  simp [add_assoc]

/-- On `ℝ × ℝ × ℝ`, the map `(x, y, z) ↦ (x + a, y + b, z + c + d x)` preserves Lebesgue measure:
on each fibre over `x` it is a translation of `ℝ × ℝ`. -/
theorem measurePreserving_affine (a b c d : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + d * p.1))
      volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).skew_product
    (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
    (g := fun (x : ℝ) (q : ℝ × ℝ) ↦ q + (b, c + d * x)) (by fun_prop)
    (Filter.Eventually.of_forall fun x ↦
      (measurePreserving_add_right ((volume : Measure ℝ).prod volume) _).map_eq)
  rw [← Measure.volume_eq_prod] at h
  convert h using 2 with p
  simp [Prod.ext_iff, add_assoc]

/-- On `ℝ × ℝ × ℝ`, the map `(x, y, z) ↦ (x + a, y + b, z + c + d y)` preserves Lebesgue measure:
it is a translation of `x` composed with the shear `measurePreserving_shear` of `(y, z)`. -/
theorem measurePreserving_affine' (a b c d : ℝ) :
    MeasurePreserving (fun p : ℝ × ℝ × ℝ ↦ (p.1 + a, p.2.1 + b, p.2.2 + c + d * p.2.1))
      volume volume := by
  have h := (measurePreserving_add_right (volume : Measure ℝ) a).skew_product
    (μc := (volume : Measure (ℝ × ℝ))) (μd := (volume : Measure (ℝ × ℝ)))
    (g := fun (_ : ℝ) (q : ℝ × ℝ) ↦ (q.1 + b, q.2 + c + d * q.1)) (by fun_prop)
    (Filter.Eventually.of_forall fun _ ↦ (measurePreserving_shear d b c).map_eq)
  rwa [← Measure.volume_eq_prod] at h

end TauCeti
