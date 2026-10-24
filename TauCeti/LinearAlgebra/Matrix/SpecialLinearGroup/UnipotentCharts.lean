/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Transvection

/-!
# Two upper-unipotent charts of `SL₂`

The first-column map has sections `sₐ = [[a, 0], [c, a⁻¹]]` when `a` is a unit and
`s꜀ = [[a, -c⁻¹], [c, 0]]` when `c` is a unit. Right multiplication by
`n(t) = [[1, t], [0, 1]]` gives mutually inverse parameterizations of the corresponding
matrix charts, over every commutative ring. Their fiber coordinates are `a⁻¹b` and `c⁻¹d`.
On the overlap the sections differ by `n(-a⁻¹c⁻¹)` and the fiber coordinates satisfy
`u꜀ = uₐ + a⁻¹c⁻¹`.

The formulas commute with changes of rings and intertwine right upper-unipotent translation
with addition in the fiber coordinate. These are the algebra-valued chart formulas for the
first-column additive torsor. This file does not construct the scheme chart isomorphisms.
Over a general ring a unimodular pair need not have either coordinate a unit, so these two
charts are used locally on the base rather than as a cover of its set of ring-valued points.

## References

* I. Hedén, *Affine extensions of principal additive bundles over a punctured surface*,
  arXiv:1407.7638, §§1 and 3.
-/

public section

open scoped MatrixGroups

namespace Matrix.SpecialLinearGroup

universe u v

variable {R : Type u} [CommRing R]

/-- The first-column section on the chart where the upper-left coordinate is a unit. -/
def firstColumnSectionA (a : Rˣ) (c : R) : SL(2, R) :=
  ⟨!![(a : R), 0; c, (a⁻¹ : Rˣ)], by simp [Matrix.det_fin_two_of]⟩

/-- The matrix of the first section. -/
@[simp]
theorem coe_firstColumnSectionA (a : Rˣ) (c : R) :
    (firstColumnSectionA a c : Matrix (Fin 2) (Fin 2) R) =
      !![(a : R), 0; c, (a⁻¹ : Rˣ)] :=
  (rfl)

/-- The first-column section on the chart where the lower-left coordinate is a unit. -/
def firstColumnSectionC (a : R) (c : Rˣ) : SL(2, R) :=
  ⟨!![a, -(c⁻¹ : Rˣ); (c : R), 0], by simp [Matrix.det_fin_two_of]⟩

/-- The matrix of the second section. -/
@[simp]
theorem coe_firstColumnSectionC (a : R) (c : Rˣ) :
    (firstColumnSectionC a c : Matrix (Fin 2) (Fin 2) R) =
      !![a, -(c⁻¹ : Rˣ); (c : R), 0] :=
  (rfl)

/-- The first section followed by upper-unipotent translation. -/
theorem coe_firstColumnSectionA_mul_transvection (a : Rˣ) (c t : R) :
    ((firstColumnSectionA a c * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t :
      SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![(a : R), t * a; c, (a⁻¹ : Rˣ) + t * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm]

/-- The second section followed by upper-unipotent translation. -/
theorem coe_firstColumnSectionC_mul_transvection (a : R) (c : Rˣ) (t : R) :
    ((firstColumnSectionC a c * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t :
      SL(2, R)) : Matrix (Fin 2) (Fin 2) R) =
      !![a, -(c⁻¹ : Rˣ) + t * a; (c : R), t * c] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [coe_mul, transvection_coe, Matrix.mul_apply, Fin.sum_univ_two, mul_comm, add_comm]

/-- Recover a matrix in the upper-left chart from its first column and fiber coordinate. -/
theorem firstColumnSectionA_mul_transvection_eq (g : SL(2, R)) (a : Rˣ)
    (ha : g 0 0 = a) :
    firstColumnSectionA a (g 1 0) * transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
      ((a⁻¹ : Rˣ) * g 0 1) = g := by
  have hdet := g.2
  rw [Matrix.det_fin_two, ha] at hdet
  apply Subtype.ext
  rw [coe_firstColumnSectionA_mul_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
  · exact ha.symm
  · simp [mul_assoc, mul_comm (g 0 1)]
  · linear_combination -(↑(a⁻¹) : R) * hdet + g 1 1 * a.inv_mul

/-- Recover a matrix in the lower-left chart from its first column and fiber coordinate. -/
theorem firstColumnSectionC_mul_transvection_eq (g : SL(2, R)) (c : Rˣ)
    (hc : g 1 0 = c) :
    firstColumnSectionC (g 0 0) c * transvection (zero_ne_one : (0 : Fin 2) ≠ 1)
      ((c⁻¹ : Rˣ) * g 1 1) = g := by
  have hdet := g.2
  rw [Matrix.det_fin_two, hc] at hdet
  apply Subtype.ext
  rw [coe_firstColumnSectionC_mul_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [Matrix.of_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one]
  · linear_combination (↑(c⁻¹) : R) * hdet + g 0 1 * c.inv_mul
  · exact hc.symm
  · simp [mul_assoc, mul_comm (g 1 1)]

/-- Coordinates on the matrix chart where the upper-left entry is a unit.
The last coordinate is the additive fiber parameter. -/
noncomputable def upperLeftChartEquiv :
    {g : SL(2, R) // IsUnit (g 0 0)} ≃ Rˣ × R × R where
  toFun g := (g.property.unit, g.val 1 0, (g.property.unit⁻¹ : Rˣ) * g.val 0 1)
  invFun p := ⟨firstColumnSectionA p.1 p.2.1 * transvection zero_ne_one p.2.2, by
    simpa only [coe_firstColumnSectionA_mul_transvection, Matrix.of_apply,
      Matrix.cons_val_zero] using p.1.isUnit⟩
  left_inv g := Subtype.ext (firstColumnSectionA_mul_transvection_eq g.val g.property.unit
    g.property.unit_spec.symm)
  right_inv p := by
    rcases p with ⟨a, c, t⟩
    simp only [coe_firstColumnSectionA_mul_transvection, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    congr 1
    · apply Units.val_injective
      exact IsUnit.unit_spec _
    · simp [mul_comm t, ← mul_assoc]

/-- The upper-left chart records the invertible entry, the other first-column entry,
and `a⁻¹b`. -/
theorem upperLeftChartEquiv_apply (g : {g : SL(2, R) // IsUnit (g 0 0)}) :
    upperLeftChartEquiv g =
      (g.property.unit, g.val 1 0, (g.property.unit⁻¹ : Rˣ) * g.val 0 1) :=
  (rfl)

/-- The inverse upper-left chart is multiplication of its section by `n(t)`. -/
@[simp]
theorem upperLeftChartEquiv_symm_apply (a : Rˣ) (c t : R) :
    ((upperLeftChartEquiv (R := R)).symm (a, c, t)).val =
      firstColumnSectionA a c * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t :=
  (rfl)

/-- Coordinates on the matrix chart where the lower-left entry is a unit.
The last coordinate is the additive fiber parameter. -/
noncomputable def lowerLeftChartEquiv :
    {g : SL(2, R) // IsUnit (g 1 0)} ≃ R × Rˣ × R where
  toFun g := (g.val 0 0, g.property.unit, (g.property.unit⁻¹ : Rˣ) * g.val 1 1)
  invFun p := ⟨firstColumnSectionC p.1 p.2.1 * transvection zero_ne_one p.2.2, by
    simpa only [coe_firstColumnSectionC_mul_transvection, Matrix.of_apply,
      Matrix.cons_val_one, Matrix.cons_val_zero] using p.2.1.isUnit⟩
  left_inv g := Subtype.ext (firstColumnSectionC_mul_transvection_eq g.val g.property.unit
    g.property.unit_spec.symm)
  right_inv p := by
    rcases p with ⟨a, c, t⟩
    simp only [coe_firstColumnSectionC_mul_transvection, Matrix.of_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one]
    simp [mul_comm t, ← mul_assoc]

/-- The lower-left chart records the first-column entries and `c⁻¹d`. -/
theorem lowerLeftChartEquiv_apply (g : {g : SL(2, R) // IsUnit (g 1 0)}) :
    lowerLeftChartEquiv g =
      (g.val 0 0, g.property.unit, (g.property.unit⁻¹ : Rˣ) * g.val 1 1) :=
  (rfl)

/-- The inverse lower-left chart is multiplication of its section by `n(t)`. -/
@[simp]
theorem lowerLeftChartEquiv_symm_apply (a : R) (c : Rˣ) (t : R) :
    ((lowerLeftChartEquiv (R := R)).symm (a, c, t)).val =
      firstColumnSectionC a c * transvection (zero_ne_one : (0 : Fin 2) ≠ 1) t :=
  (rfl)

/-- Right upper-unipotent translation adds to the upper-left fiber coordinate. -/
theorem upperLeftChartEquiv_symm_add (a : Rˣ) (c t s : R) :
    ((upperLeftChartEquiv (R := R)).symm (a, c, t + s)).val =
      ((upperLeftChartEquiv (R := R)).symm (a, c, t)).val *
        transvection (zero_ne_one : (0 : Fin 2) ≠ 1) s := by
  simp only [upperLeftChartEquiv_symm_apply, transvection_add, mul_assoc]

/-- Right upper-unipotent translation adds to the lower-left fiber coordinate. -/
theorem lowerLeftChartEquiv_symm_add (a : R) (c : Rˣ) (t s : R) :
    ((lowerLeftChartEquiv (R := R)).symm (a, c, t + s)).val =
      ((lowerLeftChartEquiv (R := R)).symm (a, c, t)).val *
        transvection (zero_ne_one : (0 : Fin 2) ≠ 1) s := by
  simp only [lowerLeftChartEquiv_symm_apply, transvection_add, mul_assoc]

/-- On the overlap, the lower-left section is the upper-left section translated by
`-a⁻¹c⁻¹`. -/
theorem firstColumnSectionC_eq_sectionA_mul_transvection (a c : Rˣ) :
    firstColumnSectionC (a : R) c = firstColumnSectionA a (c : R) *
      transvection (zero_ne_one : (0 : Fin 2) ≠ 1) (-((a⁻¹ : Rˣ) : R) * (c⁻¹ : Rˣ)) := by
  apply Subtype.ext
  rw [coe_firstColumnSectionC, coe_firstColumnSectionA_mul_transvection]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Fin.zero_eta, Fin.mk_one, neg_mul]
  · linear_combination (↑(c⁻¹) : R) * a.inv_mul
  · linear_combination (↑(a⁻¹) : R) * c.mul_inv

/-- The additive fiber coordinates differ by `a⁻¹c⁻¹` on the overlap. -/
theorem firstColumn_fiberCoordinate_transition (g : SL(2, R)) (a c : Rˣ)
    (ha : g 0 0 = a) (hc : g 1 0 = c) :
    (c⁻¹ : Rˣ) * g 1 1 = (a⁻¹ : Rˣ) * g 0 1 + (a⁻¹ : Rˣ) * (c⁻¹ : Rˣ) := by
  have hdet := g.2
  rw [Matrix.det_fin_two, ha, hc] at hdet
  linear_combination (↑(a⁻¹) : R) * (↑(c⁻¹) : R) * hdet -
    (↑(c⁻¹) : R) * g 1 1 * a.inv_mul + (↑(a⁻¹) : R) * g 0 1 * c.inv_mul

variable {S : Type v} [CommRing S]

/-- The upper-left section is natural under change of rings. -/
@[simp]
theorem map_firstColumnSectionA (f : R →+* S) (a : Rˣ) (c : R) :
    map f (firstColumnSectionA a c) = firstColumnSectionA (Units.map f a) (f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_apply_coe]

/-- The lower-left section is natural under change of rings. -/
@[simp]
theorem map_firstColumnSectionC (f : R →+* S) (a : R) (c : Rˣ) :
    map f (firstColumnSectionC a c) = firstColumnSectionC (f a) (Units.map f c) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [map_apply_coe]

end Matrix.SpecialLinearGroup
