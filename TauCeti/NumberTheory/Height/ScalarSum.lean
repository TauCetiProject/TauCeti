/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Height.ProjectiveTuple
public import TauCeti.NumberTheory.Height.FiniteOrder
import TauCeti.NumberTheory.NumberField.AdjoinPair

/-!
# The sum of the scalar heights of a tuple

The scalar-sum height `scalarSumHeight x = ∑ i, NumberField.absLogHeight₁ (x i)`
is invariant under coordinatewise inversion and subadditive under multiplication of
algebraic tuples. Unlike projective tuple height, it detects scaling of the coordinates.
It is comparable to the absolute affine logarithmic height by
`h_aff(x) ≤ scalarSumHeight x ≤ n * h_aff(x)`.

These comparisons allow affine height bounds to be used in multiplicative-group
packing arguments, where inversion invariance and a triangle inequality are needed.
The statements allow zero coordinates; their restriction to tuples of units gives
the usual height on an algebraic torus. Algebraicity is required for the upper comparison
and product bound, since the absolute heights have junk values on transcendental data.
The lower comparison holds for every tuple.

## References

* J.-H. Evertse, H. P. Schlickewei and W. M. Schmidt, *Linear equations in variables
  which lie in a multiplicative group*, Annals of Mathematics 155 (2002), §7,
  equations (7.4)–(7.7).
-/

public section

open NumberField Height Module

namespace TauCeti

variable {F F' : Type*} [Field F] [CharZero F] [Field F'] [CharZero F']
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- The sum of the absolute logarithmic heights of the coordinates of a finite tuple. -/
noncomputable def scalarSumHeight (x : ι → F) : ℝ :=
  ∑ i, absLogHeight₁ (x i)

/-- The defining sum for the scalar-sum height. -/
theorem scalarSumHeight_def (x : ι → F) :
    scalarSumHeight x = ∑ i, absLogHeight₁ (x i) :=
  (rfl)

/-- The scalar-sum height is nonnegative. -/
theorem scalarSumHeight_nonneg (x : ι → F) : 0 ≤ scalarSumHeight x :=
  Finset.sum_nonneg fun i _ ↦ zero_le_absLogHeight₁ (x i)

/-- The zero tuple has scalar-sum height zero. -/
@[simp]
theorem scalarSumHeight_zero : scalarSumHeight (0 : ι → F) = 0 := by
  simp [scalarSumHeight_def]

/-- The tuple of ones has scalar-sum height zero. -/
@[simp]
theorem scalarSumHeight_one : scalarSumHeight (1 : ι → F) = 0 := by
  simp [scalarSumHeight_def]

/-- A field embedding preserves the scalar-sum height. -/
@[simp]
theorem scalarSumHeight_comp (f : F →+* F') (x : ι → F) :
    scalarSumHeight (f ∘ x) = scalarSumHeight x := by
  simp [scalarSumHeight_def, Function.comp_def, absLogHeight₁_map]

/-- Reindexing by an equivalence preserves the scalar-sum height. -/
@[simp]
theorem scalarSumHeight_comp_equiv (e : κ ≃ ι) (x : ι → F) :
    scalarSumHeight (x ∘ e) = scalarSumHeight x :=
  Equiv.sum_comp e (fun i ↦ absLogHeight₁ (x i))

/-- Coordinatewise inversion preserves the scalar-sum height, including zero coordinates. -/
@[simp]
theorem scalarSumHeight_inv (x : ι → F) : scalarSumHeight x⁻¹ = scalarSumHeight x := by
  simp [scalarSumHeight_def, absLogHeight₁_inv]

/-- Coordinatewise natural powers multiply the scalar-sum height by the exponent. -/
@[simp]
theorem scalarSumHeight_pow (x : ι → F) (m : ℕ) :
    scalarSumHeight (x ^ m) = m * scalarSumHeight x := by
  simp [scalarSumHeight_def, absLogHeight₁_pow, Finset.mul_sum]

/-- Coordinatewise integer powers multiply the scalar-sum height by the absolute exponent. -/
@[simp]
theorem scalarSumHeight_zpow (x : ι → F) (m : ℤ) :
    scalarSumHeight (x ^ m) = m.natAbs * scalarSumHeight x := by
  cases m <;> simp [zpow_negSucc]

/-- An algebraic tuple has scalar-sum height zero exactly when each coordinate is zero
  or a root of unity. On a tuple of units, this is the torsion condition. -/
theorem scalarSumHeight_eq_zero_iff (x : ι → F) (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    scalarSumHeight x = 0 ↔ ∀ i, x i = 0 ∨ IsOfFinOrder (x i) := by
  simp only [scalarSumHeight_def,
    Finset.sum_eq_zero_iff_of_nonneg (fun i _ ↦ zero_le_absLogHeight₁ (x i)),
    Finset.mem_univ, forall_const]
  exact forall_congr' fun i ↦ absLogHeight₁_eq_zero_iff (hx i).isIntegral

/-- Over a number field, the scalar-sum height is the sum of the relative scalar heights
  divided by the field degree. -/
theorem scalarSumHeight_eq_div {K : Type*} [Field K] [NumberField K] (x : ι → K) :
    scalarSumHeight x = (∑ i, logHeight₁ (x i)) / finrank ℚ K := by
  simp [scalarSumHeight_def, absLogHeight₁_eq_div, Finset.sum_div]

/-- The scalar-sum height is subadditive under coordinatewise multiplication of algebraic
  tuples. No nonvanishing hypothesis on the coordinates is needed. -/
theorem scalarSumHeight_mul_le (x y : ι → F)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) (hy : ∀ i, IsAlgebraic ℚ (y i)) :
    scalarSumHeight (x * y) ≤ scalarSumHeight x + scalarSumHeight y := by
  let z : Sum ι ι → F := Sum.elim x y
  obtain ⟨K, hK, u, hu⟩ := exists_numberField_comp (x := z) (by
    intro i
    cases i with
    | inl i => exact hx i
    | inr i => exact hy i)
  let f := algebraMap K F
  have hxu : x = f ∘ (u ∘ Sum.inl) := funext fun i ↦ (congrFun hu (Sum.inl i)).symm
  have hyu : y = f ∘ (u ∘ Sum.inr) := funext fun i ↦ (congrFun hu (Sum.inr i)).symm
  have hxy : x * y = f ∘ ((u ∘ Sum.inl) * (u ∘ Sum.inr)) := by
    ext i
    simp [hxu, hyu]
  rw [hxy, hxu, hyu]
  simp only [scalarSumHeight_comp, scalarSumHeight_eq_div]
  rw [← add_div, ← Finset.sum_add_distrib]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_sum fun i _ ↦ logHeight₁_mul_le _ _) (Nat.cast_nonneg _)

/-- The absolute affine height of any tuple is at most its scalar-sum height. -/
theorem absoluteLogHeightAff_le_scalarSumHeight {n : ℕ} (x : Fin n → F) :
    absoluteLogHeightAff x ≤ scalarSumHeight x := by
  by_cases hx : ∀ i, IsAlgebraic ℚ (x i)
  · obtain ⟨K, f, y, rfl⟩ := exists_numberField_comp hx
    rw [absoluteLogHeightAff_comp, scalarSumHeight_comp,
      absoluteLogHeightAff_eq_logHeightAff_div, scalarSumHeight_eq_div]
    exact div_le_div_of_nonneg_right (logHeightAff_le_sum_logHeight₁ y) (Nat.cast_nonneg _)
  · obtain ⟨i, hi⟩ := not_forall.mp hx
    have h : ¬ IsIntegral ℚ ((Fin.cons 1 x : Fin (n + 1) → F) i.succ) := by
      simpa using fun h : IsIntegral ℚ (x i) ↦ hi h.isAlgebraic
    rw [absoluteLogHeightAff_def, absoluteProjectiveTupleHeight_of_not_isIntegral h, Real.log_one]
    exact scalarSumHeight_nonneg x

/-- The scalar-sum height of an algebraic `n`-tuple is at most `n` times its absolute
  affine logarithmic height. -/
theorem scalarSumHeight_le_mul_absoluteLogHeightAff {n : ℕ} (x : Fin n → F)
    (hx : ∀ i, IsAlgebraic ℚ (x i)) :
    scalarSumHeight x ≤ n * absoluteLogHeightAff x := by
  obtain ⟨K, f, y, rfl⟩ := exists_numberField_comp hx
  rw [absoluteLogHeightAff_comp, scalarSumHeight_comp,
    absoluteLogHeightAff_eq_logHeightAff_div, scalarSumHeight_eq_div, ← mul_div_assoc]
  refine div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)
  simpa using Finset.sum_le_sum (s := Finset.univ)
    (fun i _ ↦ logHeight₁_le_logHeightAff y i)

/-! The upper comparison constant is sharp already on rational two-tuples. -/

example : scalarSumHeight (![(2 : ℚ), 2]) = 2 * Real.log 2 := by
  have h2 : absLogHeight₁ (2 : ℚ) = Real.log 2 := absLogHeight₁_natCast 2
  simp [scalarSumHeight_def, Fin.sum_univ_two, h2, two_mul]

example : scalarSumHeight (![(2 : ℚ), (2 : ℚ)⁻¹]) = 2 * Real.log 2 := by
  have h2 : absLogHeight₁ (2 : ℚ) = Real.log 2 := absLogHeight₁_natCast 2
  simp [scalarSumHeight_def, Fin.sum_univ_two, absLogHeight₁_inv, h2, two_mul]

example : absoluteLogHeightAff (![(2 : ℚ), 2]) = Real.log 2 := by
  have h : logHeightAff (![(2 : ℚ), 2]) = logHeight₁ (2 : ℚ) := by
    apply le_antisymm
    · have hv : (![(2 : ℚ), 2]) = (![2] : Fin 1 → ℚ) ∘ (fun _ : Fin 2 ↦ 0) := by
        ext i
        fin_cases i <;> rfl
      rw [hv]
      simpa using logHeightAff_comp_le (fun _ : Fin 2 ↦ (0 : Fin 1)) (![2] : Fin 1 → ℚ)
    · exact logHeight₁_le_logHeightAff (![(2 : ℚ), 2]) (0 : Fin 2)
  rw [absoluteLogHeightAff_eq_logHeightAff_div, h, ← absLogHeight₁_eq_div]
  exact absLogHeight₁_natCast 2

end TauCeti
