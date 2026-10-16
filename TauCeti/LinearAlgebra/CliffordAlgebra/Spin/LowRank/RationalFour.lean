/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Invertible
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.LowRank.NonsplitCenter
public import TauCeti.LinearAlgebra.QuadraticForm.Diagonal.Basic

import Mathlib.Data.Nat.Prime.Int
import TauCeti.Algebra.Squarefree

/-!
# A rational quaternary Spin group with nonsplit center

Consider the rational diagonal quadratic form

```text
  x² + y² + z² + 2w².
```

Its discriminant is `2`, which is not a square in `ℚ`. Consequently the center of its even
Clifford algebra is the quadratic field `ℚ[X] ⧸ (X² - 2)`, rather than the split algebra
`ℚ × ℚ`. The general quaternary nonsplit-center construction then identifies its Spin group
with the norm-one group of a quaternion algebra over this quadratic center.

## Main results

* `TauCeti.rationalNonsplitQuaternaryForm` is the form `x² + y² + z² + 2w²` over `ℚ`.
* `TauCeti.rationalNonsplitQuaternaryCenterEquiv` identifies its even-Clifford center with
  `ℚ[X] ⧸ (X² - 2)`.
* `TauCeti.exists_rationalNonsplitQuaternarySpinEquivQuaternionUnitaryOverCenter` presents its
  Spin group as a quaternionic norm-one group over that center.

## References

* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §15.
-/

public section

open scoped Quaternion

namespace TauCeti

open Polynomial

/-- The rational diagonal quadratic form `x² + y² + z² + 2w²`. -/
noncomputable def rationalNonsplitQuaternaryForm : QuadraticForm ℚ (Fin 4 → ℚ) :=
  QuadraticMap.weightedSumSquares ℚ ![1, 1, 1, 2]

/-- The coordinate formula for the rational nonsplit quaternary form. -/
@[simp]
theorem rationalNonsplitQuaternaryForm_apply (v : Fin 4 → ℚ) :
    rationalNonsplitQuaternaryForm v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 + 2 * v 3 ^ 2 := by
  simp [rationalNonsplitQuaternaryForm, QuadraticMap.weightedSumSquares_apply,
    Fin.sum_univ_succ, pow_two]
  ring

/-- The discriminant of `x² + y² + z² + 2w²` is `2`. -/
@[simp]
theorem rationalNonsplitQuaternaryForm_discr' :
    QuadraticForm.discr' rationalNonsplitQuaternaryForm = 2 := by
  rw [rationalNonsplitQuaternaryForm]
  calc
    QuadraticForm.discr' (QuadraticMap.weightedSumSquares ℚ ![1, 1, 1, 2]) =
        ∏ i, (![1, 1, 1, 2] : Fin 4 → ℚ) i :=
      QuadraticForm.discr'_weightedSumSquares _
    _ = 2 := by norm_num [Fin.prod_univ_succ]

/-- The rational form `x² + y² + z² + 2w²` is nondegenerate. -/
@[simp]
theorem nondegenerate_rationalNonsplitQuaternaryForm :
    rationalNonsplitQuaternaryForm.Nondegenerate := by
  apply QuadraticMap.nondegenerate_weightedSumSquares
  intro i
  exact isRegular_iff_ne_zero.mpr (by fin_cases i <;> norm_num)

private noncomputable abbrev e4 (i : Fin 4) : Fin 4 → ℚ :=
  Pi.basisFun ℚ (Fin 4) i

private noncomputable def basisList4 : List (Fin 4 → ℚ) :=
  [e4 0, e4 1, e4 2, e4 3]

private theorem basisList4_pairwise :
    basisList4.Pairwise rationalNonsplitQuaternaryForm.IsOrtho := by
  simp [basisList4, e4, QuadraticMap.isOrtho_def,
    rationalNonsplitQuaternaryForm_apply, Pi.basisFun_apply]

private theorem basisList4_span :
    Submodule.span ℚ {x | x ∈ basisList4} = ⊤ := by
  apply top_unique
  rw [← (Pi.basisFun ℚ (Fin 4)).span_eq]
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  fin_cases i <;> simp [basisList4, e4]

private theorem basisList4_values_nonzero :
    ∀ v ∈ basisList4, rationalNonsplitQuaternaryForm v ≠ 0 := by
  intro v hv
  simp only [basisList4, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    simp [rationalNonsplitQuaternaryForm_apply, e4, Pi.basisFun_apply]

private theorem basisList4_discriminant :
    (-1 : ℚ) ^ basisList4.length.choose 2 *
      (basisList4.map rationalNonsplitQuaternaryForm).prod = 2 := by
  norm_num [basisList4, rationalNonsplitQuaternaryForm_apply, e4, Pi.basisFun_apply,
    Nat.choose]

private theorem not_isSquare_basisList4_discriminant :
    ¬ IsSquare ((-1 : ℚ) ^ basisList4.length.choose 2 *
      (basisList4.map rationalNonsplitQuaternaryForm).prod) := by
  rw [basisList4_discriminant]
  simpa only [Int.cast_ofNat] using
    (not_isSquare_intCast_of_squarefree_of_ne_one (n := 2)
      Int.prime_two.squarefree (by norm_num))

/-- The center of the even Clifford algebra of `x² + y² + z² + 2w²` is
the quadratic algebra `ℚ[X] ⧸ (X² - 2)`. -/
noncomputable def rationalNonsplitQuaternaryCenterEquiv :
    AdjoinRoot (X ^ 2 - C (2 : ℚ)) ≃ₐ[ℚ]
      Subalgebra.center ℚ (CliffordAlgebra.even rationalNonsplitQuaternaryForm) := by
  have h := CliffordAlgebra.adjoinRootEquivCenterEven basisList4_pairwise (by decide)
    (by simp [basisList4]) basisList4_span basisList4_values_nonzero
  rw [basisList4_discriminant] at h
  exact h

/-- The center of the even Clifford algebra of `x² + y² + z² + 2w²` is a field. -/
theorem isField_center_even_rationalNonsplitQuaternaryForm :
    IsField (Subalgebra.center ℚ (CliffordAlgebra.even rationalNonsplitQuaternaryForm)) := by
  rw [CliffordAlgebra.isField_center_even_iff_not_isSquare_discriminant
    basisList4_pairwise (by decide) (by simp [basisList4]) basisList4_span
      basisList4_values_nonzero]
  exact not_isSquare_basisList4_discriminant

/-- The center of the even Clifford algebra of `x² + y² + z² + 2w²` is not the split
quadratic algebra `ℚ × ℚ`. -/
theorem not_nonempty_center_even_rationalNonsplitQuaternaryForm_algEquiv_prod :
    ¬ Nonempty (Subalgebra.center ℚ (CliffordAlgebra.even rationalNonsplitQuaternaryForm) ≃ₐ[ℚ]
      ℚ × ℚ) := by
  rw [CliffordAlgebra.nonempty_center_even_algEquiv_prod_iff_isSquare_discriminant
    basisList4_pairwise (by decide) (by simp [basisList4]) basisList4_span
      basisList4_values_nonzero]
  exact not_isSquare_basisList4_discriminant

/-- The Spin group of `x² + y² + z² + 2w²` is the norm-one group of a quaternion algebra
over its quadratic field center. -/
theorem exists_rationalNonsplitQuaternarySpinEquivQuaternionUnitaryOverCenter :
    ∃ a b : (Subalgebra.center ℚ
        (CliffordAlgebra.even rationalNonsplitQuaternaryForm))ˣ,
      Nonempty (spinGroup rationalNonsplitQuaternaryForm ≃*
        unitary ℍ[Subalgebra.center ℚ
          (CliffordAlgebra.even rationalNonsplitQuaternaryForm),(a : _),0,(b : _)]) := by
  exact CliffordAlgebra.exists_spinGroupEquivQuaternionUnitaryOverCenter_of_finrank_eq_four
    rationalNonsplitQuaternaryForm nondegenerate_rationalNonsplitQuaternaryForm
      (by rw [Module.finrank_fin_fun]) isField_center_even_rationalNonsplitQuaternaryForm

end TauCeti
