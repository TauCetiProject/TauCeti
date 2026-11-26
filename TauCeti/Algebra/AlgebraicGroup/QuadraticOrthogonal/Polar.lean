/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Transpose

/-!
# The orthogonal group scheme of a quadratic form and of its polar form

Let `q` be a quadratic form on `Rⁿ` with coefficient matrix `M`, so `q(x) = xᵀ M x`, and let
`B = LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin` be the Gram matrix of its
polar form `b_q(x, y) = q(x + y) - q(x) - q(y)` (Mathlib's `QuadraticMap.polarBilin`), which is
`M + Mᵀ` (`QuadraticForm.toMatrix_polarBilin_eq_coefficientMatrix_add_transpose`). Every point of
`O(q)` preserves `b_q`: if `gᵀ M g - M` is alternating, then `gᵀ B g - B`, its sum with its
transpose, vanishes. When `2` is invertible the converse holds, since then `q(x) = ½ b_q(x, x)`.

When `B` is invertible with inverse `C`, a matrix `g` satisfies `gᵀ B g = B` exactly when
`g C gᵀ = C` (`Matrix.GeneralLinearGroup.mul_mul_transpose_eq_iff_transpose_mul_mul_eq`), the
defining relation of the constant-form subgroup scheme `TauCeti.ConstantForm.groupScheme R n C` in
Tau Ceti's row convention. So `O(q)` is a closed subgroup scheme of
`ConstantForm.groupScheme R n C` (`TauCeti.QuadraticOrthogonal.constantForm_definingHopfIdeal_le`),
and the two coincide when `2` is invertible in `R`
(`TauCeti.QuadraticOrthogonal.groupScheme_eq_constantForm`). In characteristic two the inclusion is
strict in general: over `𝔽₂`, for `q(x, y) = x y` the Gram matrix `B = [[0, 1], [1, 0]]` is its own
inverse, and `g = [[1, 1], [0, 1]]` satisfies `g B gᵀ = B` but sends `q` to `x y + y²`.

## Main declarations

* `TauCeti.QuadraticOrthogonal.transpose_mul_polarBilin_mul_of_mem`: points of `O(q)` preserve
  the polar form.
* `TauCeti.QuadraticOrthogonal.mem_pointsSubgroup_iff_transpose_mul_polarBilin_mul`: with `2`
  invertible, preserving the polar form characterizes `O(q)(A)`.
* `TauCeti.QuadraticOrthogonal.constantForm_definingHopfIdeal_le`: `O(q)` is a closed subgroup
  scheme of the subgroup scheme preserving `C = B⁻¹`.
* `TauCeti.QuadraticOrthogonal.definingHopfIdeal_eq_constantForm`,
  `TauCeti.QuadraticOrthogonal.groupScheme_eq_constantForm`: with `2` invertible, they coincide.

## References

* B. Conrad, *Reductive group schemes*, Appendix C, §C.1.
-/

public section

open CategoryTheory Matrix
open QuadraticForm (coefficientMatrix baseChangeForm baseChangeForm_apply
  toMatrix_polarBilin_eq_coefficientMatrix_add_transpose)

namespace TauCeti.QuadraticOrthogonal

universe u w

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ### The polar form -/

variable {q : QuadraticForm R (Fin n → R)} {A : Type w} [CommRing A] [Algebra R A]

/-- `gᵀ B g - B` is the sum of `gᵀ M g - M` and its transpose. -/
private theorem polar_relation (g : Matrix (Fin n) (Fin n) A) :
    gᵀ * (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map (algebraMap R A) *
          g -
        (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map (algebraMap R A) =
      (gᵀ * (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) * g -
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A)) +
        (gᵀ * (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) * g -
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A))ᵀ := by
  rw [toMatrix_polarBilin_eq_coefficientMatrix_add_transpose]
  simp only [Matrix.map_add _ (map_add (algebraMap R A)), transpose_sub, transpose_mul,
    transpose_transpose, transpose_map, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
  abel

/-- **Points of `O(q)` preserve the polar form**: if `g ∈ O(q)(A)`, then `gᵀ B g = B` for `B` the
Gram matrix of `QuadraticMap.polarBilin q`. -/
theorem transpose_mul_polarBilin_mul_of_mem {g : GL (Fin n) A}
    (hg : g ∈ pointsSubgroup R n q A) :
    (g : Matrix (Fin n) (Fin n) A)ᵀ *
          (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
            (algebraMap R A) *
        (g : Matrix (Fin n) (Fin n) A) =
      (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map (algebraMap R A) := by
  rw [← sub_eq_zero, polar_relation]
  have h := (mem_pointsSubgroup_iff_isAltMod g).mp hg
  ext i j
  rw [Matrix.add_apply, transpose_apply, Matrix.zero_apply]
  exact (Submodule.mem_bot A).mp (h.add_transpose_mem i j)

/-- **With `2` invertible, `O(q)(A)` is the group preserving the polar form**: `g ∈ O(q)(A)`
exactly when `gᵀ B g = B`, for `B` the Gram matrix of `QuadraticMap.polarBilin q`. -/
theorem mem_pointsSubgroup_iff_transpose_mul_polarBilin_mul [Invertible (2 : R)]
    (g : GL (Fin n) A) :
    g ∈ pointsSubgroup R n q A ↔
      (g : Matrix (Fin n) (Fin n) A)ᵀ *
            (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
              (algebraMap R A) *
          (g : Matrix (Fin n) (Fin n) A) =
        (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
          (algebraMap R A) := by
  refine ⟨transpose_mul_polarBilin_mul_of_mem, fun h ↦ ?_⟩
  rw [← sub_eq_zero, polar_relation] at h
  rw [mem_pointsSubgroup_iff_isAltMod]
  set N := (g : Matrix (Fin n) (Fin n) A)ᵀ *
    (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) *
      (g : Matrix (Fin n) (Fin n) A) -
    (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A)
  have hsum (i j : Fin n) : N i j + N j i = 0 := by
    simpa using congrFun (congrFun h i) j
  refine IsAltMod.of_mem (fun i ↦ ?_) fun i j ↦ by simpa using hsum i j
  have h2 : (2 : A) * N i i = 0 := by rw [two_mul]; exact hsum i i
  have hu : IsUnit (2 : A) := by
    have := (isUnit_of_invertible (2 : R)).map (algebraMap R A)
    rwa [map_ofNat] at this
  simpa using (hu.mul_right_eq_zero).mp h2

/-! ### Comparison with the constant-form subgroup scheme -/

/-- For `C` inverse to the Gram matrix `B` of the polar form, an ambient point lies in the subgroup
cut out by the Hopf ideal preserving `C` exactly when its matrix `g` satisfies `gᵀ B g = B`. -/
private theorem mem_constantForm_definingPointsSubgroup_iff {C : Matrix (Fin n) (Fin n) R}
    (hC : C * LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin = 1)
    (g : HopfAlgebra.points (R := R)
      (H := GeneralLinear.coordinateHopfAlgebra R n) (CommAlgCat.of R A)) :
    g ∈ CommHopfAlgCat.quotientPointsSubgroup
        (GeneralLinear.coordinateHopfAlgebra R n) (ConstantForm.definingHopfIdeal R n C)
        (CommAlgCat.of R A) ↔
      (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A)ᵀ *
            (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
              (algebraMap R A) *
          (GeneralLinear.pointsMulEquiv n g : Matrix (Fin n) (Fin n) A) =
        (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
          (algebraMap R A) := by
  rw [ConstantForm.mem_definingPointsSubgroup_iff,
    GeneralLinearGroup.mul_mul_transpose_eq_iff_transpose_mul_mul_eq
      (B := (LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin).map
        (algebraMap R A))
      (by rw [← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)])]

variable (q)

/-- **`O(q)` is a closed subgroup scheme of the group preserving the polar form**: if `C` is
inverse to the Gram matrix `B` of the polar form, the Hopf ideal of the subgroup scheme preserving
`C` (in the row convention `g C gᵀ = C`, that is `gᵀ B g = B`) is contained in that of `O(q)`. -/
theorem constantForm_definingHopfIdeal_le {C : Matrix (Fin n) (Fin n) R}
    (hC : C * LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin = 1) :
    ConstantForm.definingHopfIdeal R n C ≤ definingHopfIdeal R n q := by
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le]
  rintro ⟨A⟩ x hx
  rw [mem_constantForm_definingPointsSubgroup_iff hC]
  exact transpose_mul_polarBilin_mul_of_mem ((mem_definingPointsSubgroup_iff R n q A x).mp hx)

/-- **With `2` invertible, `O(q)` is the group preserving the polar form**: if `C` is inverse to
the Gram matrix `B` of the polar form, the Hopf ideal of `O(q)` is that of the subgroup scheme
preserving `C`. -/
theorem definingHopfIdeal_eq_constantForm [Invertible (2 : R)] {C : Matrix (Fin n) (Fin n) R}
    (hC : C * LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin = 1) :
    definingHopfIdeal R n q = ConstantForm.definingHopfIdeal R n C := by
  refine le_antisymm ?_ (constantForm_definingHopfIdeal_le q hC)
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le]
  rintro ⟨A⟩ x hx
  rw [mem_definingPointsSubgroup_iff, mem_pointsSubgroup_iff_transpose_mul_polarBilin_mul]
  exact (mem_constantForm_definingPointsSubgroup_iff hC x).mp hx

/-- **With `2` invertible, `O(q)` is the subgroup scheme preserving `C = B⁻¹`**, for `B` the Gram
matrix of the polar form: as closed subgroup schemes of `GLₙ`, `O(q)` and
`ConstantForm.groupScheme R n C` are equal. -/
theorem groupScheme_eq_constantForm [Invertible (2 : R)] {C : Matrix (Fin n) (Fin n) R}
    (hC : C * LinearMap.BilinForm.toMatrix (Pi.basisFun R (Fin n)) q.polarBilin = 1) :
    groupScheme R n q = ConstantForm.groupScheme R n C := by
  unfold groupScheme ConstantForm.groupScheme
  rw [definingHopfIdeal_eq_constantForm q hC]

end TauCeti.QuadraticOrthogonal
