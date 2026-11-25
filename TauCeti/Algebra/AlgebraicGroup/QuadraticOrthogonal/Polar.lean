/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.QuadraticOrthogonal.Basic
public import TauCeti.Algebra.AlgebraicGroup.ConstantForm.Basic
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Order

/-!
# The orthogonal group scheme of a quadratic form and of its polar form

Let `q` be a quadratic form on `Rⁿ` with coefficient matrix `M`, so `q(x) = xᵀ M x`, and let
`B = M + Mᵀ` be the Gram matrix of its polar form `b_q(x, y) = q(x + y) - q(x) - q(y)`
(`TauCeti.QuadraticOrthogonal.polarMatrix`). Every point of `O(q)` preserves `b_q`: if
`gᵀ M g - M` is alternating, then `gᵀ B g - B`, its sum with its transpose, vanishes. When `2` is
invertible the converse holds, since then `q(x) = ½ b_q(x, x)`.

When `B` is invertible with inverse `C`, a matrix `g` satisfies `gᵀ B g = B` exactly when
`g C gᵀ = C`, the defining relation of the constant-form subgroup scheme
`TauCeti.ConstantForm.groupScheme R n C` in Tau Ceti's row convention. So `O(q)` is a closed
subgroup scheme of `ConstantForm.groupScheme R n C`
(`TauCeti.QuadraticOrthogonal.constantForm_definingHopfIdeal_le`), and the two coincide when `2`
is invertible in `R` (`TauCeti.QuadraticOrthogonal.groupScheme_eq_constantForm`). In characteristic
two the inclusion is strict in general: over `𝔽₂` the polar form of `x²` vanishes.

## Main declarations

* `TauCeti.QuadraticOrthogonal.polarMatrix`: the Gram matrix `M + Mᵀ` of the polar form.
* `TauCeti.QuadraticOrthogonal.transpose_mul_polarMatrix_mul_of_mem`: points of `O(q)` preserve
  the polar form.
* `TauCeti.QuadraticOrthogonal.mem_pointsSubgroup_iff_transpose_mul_polarMatrix_mul`: with `2`
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
open QuadraticForm (coefficientMatrix baseChangeForm baseChangeForm_apply)

namespace TauCeti.QuadraticOrthogonal

universe u w

variable {R : Type u} [CommRing R] {n : ℕ}

/-! ### The polar form -/

variable (q : QuadraticForm R (Fin n → R))

/-- The Gram matrix `B = M + Mᵀ` of the polar form `b_q(x, y) = q(x + y) - q(x) - q(y)` of a
quadratic form `q(x) = xᵀ M x` on `Rⁿ`, for `M` its coefficient matrix. -/
noncomputable def polarMatrix : Matrix (Fin n) (Fin n) R :=
  coefficientMatrix q (Pi.basisFun R (Fin n)) + (coefficientMatrix q (Pi.basisFun R (Fin n)))ᵀ

theorem polarMatrix_def :
    polarMatrix q =
      coefficientMatrix q (Pi.basisFun R (Fin n)) +
        (coefficientMatrix q (Pi.basisFun R (Fin n)))ᵀ := by
  rw [polarMatrix]

variable {q} {A : Type w} [CommRing A] [Algebra R A]

/-- `gᵀ B g - B` is the sum of `gᵀ M g - M` and its transpose. -/
private theorem polar_relation (g : Matrix (Fin n) (Fin n) A) :
    gᵀ * (polarMatrix q).map (algebraMap R A) * g - (polarMatrix q).map (algebraMap R A) =
      (gᵀ * (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) * g -
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A)) +
        (gᵀ * (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A) * g -
          (coefficientMatrix q (Pi.basisFun R (Fin n))).map (algebraMap R A))ᵀ := by
  rw [polarMatrix_def, Matrix.map_add _ (map_add (algebraMap R A)), transpose_sub,
    transpose_mul, transpose_mul, transpose_transpose, transpose_map, Matrix.mul_add,
    Matrix.add_mul, Matrix.mul_assoc gᵀ, Matrix.mul_assoc gᵀ]
  abel

/-- **Points of `O(q)` preserve the polar form**: if `g ∈ O(q)(A)`, then `gᵀ B g = B`. -/
theorem transpose_mul_polarMatrix_mul_of_mem {g : GL (Fin n) A}
    (hg : g ∈ pointsSubgroup R n q A) :
    (g : Matrix (Fin n) (Fin n) A)ᵀ * (polarMatrix q).map (algebraMap R A) *
        (g : Matrix (Fin n) (Fin n) A) =
      (polarMatrix q).map (algebraMap R A) := by
  rw [← sub_eq_zero, polar_relation]
  have h := (mem_pointsSubgroup_iff_isAltMod g).mp hg
  ext i j
  rw [Matrix.add_apply, transpose_apply, Matrix.zero_apply]
  exact (Submodule.mem_bot A).mp (h.add_transpose_mem i j)

/-- **With `2` invertible, `O(q)(A)` is the group preserving the polar form**: `g ∈ O(q)(A)`
exactly when `gᵀ B g = B`. -/
theorem mem_pointsSubgroup_iff_transpose_mul_polarMatrix_mul [Invertible (2 : R)]
    (g : GL (Fin n) A) :
    g ∈ pointsSubgroup R n q A ↔
      (g : Matrix (Fin n) (Fin n) A)ᵀ * (polarMatrix q).map (algebraMap R A) *
          (g : Matrix (Fin n) (Fin n) A) =
        (polarMatrix q).map (algebraMap R A) := by
  refine ⟨transpose_mul_polarMatrix_mul_of_mem, fun h ↦ ?_⟩
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

/-- For invertible `g` and `C B = 1`, `g C gᵀ = C` exactly when `gᵀ B g = B`. -/
private theorem mul_mul_transpose_eq_iff {B C : Matrix (Fin n) (Fin n) A} (hCB : C * B = 1)
    (g : GL (Fin n) A) :
    (g : Matrix (Fin n) (Fin n) A) * C * (g : Matrix (Fin n) (Fin n) A)ᵀ = C ↔
      (g : Matrix (Fin n) (Fin n) A)ᵀ * B * (g : Matrix (Fin n) (Fin n) A) = B := by
  have hBC : B * C = 1 := mul_eq_one_comm.mp hCB
  set G := (g : Matrix (Fin n) (Fin n) A)
  have hG : G * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hGt : Gᵀ * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ = 1 := by
    rw [← transpose_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, transpose_one]
  constructor
  · intro h
    -- `(Gᵀ B G) C Gᵀ = Gᵀ B (G C Gᵀ) = Gᵀ B C = Gᵀ`, so `(Gᵀ B G) C = 1`.
    have h1 : Gᵀ * B * G * C * Gᵀ = Gᵀ := by
      rw [Matrix.mul_assoc (Gᵀ * B * G), Matrix.mul_assoc (Gᵀ * B), ← Matrix.mul_assoc G, h,
        Matrix.mul_assoc, hBC, Matrix.mul_one]
    have h2 : Gᵀ * B * G * C = 1 := by
      have := congrArg (· * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)ᵀ) h1
      simpa only [Matrix.mul_assoc, hGt, Matrix.mul_one] using this
    calc Gᵀ * B * G = Gᵀ * B * G * C * B := by rw [Matrix.mul_assoc _ C, hCB, Matrix.mul_one]
      _ = B := by rw [h2, Matrix.one_mul]
  · intro h
    -- `(G C Gᵀ) B G = G C (Gᵀ B G) = G C B = G`, so `(G C Gᵀ) B = 1`.
    have h1 : G * C * Gᵀ * B * G = G := by
      rw [Matrix.mul_assoc (G * C * Gᵀ), Matrix.mul_assoc (G * C), ← Matrix.mul_assoc Gᵀ, h,
        Matrix.mul_assoc, hCB, Matrix.mul_one]
    have h2 : G * C * Gᵀ * B = 1 := by
      have := congrArg (· * ((g⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) h1
      simpa only [Matrix.mul_assoc, hG, Matrix.mul_one] using this
    calc G * C * Gᵀ = G * C * Gᵀ * B * C := by rw [Matrix.mul_assoc _ B, hBC, Matrix.mul_one]
      _ = C := by rw [h2, Matrix.one_mul]

variable (q)

/-- **`O(q)` is a closed subgroup scheme of the group preserving the polar form**: if `C` is
inverse to the Gram matrix `B` of the polar form, the Hopf ideal of the subgroup scheme preserving
`C` (in the row convention `g C gᵀ = C`, that is `gᵀ B g = B`) is contained in that of `O(q)`. -/
theorem constantForm_definingHopfIdeal_le {C : Matrix (Fin n) (Fin n) R}
    (hC : C * polarMatrix q = 1) :
    ConstantForm.definingHopfIdeal R n C ≤ definingHopfIdeal R n q := by
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le]
  intro A x hx
  obtain ⟨A⟩ := A
  have hmem : GeneralLinear.pointsMulEquiv n x ∈ pointsSubgroup R n q A := by
    rw [← hopfIdealPointsSubgroup_definingHopfIdeal, GeneralLinear.mem_hopfIdealPointsSubgroup_iff,
      MulEquiv.symm_apply_apply, ← CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
    exact hx
  rw [ConstantForm.mem_definingPointsSubgroup_iff,
    mul_mul_transpose_eq_iff (B := (polarMatrix q).map (algebraMap R A))
      (by rw [← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)])]
  exact transpose_mul_polarMatrix_mul_of_mem hmem

/-- **With `2` invertible, `O(q)` is the group preserving the polar form**: if `C` is inverse to
the Gram matrix `B` of the polar form, the Hopf ideal of `O(q)` is that of the subgroup scheme
preserving `C`. -/
theorem definingHopfIdeal_eq_constantForm [Invertible (2 : R)] {C : Matrix (Fin n) (Fin n) R}
    (hC : C * polarMatrix q = 1) :
    definingHopfIdeal R n q = ConstantForm.definingHopfIdeal R n C := by
  refine le_antisymm ?_ (constantForm_definingHopfIdeal_le q hC)
  rw [HopfIdeal.le_iff_forall_quotientPointsSubgroup_le]
  intro A x hx
  obtain ⟨A⟩ := A
  rw [ConstantForm.mem_definingPointsSubgroup_iff,
    mul_mul_transpose_eq_iff (B := (polarMatrix q).map (algebraMap R A))
      (by rw [← Matrix.map_mul, hC, Matrix.map_one _ (map_zero _) (map_one _)]),
    ← mem_pointsSubgroup_iff_transpose_mul_polarMatrix_mul,
    ← hopfIdealPointsSubgroup_definingHopfIdeal, GeneralLinear.mem_hopfIdealPointsSubgroup_iff,
    MulEquiv.symm_apply_apply] at hx
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  exact hx

/-- **With `2` invertible, `O(q)` is the subgroup scheme preserving `C = B⁻¹`**, for `B` the Gram
matrix of the polar form: as closed subgroup schemes of `GLₙ`, `O(q)` and
`ConstantForm.groupScheme R n C` are equal. -/
theorem groupScheme_eq_constantForm [Invertible (2 : R)] {C : Matrix (Fin n) (Fin n) R}
    (hC : C * polarMatrix q = 1) :
    groupScheme R n q = ConstantForm.groupScheme R n C := by
  rw [ConstantForm.groupScheme_def]
  change CommHopfAlgCat.quotientSpec _ (definingHopfIdeal R n q) = _
  rw [definingHopfIdeal_eq_constantForm q hC]

end TauCeti.QuadraticOrthogonal
