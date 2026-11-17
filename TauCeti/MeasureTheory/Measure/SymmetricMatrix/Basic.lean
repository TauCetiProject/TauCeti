/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.MeasureTheory.Measure.SelfAdjointMatrix
public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
public import Mathlib.Order.Sym2

/-!
# The carrier of symmetric-matrix distributions

The Wishart and related symmetric-matrix distributions live on Mathlib's
self-adjoint subspace `selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)`. Over `ℝ`, `star` is
transpose, so this is exactly the subspace of symmetric matrices, and
`Matrix.isHermitian_iff_isSelfAdjoint` connects membership to the spectral API.

`TauCeti.MeasureTheory.Measure.SelfAdjointMatrix` equips
`selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)` with the ambient Frobenius norm and real
inner product while keeping the subtype topology and uniformity definitionally equal to the induced
product ones, with Borel measurable structure and `volume` from `measureSpaceOfInnerProductSpace`.

This file specializes the entry and trace-pairing API to `ℝ` and fixes the upper-triangular
coordinate system used to normalize Lebesgue measure on the subspace:
`TauCeti.symmetricCoordinates` reads off the entries on or above the diagonal.

## Main declarations

* `TauCeti.upperTriangle` — the index type of upper-triangular positions.
* `TauCeti.card_upperTriangle` — there are `p * (p + 1) / 2` such positions.
* `TauCeti.symmetricCoordinates` — the continuous linear equivalence with `upperTriangle p → ℝ`.
* `TauCeti.symmetricCoordinatesMeasurableEquiv` — its measurable-equivalence form.
* `TauCeti.symmetricBasis` — the basis dual to the upper-triangular coordinates.
* `TauCeti.symmetricFinOneEquiv` — the identification of `1 × 1` symmetric matrices with `ℝ`.
* `TauCeti.finrank_symmetricMatrix` — the dimension is `p * (p + 1) / 2`.
* `selfAdjoint.inner_eq_trace_mul`, `selfAdjoint.norm_sq_eq_trace_sq` — the Frobenius pairing is
  the trace pairing and the squared norm is `tr(A ^ 2)`, with continuity lemmas
  `selfAdjoint.continuous_trace_mul_coe` and `selfAdjoint.continuous_exp_trace_mul_coe`.
* `TauCeti.symmetricEntry` — the symmetric matrix representing evaluation at an entry under the
  trace pairing, with `TauCeti.trace_symmetricEntry_mul` and
  `TauCeti.trace_symmetricEntry_mul_mul_symmetricEntry_mul`.
-/

public section

noncomputable section

open MeasureTheory Module

open scoped RealInnerProductSpace

namespace TauCeti

/-- The index type for the on-or-above-diagonal positions of a `p × p` matrix. A symmetric
matrix is determined by these entries, and `TauCeti.symmetricCoordinates` reads them off. -/
abbrev upperTriangle (p : ℕ) := {ij : Fin p × Fin p // ij.1 ≤ ij.2}

/-- There are `p * (p + 1) / 2` on-or-above-diagonal positions in a `p × p` matrix. -/
theorem card_upperTriangle (p : ℕ) : Fintype.card (upperTriangle p) = p * (p + 1) / 2 := by
  rw [← Fintype.card_congr (Sym2.sortEquiv (α := Fin p)), Sym2.card, Fintype.card_fin,
    Nat.choose_two_right, Nat.add_sub_cancel, mul_comm]

section instances
variable (p : ℕ)
instance symmetricMatrixNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixNormedAddCommGroup p ℝ
instance symmetricMatrixInnerProductSpace :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixInnerProductSpace p ℝ
instance symmetricMatrixIsUniformAddGroup :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixIsUniformAddGroup p ℝ
instance symmetricMatrixSecondCountableTopology :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixSecondCountableTopology p ℝ
instance symmetricMatrixCompleteSpace :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixCompleteSpace p ℝ
instance symmetricMatrixContinuousENorm :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixContinuousENorm p ℝ
instance symmetricMatrixBorelSpace :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  selfAdjointMatrixBorelSpace p ℝ
end instances

end TauCeti

/-! ### Symmetry of the entries -/

namespace selfAdjoint

/-- The entries of a symmetric matrix are unchanged by swapping the two indices. -/
theorem coe_apply_comm {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (i j : Fin p) :
    (A : Matrix (Fin p) (Fin p) ℝ) i j = (A : Matrix (Fin p) (Fin p) ℝ) j i := by
  simpa using (isHermitian_coe A).apply j i

open scoped Matrix in
/-- An element of the symmetric subspace is fixed by transposition. -/
@[simp]
theorem transpose_coe {p : ℕ} (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (A : Matrix (Fin p) (Fin p) ℝ)ᵀ = (A : Matrix (Fin p) (Fin p) ℝ) :=
  (Matrix.isHermitian_iff_isSymm.1 (isHermitian_coe A)).eq

end selfAdjoint

namespace TauCeti

/-! ### Upper-triangular coordinates -/

section coordinates

variable (p : ℕ)

/-- The continuous linear equivalence reading off the on-or-above-diagonal entries of a
symmetric matrix. Its inverse reconstructs the matrix by reflecting them across the diagonal.

This coordinate system fixes the normalization of `TauCeti.symmetricLebesgue`. -/
def symmetricCoordinates :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ≃L[ℝ] (upperTriangle p → ℝ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun A ij := (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2
      map_add' A B := rfl
      map_smul' c A := rfl
      invFun x :=
        ⟨Matrix.of fun i j =>
            if h : i ≤ j then x ⟨(i, j), h⟩ else x ⟨(j, i), le_of_not_ge h⟩, by
          refine Matrix.IsHermitian.ext fun i j => ?_
          simp only [Matrix.of_apply, star_trivial]
          rcases le_total i j with h | h
          · rcases h.lt_or_eq with hlt | rfl
            · rw [dite_eq_right (not_le.2 hlt), dite_eq_left h]
            · rfl
          · rcases h.lt_or_eq with hlt | rfl
            · rw [dite_eq_left h, dite_eq_right (not_le.2 hlt)]
            · rfl⟩
      left_inv A := by
        refine Subtype.ext ?_
        ext i j
        simp only [Matrix.of_apply]
        by_cases h : i ≤ j
        · exact dite_eq_left h
        · rw [dite_eq_right h]
          exact selfAdjoint.coe_apply_comm A j i
      right_inv x := by
        funext ij
        obtain ⟨⟨i, j⟩, hij⟩ := ij
        exact dite_eq_left hij }

@[simp]
theorem symmetricCoordinates_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (ij : upperTriangle p) :
    symmetricCoordinates p A ij = (A : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 :=
  (rfl)

@[simp]
theorem coe_symmetricCoordinates_symm_apply_of_le (x : upperTriangle p → ℝ) {i j : Fin p}
    (h : i ≤ j) :
    ((symmetricCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(i, j), h⟩ :=
  dite_eq_left h

@[simp]
theorem coe_symmetricCoordinates_symm_apply_of_ge (x : upperTriangle p → ℝ) {i j : Fin p}
    (h : j ≤ i) :
    ((symmetricCoordinates p).symm x : Matrix (Fin p) (Fin p) ℝ) i j = x ⟨(j, i), h⟩ := by
  by_cases h' : i ≤ j
  · obtain rfl : i = j := le_antisymm h' h
    exact dite_eq_left h'
  · exact dite_eq_right h'

/-- The measurable equivalence induced by `TauCeti.symmetricCoordinates`. -/
def symmetricCoordinatesMeasurableEquiv :
    (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) ≃ᵐ (upperTriangle p → ℝ) :=
  (symmetricCoordinates p).toHomeomorph.toMeasurableEquiv

@[simp]
theorem symmetricCoordinatesMeasurableEquiv_coe :
    (symmetricCoordinatesMeasurableEquiv p : _ → upperTriangle p → ℝ) =
      symmetricCoordinates p :=
  (rfl)

@[simp]
theorem symmetricCoordinatesMeasurableEquiv_symm_coe :
    ((symmetricCoordinatesMeasurableEquiv p).symm : (upperTriangle p → ℝ) → _) =
      (symmetricCoordinates p).symm :=
  (rfl)

/-- The symmetric subspace has dimension `p * (p + 1) / 2`. -/
theorem finrank_symmetricMatrix :
    Module.finrank ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) =
      p * (p + 1) / 2 := by
  rw [(symmetricCoordinates p).toLinearEquiv.finrank_eq, Module.finrank_fintype_fun_eq_card,
    card_upperTriangle]

/-- The basis of the symmetric subspace dual to the upper-triangular coordinates: its vector at
an on-or-above-diagonal position is the symmetric matrix carrying a one at that position and at
its mirror image, and nothing else. -/
def symmetricBasis :
    Basis (upperTriangle p) ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (Pi.basisFun ℝ (upperTriangle p)).map (symmetricCoordinates p).symm.toLinearEquiv

theorem symmetricBasis_apply (ij : upperTriangle p) :
    symmetricBasis p ij = (symmetricCoordinates p).symm (Pi.single ij 1) := by
  simp [symmetricBasis]

/-- The coordinates of a symmetric matrix in `TauCeti.symmetricBasis` are its
on-or-above-diagonal entries. -/
@[simp]
theorem symmetricBasis_repr (x : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ))
    (ij : upperTriangle p) :
    (symmetricBasis p).repr x ij = (x : Matrix (Fin p) (Fin p) ℝ) ij.1.1 ij.1.2 := by
  simp [symmetricBasis]

theorem coe_symmetricBasis_apply_of_le (ij : upperTriangle p) {k l : Fin p} (h : k ≤ l) :
    ((symmetricBasis p ij : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) k l = if ij = ⟨(k, l), h⟩ then 1 else 0 := by
  rw [symmetricBasis_apply, coe_symmetricCoordinates_symm_apply_of_le p _ h, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

theorem coe_symmetricBasis_apply_of_ge (ij : upperTriangle p) {k l : Fin p} (h : l ≤ k) :
    ((symmetricBasis p ij : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) k l = if ij = ⟨(l, k), h⟩ then 1 else 0 := by
  rw [symmetricBasis_apply, coe_symmetricCoordinates_symm_apply_of_ge p _ h, Pi.single_apply]
  exact if_congr eq_comm rfl rfl

/-- On the diagonal, the coordinate basis vector is a single matrix unit. -/
theorem coe_symmetricBasis_diag (i : Fin p) :
    ((symmetricBasis p ⟨(i, i), le_rfl⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ) = Matrix.single i i 1 := by
  ext k l
  rw [Matrix.single_apply]
  rcases le_total k l with h | h
  · rw [coe_symmetricBasis_apply_of_le _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff]
  · rw [coe_symmetricBasis_apply_of_ge _ _ h]
    simp [Subtype.ext_iff, Prod.ext_iff, and_comm]

/-- Off the diagonal, the coordinate basis vector is a symmetrized pair of matrix units. -/
theorem coe_symmetricBasis_offDiag {i j : Fin p} (hij : i ≤ j) (hne : i ≠ j) :
    ((symmetricBasis p ⟨(i, j), hij⟩ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
      Matrix (Fin p) (Fin p) ℝ) = Matrix.single i j 1 + Matrix.single j i 1 := by
  ext k l
  rw [Matrix.add_apply, Matrix.single_apply, Matrix.single_apply]
  rcases le_total k l with h | h
  · have h2 : ¬(j = k ∧ i = l) := by
      rintro ⟨rfl, rfl⟩
      exact hne (le_antisymm hij h)
    rw [coe_symmetricBasis_apply_of_le _ _ h, ite_eq_right h2, add_zero]
    simp [Subtype.ext_iff, Prod.ext_iff]
  · have h2 : ¬(i = k ∧ j = l) := by
      rintro ⟨rfl, rfl⟩
      exact hne (le_antisymm hij h)
    rw [coe_symmetricBasis_apply_of_ge _ _ h, ite_eq_right h2, zero_add]
    simp [Subtype.ext_iff, Prod.ext_iff, and_comm]

end coordinates

/-! ### The one-dimensional carrier -/

/-- In dimension one there is a single on-or-above-diagonal position. -/
instance uniqueUpperTriangleOne : Unique (upperTriangle 1) where
  default := ⟨(0, 0), le_rfl⟩
  uniq _ := Subtype.ext (Subsingleton.elim _ _)

/-- **A `1 × 1` symmetric matrix is its single entry.** This is the upper-triangular coordinate
system `TauCeti.symmetricCoordinates` in dimension one, with the single coordinate read as a real
number rather than as a function on a one-element index type. It is the identification under which
a one-dimensional symmetric-matrix law becomes a law on `ℝ`. -/
def symmetricFinOneEquiv : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ) ≃L[ℝ] ℝ :=
  (symmetricCoordinates 1).trans (ContinuousLinearEquiv.funUnique (upperTriangle 1) ℝ ℝ)

@[simp]
theorem symmetricFinOneEquiv_apply (A : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ)) :
    symmetricFinOneEquiv A = (A : Matrix (Fin 1) (Fin 1) ℝ) 0 0 := by
  have hdefault : (default : upperTriangle 1) = ⟨(0, 0), le_rfl⟩ := Subsingleton.elim _ _
  rw [symmetricFinOneEquiv, ContinuousLinearEquiv.trans_apply,
    ContinuousLinearEquiv.coe_funUnique, Function.eval, hdefault, symmetricCoordinates_apply]

@[simp]
theorem coe_symmetricFinOneEquiv_symm_apply (x : ℝ) (i j : Fin 1) :
    ((symmetricFinOneEquiv.symm x : selfAdjoint.submodule ℝ (Matrix (Fin 1) (Fin 1) ℝ)) :
        Matrix (Fin 1) (Fin 1) ℝ) i j = x := by
  obtain rfl : i = 0 := Subsingleton.elim _ _
  obtain rfl : j = 0 := Subsingleton.elim _ _
  rw [symmetricFinOneEquiv, ContinuousLinearEquiv.symm_trans_apply,
    ContinuousLinearEquiv.coe_funUnique_symm, coe_symmetricCoordinates_symm_apply_of_le 1 _ le_rfl,
    Function.const_apply]

end TauCeti

/-! ### The trace pairing -/

namespace selfAdjoint

/-- On the symmetric subspace, the Frobenius inner product is the trace pairing. This makes
`MeasureTheory.charFun` on the subspace use the same pairing as the Wishart trace statistics. -/
theorem inner_eq_trace_mul {p : ℕ}
    (A Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ⟪A, Θ⟫ = ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace :=
  inner_eq_rclike_re_trace_mul A Θ

/-- The squared Frobenius norm of an element of the real symmetric subspace is `tr(A ^ 2)`. -/
theorem norm_sq_eq_trace_sq {p : ℕ}
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    ‖A‖ ^ 2 = ((A : Matrix (Fin p) (Fin p) ℝ) ^ 2).trace :=
  norm_sq_eq_rclike_re_trace_sq A

/-- The trace pairing against a fixed symmetric matrix is continuous, being the Frobenius inner
product with that matrix. -/
theorem continuous_trace_mul_coe {p : ℕ}
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace := by
  simp only [← inner_eq_trace_mul]
  exact continuous_id.inner continuous_const

/-- Reading off an entry of a symmetric matrix is continuous. -/
theorem continuous_coe_apply {p : ℕ} (i j : Fin p) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ) i j :=
  continuous_subtype_val.matrix_elem i j

/-- Reading off an entry of a symmetric matrix is measurable. -/
@[fun_prop]
theorem measurable_coe_apply {p : ℕ} (i j : Fin p) :
    Measurable fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      (A : Matrix (Fin p) (Fin p) ℝ) i j :=
  (continuous_coe_apply i j).measurable

/-- The exponential of a scalar multiple of the trace pairing is continuous. This is the
measurability side condition of the exponential-moment computations on the symmetric
subspace. -/
theorem continuous_exp_trace_mul_coe {p : ℕ}
    (Θ : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) (t : ℝ) :
    Continuous fun A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) =>
      Real.exp (t * ((Θ : Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace) :=
  (continuous_const.mul (continuous_trace_mul_coe Θ)).rexp

end selfAdjoint

namespace TauCeti

/-! ### Representers of the matrix entries -/

section symmetricEntry

variable {p : ℕ}

/-- The symmetric matrix `(Eᵢⱼ + Eⱼᵢ) / 2`, which represents evaluation at the `(i, j)` entry
under the trace pairing: `trace (symmetricEntry i j * A) = A i j` for every symmetric `A`. -/
def symmetricEntry (i j : Fin p) : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨(1 / 2 : ℝ) • (Matrix.single i j 1 + Matrix.single j i 1),
    Matrix.isHermitian_iff_isSelfAdjoint.1 <| by
      rw [Matrix.isHermitian_iff_isSymm, Matrix.IsSymm.ext_iff]
      intro k l
      simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.single_apply, smul_eq_mul]
      split_ifs <;> simp_all [eq_comm] ⟩

theorem coe_symmetricEntry (i j : Fin p) :
    ((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) =
      (1 / 2 : ℝ) • (Matrix.single i j 1 + Matrix.single j i 1) :=
  (rfl)

/-- Pairing a Hermitian matrix with `TauCeti.symmetricEntry i j` under the trace reads off its
`(i, j)` entry. -/
theorem trace_symmetricEntry_mul (i j : Fin p) {A : Matrix (Fin p) (Fin p) ℝ}
    (hA : A.IsHermitian) :
    (((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * A).trace = A i j := by
  rw [coe_symmetricEntry, Matrix.smul_mul, Matrix.trace_smul, Matrix.add_mul, Matrix.trace_add,
    Matrix.trace_single_mul, Matrix.trace_single_mul]
  simp only [smul_eq_mul]
  have hsym : A j i = A i j := by simpa using hA.apply i j
  rw [hsym]
  ring

/-- The trace pairing of `TauCeti.symmetricEntry i j` with an element of the symmetric subspace is
its `(i, j)` entry. -/
@[simp]
theorem trace_symmetricEntry_mul_coe (i j : Fin p)
    (A : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * (A : Matrix (Fin p) (Fin p) ℝ)).trace =
      (A : Matrix (Fin p) (Fin p) ℝ) i j :=
  trace_symmetricEntry_mul i j (selfAdjoint.isHermitian_coe A)

/-- The bilinear map `(M, N) ↦ trace (M * S * N * S)` at two entry representers, for a Hermitian
`S`. -/
theorem trace_symmetricEntry_mul_mul_symmetricEntry_mul (i j k l : Fin p)
    {S : Matrix (Fin p) (Fin p) ℝ} (hS : S.IsHermitian) :
    (((symmetricEntry i j : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * S *
      ((symmetricEntry k l : selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
        Matrix (Fin p) (Fin p) ℝ) * S).trace =
      (S i k * S j l + S i l * S j k) / 2 := by
  rw [coe_symmetricEntry, coe_symmetricEntry]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.trace_smul, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, Matrix.single_mul_mul_single, Matrix.trace_single_mul]
  have hsym (a b : Fin p) : S a b = S b a := by simpa using hS.apply b a
  rw [hsym j k, hsym l i, hsym j l, hsym k i, hsym i l, hsym k j]
  ring

end symmetricEntry

end TauCeti
