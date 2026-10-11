/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Level
public import TauCeti.LinearAlgebra.IntegralLattice.Signature
public import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates

/-!
# The standard unit integral lattice

For a finite index type `ι`, the lattice `unitLattice ι` is the standard lattice
`I_ι = ℤ^ι` in `ℚ^ι`, with the dot-product form.  Its Gram matrix in the standard basis
is the identity matrix.  Consequently it is positive definite, unimodular, and has determinant
and discriminant one.  It is odd whenever `ι` is nonempty, and its signature is
`(#ι, 0, 0)`.

The lattices `I_n` are the basic odd unimodular lattices: they serve as the standard comparison
objects in integral-lattice calculations, for instance as the odd positive definite unimodular
lattices against which even lattices such as `E_8` are contrasted.

The empty-index case is retained: `I_∅` is the rank-zero even unimodular lattice.  This is why
the parity and level results below separate empty and nonempty index types.

## Main declarations

* `TauCeti.IntegralLattice.unitLattice`: the standard lattice `ℤ^ι` with identity Gram matrix.
* `TauCeti.IntegralLattice.unitLatticeBasis`: its standard integral basis.
* `TauCeti.IntegralLattice.unitLattice_signature`: its signature is `(#ι, 0, 0)`.
* `TauCeti.IntegralLattice.isUnimodular_unitLattice`: `I_ι` is unimodular.
* `TauCeti.IntegralLattice.isEven_unitLattice_iff`: `I_ι` is even exactly in rank zero.
* `TauCeti.IntegralLattice.level_unitLattice`: a nonzero-rank `I_ι` has level two.

## References

* W. Ebeling, *Lattices and Codes*, Chapter 1.
-/

public section

namespace TauCeti

namespace IntegralLattice

open Module

universe u

variable (ι : Type u)

variable [Fintype ι]

open Classical in
/-- The standard unit lattice `I_ι`: the integer coordinate lattice `ℤ^ι` inside `ℚ^ι`,
with the dot-product form and identity Gram matrix. -/
noncomputable def unitLattice : IntegralLattice (ι → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ ι) 1 Matrix.isSymm_one

/-- A vector belongs to the standard unit lattice exactly when all its coordinates are integers. -/
@[simp]
theorem mem_unitLattice_carrier_iff (x : ι → ℚ) :
    x ∈ (unitLattice ι).carrier ↔ ∀ i, ∃ z : ℤ, (z : ℚ) = x i := by
  classical
  simpa only [unitLattice] using mem_ofGramMatrix_basisFun_carrier_iff 1 Matrix.isSymm_one x

/-- The form of the standard unit lattice is the ordinary dot product. -/
@[simp]
theorem unitLattice_form_apply (x y : ι → ℚ) :
    (unitLattice ι).form x y = ∑ i, x i * y i := by
  classical
  rw [unitLattice, form_ofGramMatrix_basisFun_apply]
  simp [Matrix.one_apply]

/-- The norm of a vector in the standard unit lattice is the sum of its coordinate squares. -/
@[simp]
theorem unitLattice_norm_apply (x : ι → ℚ) :
    (unitLattice ι).norm x = ∑ i, x i ^ 2 := by
  rw [norm_apply, unitLattice_form_apply]
  congr 1
  funext i
  ring

open Classical in
/-- The coordinate vectors form the standard integral basis of `I_ι`. -/
noncomputable def unitLatticeBasis : Basis ι ℤ (unitLattice ι) :=
  ofGramMatrix.basis (Pi.basisFun ℚ ι) 1 Matrix.isSymm_one

/-- The standard integral basis vector has the corresponding unit coordinate vector in `ℚ^ι`. -/
@[simp]
theorem coe_unitLatticeBasis_apply (i : ι) :
    (unitLatticeBasis ι i : ι → ℚ) = Pi.basisFun ℚ ι i :=
  ofGramMatrix.coe_basis _ _ _ i

/-- The Gram matrix of the standard integral basis is the identity matrix. -/
@[simp]
theorem gramMatrix_unitLatticeBasis [DecidableEq ι] :
    (unitLattice ι).gramMatrix (unitLatticeBasis ι) = 1 := by
  unfold unitLattice unitLatticeBasis
  convert gramMatrix_ofGramMatrix (Pi.basisFun ℚ ι) 1 Matrix.isSymm_one

/-- The rank of `I_ι` is the cardinality of its index type. -/
@[simp]
theorem finrank_unitLattice : Module.finrank ℤ (unitLattice ι) = Fintype.card ι := by
  rw [(unitLattice ι).finrank_carrier]
  simp

/-- The signed determinant of the standard unit lattice is one. -/
@[simp]
theorem unitLattice_determinant : (unitLattice ι).determinant = 1 := by
  classical
  rw [unitLattice, determinant_ofGramMatrix]
  simp

/-- The discriminant of the standard unit lattice is one. -/
@[simp]
theorem unitLattice_discriminant : (unitLattice ι).discriminant = 1 := by
  rw [discriminant_def, unitLattice_determinant]
  norm_num

/-- The standard unit lattice is nondegenerate. -/
instance instIsNondegenerateUnitLattice : (unitLattice ι).IsNondegenerate :=
  ⟨(unitLattice ι).determinant_ne_zero_iff.mp (by simp)⟩

/-- The standard unit lattice is positive definite. -/
theorem isPosDef_unitLattice : (unitLattice ι).IsPosDef := by
  classical
  rw [unitLattice, isPosDef_ofGramMatrix_iff]
  rw [Matrix.map_one Int.cast Int.cast_zero Int.cast_one]
  exact Matrix.PosDef.one

/-- The standard unit lattice has signature `(#ι, 0, 0)`. -/
@[simp]
theorem unitLattice_signature :
    (unitLattice ι).signature = (Fintype.card ι, 0, 0) := by
  have hvanish := (unitLattice ι).isPosDef_iff_sigNull_eq_zero_and_sigNeg_eq_zero.mp
    (isPosDef_unitLattice ι)
  have hsum := (unitLattice ι).signature_sum_eq_finrank
  simp at hsum
  simp only [signature, Prod.mk.injEq]
  omega

/-- The standard unit lattice is unimodular. -/
theorem isUnimodular_unitLattice : (unitLattice ι).IsUnimodular := by
  rw [(unitLattice ι).isUnimodular_iff_discriminant_eq_one]
  exact unitLattice_discriminant ι

/-- The standard unit lattice is even exactly when it has rank zero. -/
@[simp]
theorem isEven_unitLattice_iff :
    (unitLattice ι).IsEven ↔ Fintype.card ι = 0 := by
  classical
  rw [unitLattice, isEven_ofGramMatrix_iff]
  constructor
  · intro h
    apply Fintype.card_eq_zero_iff.mpr
    exact ⟨fun i ↦ by
      obtain ⟨k, hk⟩ := h i
      have : (1 : ℤ) = k + k := by
        simpa only [Matrix.one_apply_eq] using hk
      omega⟩
  · intro h i
    exact (Fintype.card_eq_zero_iff.mp h).false i |>.elim

/-- A positive-rank standard unit lattice is odd. -/
theorem not_isEven_unitLattice [Nonempty ι] : ¬ (unitLattice ι).IsEven := by
  rw [isEven_unitLattice_iff]
  exact Fintype.card_ne_zero

/-- The rank-zero standard unit lattice has level one. -/
@[simp]
theorem level_unitLattice_of_isEmpty [IsEmpty ι] : (unitLattice ι).level = 1 := by
  rw [(unitLattice ι).level_eq_one_iff]
  exact ⟨(isEven_unitLattice_iff ι).mpr (Fintype.card_eq_zero_iff.mpr inferInstance),
    isUnimodular_unitLattice ι⟩

/-- A positive-rank standard unit lattice has level two. -/
@[simp]
theorem level_unitLattice [Nonempty ι] : (unitLattice ι).level = 2 := by
  rw [(isUnimodular_unitLattice ι).level_eq_two_iff]
  exact not_isEven_unitLattice ι

end IntegralLattice

end TauCeti
