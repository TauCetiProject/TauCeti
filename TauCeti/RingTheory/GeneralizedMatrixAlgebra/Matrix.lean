/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Unique
public import TauCeti.RingTheory.GeneralizedMatrixAlgebra.Basic
public import TauCeti.RingTheory.Idempotents.Matrix

/-!
# The matrix algebra as a generalized matrix algebra with scalar blocks

The matrix algebra `Mₙ(A)` over a commutative semiring `A` carries GMA data with one block of size
one for each index: the block idempotents are the diagonal matrix units `Eᵢᵢ`, and each corner
`A Eᵢᵢ` is identified with `M₁(A)` through its `(i, i)` entry. The trace of these GMA data is the
matrix trace, the entry module `A_{ij}` is the line `A Eᵢⱼ`, and the scalar pairing multiplies
coefficients: `φ(a Eᵢⱼ, b Eⱼᵢ) = ab`. This is the basic example of a generalized matrix algebra, in
which every entry module is free of rank one.

## Main definitions

* `Matrix.scalarGMAData`: the GMA data on `Mₙ(A)` with scalar blocks.

## Main results

* `Matrix.cornerEquiv_scalarGMAData_apply`: its corner isomorphisms read off the diagonal entry.
* `Matrix.trace_scalarGMAData`: its trace is the matrix trace.
* `Matrix.primitiveIdempotent_scalarGMAData`: its primitive idempotents are the `Eᵢᵢ`.
* `Matrix.mem_entry_scalarGMAData_iff`: its entry module `A_{ij}` consists of the multiples of
  `Eᵢⱼ`.
* `Matrix.pairing_scalarGMAData`: its scalar pairing is `φ(a Eᵢⱼ, b Eⱼᵢ) = ab`.

## References

* J. Bellaïche, G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), §1.3.
-/

public noncomputable section

namespace Matrix

variable (A n : Type*) [CommSemiring A] [Fintype n] [DecidableEq n]

/-- The identification of the corner of `Eᵢᵢ` in `Mₙ(A)` with `M₁(A)`, through the `(i, i)`
entry followed by Mathlib's `Matrix.uniqueRingEquiv`, upgraded to an `A`-algebra isomorphism. -/
private def scalarCornerEquiv (i : n) :
    (isIdempotentElem_single_one (α := A) i).Corner ≃ₐ[A] Matrix (Fin 1) (Fin 1) A :=
  (cornerSingleOneAlgEquiv A i).trans <| AlgEquiv.ofRingEquiv (f := uniqueRingEquiv.symm) fun a ↦ by
    ext k l
    simp only [Subsingleton.elim k l, algebraMap_matrix_apply, ↓reduceIte]
    -- `uniqueRingEquiv` multiplies matrices over `Fin 1` with the instances `Unique.fintype` and
    -- `decidableEq_of_subsingleton`, rather than `Fin.fintype 1` and `instDecidableEqFin 1`, so
    -- `rw` and `simp` cannot use `uniqueRingEquiv_symm_apply`; the two instance paths agree
    -- definitionally, and `exact` applies the lemma across them.
    exact (congrFun₂ (uniqueRingEquiv_symm_apply _) l l).trans (of_apply _ l l)

/-- `scalarCornerEquiv` sends an element of the corner of `Eᵢᵢ` to the `1 × 1` matrix of its
`(i, i)` entry. The last step is `uniqueRingEquiv_symm_apply`, applied across the two
definitionally equal instance paths on `Fin 1` explained in `scalarCornerEquiv`. -/
private theorem scalarCornerEquiv_apply (i : n)
    (x : (isIdempotentElem_single_one (α := A) i).Corner) :
    scalarCornerEquiv A n i x = of fun _ _ ↦ x.val i i := by
  rw [scalarCornerEquiv, AlgEquiv.trans_apply, cornerSingleOneAlgEquiv_apply]
  exact uniqueRingEquiv_symm_apply _

private theorem val_scalarCornerEquiv_symm_apply (i : n) (M : Matrix (Fin 1) (Fin 1) A) :
    ((scalarCornerEquiv A n i).symm M).val = single i i (M 0 0) := by
  have h : (scalarCornerEquiv A n i).symm M = (cornerSingleOneEquiv i).symm (M 0 0) := by
    rw [AlgEquiv.symm_apply_eq, scalarCornerEquiv_apply]
    ext k l
    rw [Subsingleton.elim k 0, Subsingleton.elim l 0, of_apply,
      val_cornerSingleOneEquiv_symm_apply, single_apply_same]
  rw [h, val_cornerSingleOneEquiv_symm_apply]

private theorem trace_scalarCornerEquiv_compress (i : n) (x : Matrix n n A) :
    (scalarCornerEquiv A n i ((isIdempotentElem_single_one i).compress x)).trace = x i i := by
  simp [scalarCornerEquiv_apply, trace_fin_one]

private theorem sum_trace_scalarCornerEquiv_compress (x : Matrix n n A) :
    ∑ i, (scalarCornerEquiv A n i ((isIdempotentElem_single_one i).compress x)).trace =
      x.trace := by
  simp_rw [trace_scalarCornerEquiv_compress, Matrix.trace, diag_apply]

/-- The **GMA data with scalar blocks** on the matrix algebra `Mₙ(A)`: one block of size one for
each index `i`, with block idempotent the diagonal matrix unit `Eᵢᵢ` and corner `A Eᵢᵢ ≃ M₁(A)`
given by the `(i, i)` entry. -/
def scalarGMAData : TauCeti.GMAData A (Matrix n n A) fun _ : n ↦ 1 where
  idempotent i := single i i 1
  completeOrthogonalIdempotents := completeOrthogonalIdempotents_single_one
  cornerEquiv := scalarCornerEquiv A n
  trace_mul_comm' x y := by
    rw [sum_trace_scalarCornerEquiv_compress, sum_trace_scalarCornerEquiv_compress,
      Matrix.trace_mul_comm]

variable {A n}

@[simp]
theorem idempotent_scalarGMAData (i : n) : (scalarGMAData A n).idempotent i = single i i 1 :=
  (rfl)

/-- The corner isomorphism `ψᵢ` of the scalar-block GMA data reads off the `(i, i)` entry. -/
@[simp]
theorem cornerEquiv_scalarGMAData_apply (i : n)
    (x : ((scalarGMAData A n).isIdempotentElem_idempotent i).Corner) :
    (scalarGMAData A n).cornerEquiv i x = of fun _ _ ↦ x.val i i :=
  scalarCornerEquiv_apply A n i x

/-- The inverse of the corner isomorphism `ψᵢ` of the scalar-block GMA data sends a `1 × 1` matrix
`(a)` to `a Eᵢᵢ`. -/
@[simp]
theorem val_cornerEquiv_scalarGMAData_symm_apply (i : n) (M : Matrix (Fin 1) (Fin 1) A) :
    (((scalarGMAData A n).cornerEquiv i).symm M).val = single i i (M 0 0) :=
  val_scalarCornerEquiv_symm_apply A n i M

/-- **The trace of the scalar-block GMA data is the matrix trace.** -/
@[simp]
theorem trace_scalarGMAData (x : Matrix n n A) : (scalarGMAData A n).trace x = x.trace := by
  rw [TauCeti.GMAData.trace_apply]
  exact sum_trace_scalarCornerEquiv_compress A n x

@[simp]
theorem matrixUnit_scalarGMAData (i : n) (k l : Fin 1) :
    (scalarGMAData A n).matrixUnit i k l = single i i 1 := by
  have h : single k l (1 : A) = 1 := by
    ext a b
    fin_cases k; fin_cases l; fin_cases a; fin_cases b
    simp
  rw [TauCeti.GMAData.matrixUnit_def, h, map_one, IsIdempotentElem.Corner.val_one,
    idempotent_scalarGMAData]

/-- The primitive idempotents of the scalar-block GMA data are the diagonal matrix units. -/
@[simp]
theorem primitiveIdempotent_scalarGMAData (i : n) :
    (scalarGMAData A n).primitiveIdempotent i = single i i 1 := by
  rw [TauCeti.GMAData.primitiveIdempotent_def, matrixUnit_scalarGMAData]

/-- **The entry modules of the scalar-block GMA data are the lines `A Eᵢⱼ`**: a matrix lies in
`A_{ij}` exactly when it is supported on the entry `(i, j)`. -/
theorem mem_entry_scalarGMAData_iff {i j : n} {x : Matrix n n A} :
    x ∈ (scalarGMAData A n).entry i j ↔ single i j (x i j) = x := by
  rw [TauCeti.GMAData.mem_entry_iff, primitiveIdempotent_scalarGMAData,
    primitiveIdempotent_scalarGMAData, single_mul_mul_single, one_mul, mul_one]

theorem single_mem_entry_scalarGMAData (i j : n) (a : A) :
    single i j a ∈ (scalarGMAData A n).entry i j := by
  rw [mem_entry_scalarGMAData_iff, single_apply_same]

/-- **The scalar pairing of the scalar-block GMA data multiplies coefficients**:
`φ(a Eᵢⱼ, b Eⱼᵢ) = ab`. -/
theorem pairing_scalarGMAData (i j : n) (a b : A) :
    (scalarGMAData A n).pairing i j ⟨single i j a, single_mem_entry_scalarGMAData i j a⟩
      ⟨single j i b, single_mem_entry_scalarGMAData j i b⟩ = a * b := by
  rw [TauCeti.GMAData.pairing_apply, trace_scalarGMAData, single_mul_single_same,
    trace_single_eq_same]

end Matrix
