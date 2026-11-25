/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.RingTheory.Idempotents.Corner.Basic
import Mathlib.Data.Matrix.Basis

/-!
# Generalized matrix algebras

Let `A` be a commutative semiring and `R` an `A`-algebra. Following Bellaïche–Chenevier, *GMA data*
of block sizes `d = (dᵢ)ᵢ` on `R` consist of a complete family of orthogonal idempotents `eᵢ ∈ R`,
`A`-algebra isomorphisms `ψᵢ : eᵢ R eᵢ ≃ M_{dᵢ}(A)` of the diagonal corners with matrix algebras,
and the requirement that the resulting trace `T(x) = ∑ᵢ tr ψᵢ(eᵢ x eᵢ)` be central:
`T(xy) = T(yx)`. An `A`-algebra with GMA data is a *generalized matrix algebra* (GMA).

Generalized matrix algebras are the integral substitute for matrix algebras in the theory of
pseudocharacters: the Cayley–Hamilton quotient of a group algebra by a residually multiplicity-free
determinant is a GMA, although in general not a matrix algebra over `A`. The off-diagonal entries
of a GMA live in `A`-modules `A_{ij}`, which need not be free, and the products `A_{ij} A_{ji} ⊆ A`
measure how far the representation is from being reducible.

The matrix units `E_i^{kl} = ψᵢ⁻¹(E_{kl})` of the diagonal blocks are `E.matrixUnit i k l`. When
every block is nonempty, the primitive idempotent of block `i` is `Eᵢ = E_i^{00}` and the *entry
module* is `A_{ij} = Eᵢ R Eⱼ`. Multiplication in `R` restricts to bilinear maps
`A_{ij} × A_{jk} → A_{ik}`; on `A_{ii} = A Eᵢ` it lands in the scalars, and the resulting scalar
pairing `A_{ij} × A_{ji} → A`, which is `(x, y) ↦ T(xy)`, is symmetric because `T` is central.

The decomposition of `R` into the blocks `eᵢ R eⱼ` is the two-sided Peirce decomposition
`CompleteOrthogonalIdempotents.isInternal_cornerSubmodule`. The primitive matrix units identify
each block `eᵢ R eⱼ` with the `dᵢ × dⱼ` matrices with entries in `A_{ij}`, and under this
identification multiplication of blocks is matrix multiplication.

## Main definitions

* `TauCeti.GMAData A R d`: GMA data of block sizes `d` on the `A`-algebra `R`.
* `TauCeti.GMAData.trace`: the trace `T(x) = ∑ᵢ tr ψᵢ(eᵢ x eᵢ)`.
* `TauCeti.GMAData.matrixUnit`: the matrix units `E_i^{kl}` of the diagonal blocks.
* `TauCeti.GMAData.primitiveIdempotent`: the primitive idempotent `Eᵢ = E_i^{00}` of a block.
* `TauCeti.GMAData.entry`: the entry module `A_{ij} = Eᵢ R Eⱼ`.
* `TauCeti.GMAData.entrySelfEquiv`: the identification `A ≃ A_{ii}`, `a ↦ a Eᵢ`.
* `TauCeti.GMAData.entryMul`: the multiplication `A_{ij} × A_{jk} → A_{ik}`.
* `TauCeti.GMAData.pairing`: the scalar pairing `A_{ij} × A_{ji} → A`.
* `TauCeti.GMAData.blockEquiv`: the identification of the block `eᵢ R eⱼ` with the matrices
  `M_{dᵢ × dⱼ}(A_{ij})`.

## Main results

* `TauCeti.GMAData.trace_mul_comm`: the trace is central.
* `TauCeti.GMAData.trace_one`: the trace of `1` is the total size `∑ᵢ dᵢ`.
* `TauCeti.GMAData.matrixUnit_mul_mul_matrixUnit`: `E_i^{ak} x E_i^{lb}` is the `(k, l)` entry
  of `ψᵢ(eᵢ x eᵢ)` times `E_i^{ab}`.
* `TauCeti.GMAData.trace_smul_primitiveIdempotent`: every element `x` of `A_{ii}` is `T(x) Eᵢ`.
* `TauCeti.GMAData.entryMul_assoc`: the multiplication maps of the entry modules are associative.
* `TauCeti.GMAData.pairing_comm`: the scalar pairing is symmetric, `φ(x, y) = φ(y, x)`.
* `TauCeti.GMAData.pairing_smul_primitiveIdempotent`: `xy = φ(x, y) Eᵢ` for `x ∈ A_{ij}` and
  `y ∈ A_{ji}`.
* `TauCeti.GMAData.coe_blockEquiv_mul_apply`: under `blockEquiv`, multiplication of blocks is
  matrix multiplication with entries multiplied in `R`.

## References

* J. Bellaïche, G. Chenevier, *Families of Galois representations and Selmer groups*,
  Astérisque 324 (2009), §1.3: Definition 1.3.1, §1.3.2 and Lemma 1.3.5.
-/

public section

open Matrix

namespace TauCeti

variable (A R : Type*) [CommSemiring A] [Semiring R] [Algebra A R] {ι : Type*} [Fintype ι]

/-- **GMA data** of block sizes `d = (dᵢ)ᵢ` on an `A`-algebra `R` (Bellaïche–Chenevier,
Definition 1.3.1): a complete family of orthogonal idempotents `eᵢ`, `A`-algebra isomorphisms
`ψᵢ : eᵢ R eᵢ ≃ M_{dᵢ}(A)` of the diagonal corners with matrix algebras, such that the trace
`T(x) = ∑ᵢ tr ψᵢ(eᵢ x eᵢ)` is central. The trace is `TauCeti.GMAData.trace`. -/
structure GMAData (d : ι → ℕ) where
  /-- The block idempotents `eᵢ`. -/
  idempotent : ι → R
  /-- The block idempotents form a complete family of orthogonal idempotents. -/
  completeOrthogonalIdempotents : CompleteOrthogonalIdempotents idempotent
  /-- The identification `ψᵢ` of the diagonal corner `eᵢ R eᵢ` with the matrix algebra
  `M_{dᵢ}(A)`. -/
  cornerEquiv (i : ι) :
    (completeOrthogonalIdempotents.idem i).Corner ≃ₐ[A] Matrix (Fin (d i)) (Fin (d i)) A
  /-- The trace `x ↦ ∑ᵢ tr ψᵢ(eᵢ x eᵢ)` is central. Use `TauCeti.GMAData.trace_mul_comm`. -/
  trace_mul_comm' (x y : R) :
    ∑ i, (cornerEquiv i ((completeOrthogonalIdempotents.idem i).compress (x * y))).trace =
      ∑ i, (cornerEquiv i ((completeOrthogonalIdempotents.idem i).compress (y * x))).trace

namespace GMAData

variable {A R} {d : ι → ℕ} (E : GMAData A R d)

/-- The block idempotents are idempotent. -/
theorem isIdempotentElem_idempotent (i : ι) : IsIdempotentElem (E.idempotent i) :=
  E.completeOrthogonalIdempotents.idem i

/-- Distinct block idempotents are orthogonal. -/
theorem idempotent_mul_idempotent_of_ne {i j : ι} (h : i ≠ j) :
    E.idempotent i * E.idempotent j = 0 :=
  E.completeOrthogonalIdempotents.ortho h

/-! ### The trace -/

/-- The **trace** of a generalized matrix algebra, `T(x) = ∑ᵢ tr ψᵢ(eᵢ x eᵢ)`. -/
def trace : R →ₗ[A] A where
  toFun x := ∑ i, (E.cornerEquiv i ((E.isIdempotentElem_idempotent i).compress x)).trace
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.mul_sum]

theorem trace_apply (x : R) :
    E.trace x = ∑ i, (E.cornerEquiv i ((E.isIdempotentElem_idempotent i).compress x)).trace :=
  (rfl)

/-- **The trace of a generalized matrix algebra is central.** -/
theorem trace_mul_comm (x y : R) : E.trace (x * y) = E.trace (y * x) :=
  E.trace_mul_comm' x y

/-- On the diagonal corner `eᵢ R eᵢ`, the trace is the matrix trace transported along `ψᵢ`. -/
theorem trace_val (i : ι) (b : (E.isIdempotentElem_idempotent i).Corner) :
    E.trace b.val = (E.cornerEquiv i b).trace := by
  rw [trace_apply, Finset.sum_eq_single i]
  · rw [IsIdempotentElem.compress_val]
  · intro j _ hji
    have h : (E.isIdempotentElem_idempotent j).compress b.val = 0 := Subtype.ext <| by
      rw [IsIdempotentElem.val_compress, ← (E.isIdempotentElem_idempotent i).mul_corner_val b,
        ← mul_assoc, E.idempotent_mul_idempotent_of_ne hji, zero_mul, zero_mul,
        IsIdempotentElem.Corner.val_zero]
    rw [h, map_zero, Matrix.trace_zero]
  · simp

/-- **The trace of `1` is the total size** `∑ᵢ dᵢ` of the blocks. -/
@[simp]
theorem trace_one : E.trace 1 = ∑ i, (d i : A) := by
  simp [trace_apply, IsIdempotentElem.compress_one, Matrix.trace_one]

/-! ### Matrix units -/

/-- The **matrix unit** `E_i^{kl} = ψᵢ⁻¹(E_{kl})` of the diagonal block `eᵢ R eᵢ`, as an element
of `R`. -/
def matrixUnit (i : ι) (k l : Fin (d i)) : R :=
  ((E.cornerEquiv i).symm (single k l 1)).val

theorem matrixUnit_def (i : ι) (k l : Fin (d i)) :
    E.matrixUnit i k l = ((E.cornerEquiv i).symm (single k l 1)).val :=
  (rfl)

/-- The `A`-linear inclusion `M_{dᵢ}(A) ≃ eᵢ R eᵢ ⊆ R` of a diagonal block. -/
private def blockInclusion (i : ι) : Matrix (Fin (d i)) (Fin (d i)) A →ₗ[A] R :=
  (TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent i)).subtype ∘ₗ
    ((E.isIdempotentElem_idempotent i).cornerLinearEquivCornerSubmodule (R := A)).toLinearMap ∘ₗ
      (E.cornerEquiv i).symm.toLinearMap

private theorem blockInclusion_apply (i : ι) (m : Matrix (Fin (d i)) (Fin (d i)) A) :
    E.blockInclusion i m = ((E.cornerEquiv i).symm m).val := by
  simp [blockInclusion]

/-- The preimage under `ψᵢ` of the single-entry matrix `c E_{kl}` is `c E_i^{kl}`. -/
theorem val_cornerEquiv_symm_single (i : ι) (k l : Fin (d i)) (c : A) :
    ((E.cornerEquiv i).symm (single k l c)).val = c • E.matrixUnit i k l := by
  rw [show single k l c = c • single k l (1 : A) by rw [smul_single, smul_eq_mul, mul_one],
    map_smul, IsIdempotentElem.Corner.val_smul, matrixUnit]

/-- An element of the diagonal block `eᵢ R eᵢ` expands in the matrix units:
`ψᵢ⁻¹(m) = ∑_{k,l} m_{kl} E_i^{kl}`. -/
theorem val_cornerEquiv_symm_apply (i : ι) (m : Matrix (Fin (d i)) (Fin (d i)) A) :
    ((E.cornerEquiv i).symm m).val = ∑ k, ∑ l, m k l • E.matrixUnit i k l := by
  rw [← blockInclusion_apply]
  conv_lhs => rw [Matrix.matrix_eq_sum_single m]
  simp_rw [map_sum]
  exact Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ by
    rw [blockInclusion_apply, val_cornerEquiv_symm_single]

@[simp]
theorem idempotent_mul_matrixUnit (i : ι) (k l : Fin (d i)) :
    E.idempotent i * E.matrixUnit i k l = E.matrixUnit i k l :=
  (E.isIdempotentElem_idempotent i).mul_corner_val _

@[simp]
theorem matrixUnit_mul_idempotent (i : ι) (k l : Fin (d i)) :
    E.matrixUnit i k l * E.idempotent i = E.matrixUnit i k l :=
  (E.isIdempotentElem_idempotent i).corner_val_mul _

theorem idempotent_mul_matrixUnit_of_ne {i j : ι} (h : j ≠ i) (k l : Fin (d i)) :
    E.idempotent j * E.matrixUnit i k l = 0 := by
  rw [← E.idempotent_mul_matrixUnit, ← mul_assoc, E.idempotent_mul_idempotent_of_ne h, zero_mul]

theorem matrixUnit_mul_idempotent_of_ne {i j : ι} (h : i ≠ j) (k l : Fin (d i)) :
    E.matrixUnit i k l * E.idempotent j = 0 := by
  rw [← E.matrixUnit_mul_idempotent, mul_assoc, E.idempotent_mul_idempotent_of_ne h, mul_zero]

/-- **Multiplication of matrix units** within one block: `E_i^{kl} E_i^{l'm}` is `E_i^{km}` if
`l = l'` and `0` otherwise. -/
theorem matrixUnit_mul_matrixUnit (i : ι) (k l l' m : Fin (d i)) :
    E.matrixUnit i k l * E.matrixUnit i l' m = if l = l' then E.matrixUnit i k m else 0 := by
  rw [matrixUnit, matrixUnit, ← IsIdempotentElem.Corner.val_mul, ← map_mul]
  split_ifs with h
  · rw [h, single_mul_single_same, one_mul, matrixUnit]
  · rw [single_mul_single_of_ne _ _ _ _ h, map_zero, IsIdempotentElem.Corner.val_zero]

@[simp]
theorem matrixUnit_mul_matrixUnit_same (i : ι) (k l m : Fin (d i)) :
    E.matrixUnit i k l * E.matrixUnit i l m = E.matrixUnit i k m := by
  simp [matrixUnit_mul_matrixUnit]

/-- Matrix units of different blocks are orthogonal. -/
theorem matrixUnit_mul_matrixUnit_of_ne {i j : ι} (h : i ≠ j) (k l : Fin (d i))
    (k' l' : Fin (d j)) : E.matrixUnit i k l * E.matrixUnit j k' l' = 0 := by
  rw [← E.matrixUnit_mul_idempotent i, mul_assoc, E.idempotent_mul_matrixUnit_of_ne h, mul_zero]

/-- The diagonal matrix units of a block add up to its block idempotent. -/
theorem sum_matrixUnit_self (i : ι) : ∑ k, E.matrixUnit i k k = E.idempotent i := by
  have h := E.val_cornerEquiv_symm_apply i 1
  rw [map_one, IsIdempotentElem.Corner.val_one] at h
  rw [h]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [Finset.sum_eq_single k (fun l _ hlk ↦ by rw [one_apply_ne' hlk, zero_smul]) (by simp),
    one_apply_eq, one_smul]

/-- **Matrix coefficients.** Cutting `x` down by matrix units of the block `i` on both sides
gives the `(k, l)` entry of the matrix `ψᵢ(eᵢ x eᵢ)`:
`E_i^{ak} x E_i^{lb} = ψᵢ(eᵢ x eᵢ)_{kl} E_i^{ab}`. -/
theorem matrixUnit_mul_mul_matrixUnit (i : ι) (a k l b : Fin (d i)) (x : R) :
    E.matrixUnit i a k * x * E.matrixUnit i l b =
      E.cornerEquiv i ((E.isIdempotentElem_idempotent i).compress x) k l • E.matrixUnit i a b := by
  have h : E.matrixUnit i a k * x * E.matrixUnit i l b =
      ((E.cornerEquiv i).symm (single a k 1) * (E.isIdempotentElem_idempotent i).compress x *
        (E.cornerEquiv i).symm (single l b 1)).val := by
    rw [IsIdempotentElem.Corner.val_mul, IsIdempotentElem.Corner.val_mul,
      IsIdempotentElem.val_compress, ← matrixUnit, ← matrixUnit]
    simp only [← mul_assoc, matrixUnit_mul_idempotent]
    simp only [mul_assoc, idempotent_mul_matrixUnit]
  rw [h]
  conv_lhs => rw [← (E.cornerEquiv i).symm_apply_apply
    ((E.isIdempotentElem_idempotent i).compress x), ← map_mul, ← map_mul, single_mul_mul_single,
    one_mul, mul_one, val_cornerEquiv_symm_single]

/-- The trace of a matrix unit is `1` on the diagonal and `0` off it. -/
@[simp]
theorem trace_matrixUnit (i : ι) (k l : Fin (d i)) :
    E.trace (E.matrixUnit i k l) = if k = l then 1 else 0 := by
  rw [matrixUnit, trace_val, AlgEquiv.apply_symm_apply]
  split_ifs with h
  · rw [h, trace_single_eq_same]
  · exact trace_single_eq_of_ne _ _ _ h

/-! ### Primitive idempotents and entry modules -/

variable [∀ i, NeZero (d i)]

/-- The **primitive idempotent** `Eᵢ = E_i^{00}` of the block `i`. -/
def primitiveIdempotent (i : ι) : R :=
  E.matrixUnit i 0 0

theorem primitiveIdempotent_def (i : ι) : E.primitiveIdempotent i = E.matrixUnit i 0 0 :=
  (rfl)

theorem isIdempotentElem_primitiveIdempotent (i : ι) :
    IsIdempotentElem (E.primitiveIdempotent i) :=
  E.matrixUnit_mul_matrixUnit_same i 0 0 0

@[simp]
theorem trace_primitiveIdempotent (i : ι) : E.trace (E.primitiveIdempotent i) = 1 := by
  simp [primitiveIdempotent, trace_matrixUnit]

/-- The **entry module** `A_{ij} = Eᵢ R Eⱼ` of a generalized matrix algebra, cut out by the
primitive idempotents of the blocks `i` and `j`. -/
def entry (i j : ι) : Submodule A R :=
  TauCeti.cornerSubmodule A (E.primitiveIdempotent i) (E.primitiveIdempotent j)

theorem entry_def (i j : ι) :
    E.entry i j = TauCeti.cornerSubmodule A (E.primitiveIdempotent i) (E.primitiveIdempotent j) :=
  (rfl)

@[simp]
theorem mem_entry_iff {i j : ι} {x : R} :
    x ∈ E.entry i j ↔ E.primitiveIdempotent i * x * E.primitiveIdempotent j = x :=
  TauCeti.mem_cornerSubmodule_iff A (E.isIdempotentElem_primitiveIdempotent i)
    (E.isIdempotentElem_primitiveIdempotent j)

/-- Cutting an element down by `Eᵢ` and `Eⱼ` lands in the entry module `A_{ij}`. -/
theorem primitiveIdempotent_mul_mul_mem_entry (i j : ι) (x : R) :
    E.primitiveIdempotent i * x * E.primitiveIdempotent j ∈ E.entry i j :=
  TauCeti.mul_mul_mem_cornerSubmodule A _ _ x

theorem primitiveIdempotent_mem_entry (i : ι) : E.primitiveIdempotent i ∈ E.entry i i := by
  rw [mem_entry_iff, (E.isIdempotentElem_primitiveIdempotent i).eq,
    (E.isIdempotentElem_primitiveIdempotent i).eq]

theorem primitiveIdempotent_mul_of_mem_entry {i j : ι} {x : R} (hx : x ∈ E.entry i j) :
    E.primitiveIdempotent i * x = x :=
  TauCeti.mul_eq_self_of_mem_cornerSubmodule (E.isIdempotentElem_primitiveIdempotent i) hx

theorem mul_primitiveIdempotent_of_mem_entry {i j : ι} {x : R} (hx : x ∈ E.entry i j) :
    x * E.primitiveIdempotent j = x :=
  TauCeti.mul_eq_self_of_mem_cornerSubmodule_right (E.isIdempotentElem_primitiveIdempotent j) hx

/-- The entry modules are closed under multiplication: `A_{ij} A_{jk} ⊆ A_{ik}`. -/
theorem mul_mem_entry {i j k : ι} {x y : R} (hx : x ∈ E.entry i j) (hy : y ∈ E.entry j k) :
    x * y ∈ E.entry i k :=
  TauCeti.mul_mem_cornerSubmodule hx hy

/-- Cutting `x` down by the matrix units `E_i^{0k}` and `E_j^{l0}` lands in `A_{ij}`. -/
theorem matrixUnit_mul_mul_matrixUnit_mem_entry {i j : ι} (k : Fin (d i)) (l : Fin (d j))
    (x : R) : E.matrixUnit i 0 k * x * E.matrixUnit j l 0 ∈ E.entry i j := by
  rw [mem_entry_iff, primitiveIdempotent, primitiveIdempotent, ← mul_assoc, ← mul_assoc,
    matrixUnit_mul_matrixUnit_same, mul_assoc, matrixUnit_mul_matrixUnit_same]

/-- **The diagonal entry modules are the scalars**: every `x ∈ A_{ii}` is `T(x) Eᵢ`. -/
theorem trace_smul_primitiveIdempotent {i : ι} {x : R} (hx : x ∈ E.entry i i) :
    E.trace x • E.primitiveIdempotent i = x := by
  have h := E.matrixUnit_mul_mul_matrixUnit i 0 0 0 0 x
  rw [← primitiveIdempotent, E.mem_entry_iff.1 hx] at h
  rw [h, map_smul, trace_primitiveIdempotent, smul_eq_mul, mul_one]

/-- The identification `A ≃ A_{ii}`, `a ↦ a Eᵢ`, with inverse the trace. -/
def entrySelfEquiv (i : ι) : A ≃ₗ[A] E.entry i i where
  toFun a := ⟨a • E.primitiveIdempotent i,
    Submodule.smul_mem _ a (E.primitiveIdempotent_mem_entry i)⟩
  invFun x := E.trace x
  map_add' a b := Subtype.ext (add_smul a b _)
  map_smul' a b := Subtype.ext (mul_smul a b _)
  left_inv a := by simp
  right_inv x := Subtype.ext (E.trace_smul_primitiveIdempotent x.property)

@[simp]
theorem coe_entrySelfEquiv_apply (i : ι) (a : A) :
    (E.entrySelfEquiv i a : R) = a • E.primitiveIdempotent i :=
  (rfl)

@[simp]
theorem entrySelfEquiv_symm_apply (i : ι) (x : E.entry i i) :
    (E.entrySelfEquiv i).symm x = E.trace x :=
  (rfl)

/-! ### The multiplication of entry modules and the scalar pairing -/

/-- The **multiplication of entry modules** `A_{ij} × A_{jk} → A_{ik}`, the restriction of the
multiplication of `R`. -/
def entryMul (i j k : ι) : E.entry i j →ₗ[A] E.entry j k →ₗ[A] E.entry i k :=
  LinearMap.mk₂ A (fun x y ↦ ⟨x * y, E.mul_mem_entry x.property y.property⟩)
    (fun x x' y ↦ Subtype.ext (add_mul (x : R) x' y))
    (fun a x y ↦ Subtype.ext (smul_mul_assoc a (x : R) y))
    (fun x y y' ↦ Subtype.ext (mul_add (x : R) y y'))
    (fun a x y ↦ Subtype.ext (mul_smul_comm a (x : R) y))

@[simp]
theorem coe_entryMul_apply {i j k : ι} (x : E.entry i j) (y : E.entry j k) :
    (E.entryMul i j k x y : R) = x * y :=
  (rfl)

/-- **The multiplication maps of the entry modules are associative.** -/
theorem entryMul_assoc {i j k l : ι} (x : E.entry i j) (y : E.entry j k) (z : E.entry k l) :
    E.entryMul i k l (E.entryMul i j k x y) z = E.entryMul i j l x (E.entryMul j k l y z) :=
  Subtype.ext (mul_assoc (x : R) y z)

/-- The **scalar pairing** `φ : A_{ij} × A_{ji} → A` of a generalized matrix algebra: the product
`xy ∈ A_{ii}`, read as a scalar through `A ≃ A_{ii}`. It is `(x, y) ↦ T(xy)`
(`TauCeti.GMAData.pairing_apply`). -/
def pairing (i j : ι) : E.entry i j →ₗ[A] E.entry j i →ₗ[A] A :=
  (E.entryMul i j i).compr₂ (E.entrySelfEquiv i).symm.toLinearMap

@[simp]
theorem pairing_apply {i j : ι} (x : E.entry i j) (y : E.entry j i) :
    E.pairing i j x y = E.trace (x * y) :=
  (rfl)

/-- **The product of opposite entries is a scalar**: `xy = φ(x, y) Eᵢ` for `x ∈ A_{ij}` and
`y ∈ A_{ji}`. -/
theorem pairing_smul_primitiveIdempotent {i j : ι} (x : E.entry i j) (y : E.entry j i) :
    E.pairing i j x y • E.primitiveIdempotent i = x * y :=
  E.trace_smul_primitiveIdempotent (E.mul_mem_entry x.property y.property)

/-- **The scalar pairing is symmetric**: `φ(x, y) = φ(y, x)` for `x ∈ A_{ij}` and `y ∈ A_{ji}`.
This is where centrality of the trace enters. -/
theorem pairing_comm {i j : ι} (x : E.entry i j) (y : E.entry j i) :
    E.pairing i j x y = E.pairing j i y x := by
  rw [pairing_apply, pairing_apply, trace_mul_comm]

theorem pairing_flip (i j : ι) : (E.pairing i j).flip = E.pairing j i :=
  LinearMap.ext₂ fun y x ↦ E.pairing_comm x y

/-- A product of opposite entries acts on `A_{ik}` from the left by its scalar pairing:
`x y z = φ(x, y) z`. -/
theorem pairing_smul_of_mem_entry {i j k : ι} (x : E.entry i j) (y : E.entry j i) {z : R}
    (hz : z ∈ E.entry i k) : E.pairing i j x y • z = x * y * z := by
  rw [← E.pairing_smul_primitiveIdempotent, smul_mul_assoc,
    E.primitiveIdempotent_mul_of_mem_entry hz]

/-- A product of opposite entries acts on `A_{ki}` from the right by its scalar pairing:
`z x y = φ(x, y) z`. -/
theorem pairing_smul_of_mem_entry_right {i j k : ι} (x : E.entry i j) (y : E.entry j i) {z : R}
    (hz : z ∈ E.entry k i) : E.pairing i j x y • z = z * (x * y) := by
  rw [← E.pairing_smul_primitiveIdempotent, mul_smul_comm,
    E.mul_primitiveIdempotent_of_mem_entry hz]

/-! ### Blocks as matrices over the entry modules -/

/-- The `(k, l)` entry `E_i^{0k} x E_j^{l0} ∈ A_{ij}` of an element `x` of the block `eᵢ R eⱼ`. -/
private def blockEntry {i j : ι} (x : R) (k : Fin (d i)) (l : Fin (d j)) : E.entry i j :=
  ⟨E.matrixUnit i 0 k * x * E.matrixUnit j l 0, E.matrixUnit_mul_mul_matrixUnit_mem_entry k l x⟩

private theorem coe_blockEntry {i j : ι} (x : R) (k : Fin (d i)) (l : Fin (d j)) :
    (E.blockEntry x k l : R) = E.matrixUnit i 0 k * x * E.matrixUnit j l 0 :=
  (rfl)

/-- The element `∑_{k,l} E_i^{k0} a_{kl} E_j^{0l}` of the block `eᵢ R eⱼ` with entries
`a_{kl} ∈ A_{ij}`. -/
private theorem sum_sum_matrixUnit_mul_mul_matrixUnit_mem {i j : ι}
    (a : Matrix (Fin (d i)) (Fin (d j)) (E.entry i j)) :
    ∑ k, ∑ l, E.matrixUnit i k 0 * (a k l : R) * E.matrixUnit j 0 l ∈
      TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent j) := by
  refine Submodule.sum_mem _ fun k _ ↦ Submodule.sum_mem _ fun l _ ↦ ?_
  have h : E.matrixUnit i k 0 * (a k l : R) * E.matrixUnit j 0 l = E.idempotent i *
      (E.matrixUnit i k 0 * (a k l : R) * E.matrixUnit j 0 l) * E.idempotent j := by
    simp only [← mul_assoc, idempotent_mul_matrixUnit]
    simp only [mul_assoc, matrixUnit_mul_idempotent]
  rw [h]
  exact TauCeti.mul_mul_mem_cornerSubmodule A _ _ _

private theorem matrixUnit_mul_sum_sum_mul_matrixUnit {i j : ι}
    (a : Matrix (Fin (d i)) (Fin (d j)) (E.entry i j)) (k : Fin (d i)) (l : Fin (d j)) :
    E.matrixUnit i 0 k * (∑ k', ∑ l', E.matrixUnit i k' 0 * (a k' l' : R) * E.matrixUnit j 0 l') *
      E.matrixUnit j l 0 = a k l := by
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_eq_single k, Finset.sum_eq_single l]
  · rw [← mul_assoc, ← mul_assoc, matrixUnit_mul_matrixUnit_same, mul_assoc,
      matrixUnit_mul_matrixUnit_same, ← primitiveIdempotent, ← primitiveIdempotent,
      E.mem_entry_iff.1 (a k l).property]
  · intro l' _ hl'
    simp [mul_assoc, matrixUnit_mul_matrixUnit, hl']
  · simp
  · intro k' _ hk'
    refine Finset.sum_eq_zero fun l' _ ↦ ?_
    simp [← mul_assoc, matrixUnit_mul_matrixUnit, Ne.symm hk']
  · simp

private theorem sum_sum_matrixUnit_mul_blockEntry_mul_matrixUnit {i j : ι} {x : R}
    (hx : x ∈ TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent j)) :
    ∑ k, ∑ l, E.matrixUnit i k 0 * (E.blockEntry x k l : R) * E.matrixUnit j 0 l = x := by
  have h (k : Fin (d i)) (l : Fin (d j)) :
      E.matrixUnit i k 0 * (E.blockEntry x k l : R) * E.matrixUnit j 0 l =
        E.matrixUnit i k k * x * E.matrixUnit j l l := by
    simp only [coe_blockEntry, ← mul_assoc, matrixUnit_mul_matrixUnit_same]
    simp only [mul_assoc, matrixUnit_mul_matrixUnit_same]
  simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, sum_matrixUnit_self]
  exact (TauCeti.mem_cornerSubmodule_iff A (E.isIdempotentElem_idempotent i)
    (E.isIdempotentElem_idempotent j)).1 hx

/-- **Blocks are matrices over the entry modules** (Bellaïche–Chenevier, §1.3.2): the block
`eᵢ R eⱼ` is identified with the `dᵢ × dⱼ` matrices with entries in `A_{ij}`, the `(k, l)` entry
of `x` being `E_i^{0k} x E_j^{l0}`. The inverse sends `(a_{kl})` to
`∑_{k,l} E_i^{k0} a_{kl} E_j^{0l}`. -/
def blockEquiv (i j : ι) :
    TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent j) ≃ₗ[A]
      Matrix (Fin (d i)) (Fin (d j)) (E.entry i j) where
  toFun x := Matrix.of (E.blockEntry x)
  invFun a := ⟨_, E.sum_sum_matrixUnit_mul_mul_matrixUnit_mem a⟩
  map_add' x y := by
    ext k l
    simp only [coe_blockEntry, Submodule.coe_add, mul_add, add_mul, of_apply, Matrix.add_apply]
  map_smul' a x := by
    ext k l
    simp only [coe_blockEntry, SetLike.val_smul, mul_smul_comm, smul_mul_assoc, of_apply,
      Matrix.smul_apply, RingHom.id_apply]
  left_inv x := Subtype.ext (E.sum_sum_matrixUnit_mul_blockEntry_mul_matrixUnit x.property)
  right_inv a := by
    ext k l
    exact E.matrixUnit_mul_sum_sum_mul_matrixUnit a k l

@[simp]
theorem coe_blockEquiv_apply {i j : ι}
    (x : TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent j)) (k : Fin (d i))
    (l : Fin (d j)) : (E.blockEquiv i j x k l : R) = E.matrixUnit i 0 k * x * E.matrixUnit j l 0 :=
  (rfl)

@[simp]
theorem coe_blockEquiv_symm_apply {i j : ι} (a : Matrix (Fin (d i)) (Fin (d j)) (E.entry i j)) :
    ((E.blockEquiv i j).symm a : R) =
      ∑ k, ∑ l, E.matrixUnit i k 0 * (a k l : R) * E.matrixUnit j 0 l :=
  (rfl)

/-- **Multiplication of blocks is matrix multiplication** over the entry modules: for `x ∈ eᵢ R eⱼ`
and `y ∈ eⱼ R eₖ`, the `(a, c)` entry of `xy` is `∑_b x_{ab} y_{bc}`, the products being taken by
`TauCeti.GMAData.entryMul`. -/
theorem coe_blockEquiv_mul_apply {i j k : ι}
    (x : TauCeti.cornerSubmodule A (E.idempotent i) (E.idempotent j))
    (y : TauCeti.cornerSubmodule A (E.idempotent j) (E.idempotent k))
    (a : Fin (d i)) (c : Fin (d k)) :
    (E.blockEquiv i k ⟨_, TauCeti.mul_mem_cornerSubmodule x.property y.property⟩ a c : R) =
      ∑ b, (E.entryMul i j k (E.blockEquiv i j x a b) (E.blockEquiv j k y b c) : R) := by
  simp only [coe_blockEquiv_apply, coe_entryMul_apply]
  have hx : (x : R) * E.idempotent j = x :=
    TauCeti.mul_eq_self_of_mem_cornerSubmodule_right (E.isIdempotentElem_idempotent j) x.property
  rw [show (x : R) * y = ∑ b, x * E.matrixUnit j b b * y by
    rw [← Finset.sum_mul, ← Finset.mul_sum, sum_matrixUnit_self, hx], Finset.mul_sum,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ ↦ ?_
  rw [← E.matrixUnit_mul_matrixUnit_same j b 0 b]
  simp only [mul_assoc]

end GMAData

end TauCeti
