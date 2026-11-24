/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.Data.Nat.BitField
import TauCeti.Algebra.CharP.Two
import TauCeti.Data.Nat.Bitwise

/-!
# Bit-packed square matrices in characteristic two

A square matrix of size `n` whose entries are `0` or `1` can be stored in one natural number, the
entry in row `i` and column `j` being the bit `n * i + j`. This file defines the type
`TauCeti.BitMatrix n` of such packed matrices, with a multiplication that is the matrix product
over a semiring of characteristic two, and the monoid homomorphism to Mathlib's matrices over any
such semiring.

The point is evaluation by the kernel. The product of two matrices of `Matrix (Fin n) (Fin n)
(ZMod 2)` is a sum over `Fin n` for each of the `n * n` entries, which is far too slow to decide
for `n` beyond a few dozen. The product here takes `n` steps on the binary representations:
column `j` of the left factor, spread out so that its entry of row `i` is the bit `n * i`, is
multiplied *as a natural number* by row `j` of the right factor. No carry occurs, so the result
is the packed matrix whose entry `(i, k)` is the product of the entries `(i, j)` and `(j, k)`, and
the exclusive-or of these `n` numbers is the packed matrix product. An equation between words in
matrices over `ZMod 2` is thus decided by `decide +kernel` on the packed side and transported along
`TauCeti.BitMatrix.toMatrixHom`, or along `TauCeti.BitMatrix.toGL` for invertible matrices.

## Main definitions

* `TauCeti.BitMatrix`: square matrices of bits packed in a natural number, a monoid with decidable
  equality.
* `TauCeti.BitMatrix.ofNat`: the packed matrix given by the low `n * n` bits of a natural number.
* `TauCeti.BitMatrix.toMatrix`, `TauCeti.BitMatrix.toMatrixHom`: the matrix of a packed matrix, as
  a function and, over a semiring of characteristic two, as a monoid homomorphism.
* `TauCeti.BitMatrix.toGL`: the induced homomorphism from the invertible packed matrices to the
  general linear group.

## Main results

* `TauCeti.BitMatrix.toMatrix_mul`, `TauCeti.BitMatrix.toMatrix_one`: the packed product and unit
  are the matrix product and the identity matrix.
* `TauCeti.BitMatrix.toMatrix_injective`, `TauCeti.BitMatrix.toGL_injective`: a packed matrix is
  determined by its matrix.
-/

public section

namespace TauCeti

/-- A square matrix of size `n` with entries in `{0, 1}`, packed in a natural number: the bit
`n * i + j` of `toNat` is the entry in row `i` and column `j`. -/
@[ext]
structure BitMatrix (n : ℕ) where
  /-- The packed entries: the bit `n * i + j` is the entry in row `i` and column `j`. -/
  toNat : ℕ
  /-- Only the `n * n` bits of the entries are used. -/
  toNat_lt : toNat < 2 ^ (n * n)

namespace BitMatrix

variable {n : ℕ} {R : Type*}

/-- Equality of packed matrices is decided on the packed numbers, by one comparison of natural
numbers. -/
instance : DecidableEq (BitMatrix n) := fun A B ↦
  decidable_of_iff (A.toNat = B.toNat) BitMatrix.ext_iff.symm

/-- The packed matrix whose entries are the `n * n` lowest bits of `M`. -/
@[expose] def ofNat (n M : ℕ) : BitMatrix n :=
  ⟨M % 2 ^ (n * n), Nat.mod_lt _ (Nat.two_pow_pos _)⟩

/-- The packed number of `ofNat n M` is `M` reduced to its `n * n` lowest bits. -/
@[simp]
theorem toNat_ofNat (n M : ℕ) : (ofNat n M).toNat = M % 2 ^ (n * n) :=
  (rfl)

/-- A packed matrix is recovered from its packed number. -/
@[simp]
theorem ofNat_toNat (A : BitMatrix n) : ofNat n A.toNat = A :=
  BitMatrix.ext (Nat.mod_eq_of_lt A.toNat_lt)

/-- The natural number with the bits `n * i` for `i < n`: the packed matrix whose column `0` is
full and whose other columns are empty. Masking with it isolates one column of a packed matrix,
which is how the product reads the columns of its left factor. -/
@[expose] def columnMask (n : ℕ) : ℕ :=
  (List.range n).foldl (fun acc i ↦ acc ||| 2 ^ (n * i)) 0

/-- The product of packed matrices. For each `j`, column `j` of `A` with its entries at the bits
`n * i` is multiplied as a natural number by row `j` of `B`, which gives the packed matrix with
entry `(i, k)` the product of the entries `(i, j)` of `A` and `(j, k)` of `B`; these are added up
by exclusive-or. -/
instance : Mul (BitMatrix n) where
  mul A B := ofNat n <| (List.range n).foldl
    (fun acc j ↦ acc ^^^ (A.toNat >>> j &&& columnMask n) * (B.toNat >>> (n * j) % 2 ^ n)) 0

/-- The packed identity matrix, with the bits `n * i + i` for `i < n`. -/
instance : One (BitMatrix n) where
  one := ofNat n <| (List.range n).foldl (fun acc i ↦ acc ||| 2 ^ (n * i + i)) 0

/-- The product unfolded: the exclusive-or over `j` of the natural-number products of column `j`
of the left factor and row `j` of the right factor. -/
protected theorem mul_def (A B : BitMatrix n) :
    A * B = ofNat n ((List.range n).foldl
      (fun acc j ↦ acc ^^^ (A.toNat >>> j &&& columnMask n) * (B.toNat >>> (n * j) % 2 ^ n)) 0) :=
  (rfl)

/-- The unit unfolded: the bits `n * i + i` for `i < n`. -/
protected theorem one_def :
    (1 : BitMatrix n) = ofNat n ((List.range n).foldl (fun acc i ↦ acc ||| 2 ^ (n * i + i)) 0) :=
  (rfl)

/-- **The matrix of a packed matrix**, over any type with `0` and `1`: the entry in row `i` and
column `j` is `1` if the bit `n * i + j` is set and `0` otherwise. -/
def toMatrix (R : Type*) [Zero R] [One R] (A : BitMatrix n) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun i j ↦ if A.toNat.testBit (n * i + j) then 1 else 0

/-- The entries of the matrix of a packed matrix. -/
@[simp]
theorem toMatrix_apply [Zero R] [One R] (A : BitMatrix n) (i j : Fin n) :
    toMatrix R A i j = if A.toNat.testBit (n * i + j) then 1 else 0 :=
  (rfl)

/-- The entries of the matrix of `ofNat n M` are the bits of `M`. -/
theorem toMatrix_ofNat_apply [Zero R] [One R] (M : ℕ) (i j : Fin n) :
    toMatrix R (ofNat n M) i j = if M.testBit (n * i + j) then 1 else 0 := by
  simp [Nat.testBit_mod_two_pow, Nat.mul_add_lt_mul_of_lt_of_lt i.isLt j.isLt]

/-! ### Bits of the masks and of the product -/

/-- The bits of the column mask: at an entry position, the bit is set exactly in column `0`. -/
theorem testBit_columnMask {i k : ℕ} (hk : k < n) :
    (columnMask n).testBit (n * i + k) = decide (k = 0 ∧ i < n) := by
  simp only [columnMask, Nat.testBit_foldl_or, Nat.zero_testBit, Bool.false_or, List.any_eq,
    List.mem_range, Nat.testBit_two_pow, decide_eq_true_eq]
  refine decide_eq_decide.mpr ⟨?_, ?_⟩
  · rintro ⟨i', hi', h⟩
    -- Division of the position `n * i' = n * i + k` by `n` gives `i' = i` and `k = 0`.
    have hn : 0 < n := by omega
    have h1 := (Nat.div_mod_unique hn).mpr ⟨(Nat.add_comm k (n * i)).trans h.symm, hk⟩
    rw [Nat.mul_div_cancel_left i' hn, Nat.mul_mod_right] at h1
    exact ⟨h1.2.symm, h1.1 ▸ hi'⟩
  · rintro ⟨rfl, hi⟩
    exact ⟨i, hi, rfl⟩

/-- Column `j` of a packed matrix, isolated by the column mask, as an array of fields of width
`n`: field `i` is the entry `(i, j)`. -/
private theorem bitField_shiftRight_and_columnMask (M j i : ℕ) :
    Nat.bitField n (M >>> j &&& columnMask n) i =
      if i < n ∧ M.testBit (n * i + j) then 1 else 0 := by
  refine Nat.eq_of_testBit_eq fun k ↦ ?_
  rw [Nat.testBit_bitField]
  by_cases hk : k < n
  · rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_columnMask hk]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · by_cases hi : i < n <;> by_cases hb : M.testBit (n * i + j) <;>
        simp [hi, hb, hk, Nat.add_comm j]
    · have hk' : k ≠ 0 := by omega
      split_ifs <;> simp [hk', Nat.testBit_lt_two_pow (Nat.one_lt_two_pow hk')]
  · have h1 : (if i < n ∧ M.testBit (n * i + j) then 1 else 0 : ℕ) < 2 ^ k := by
      split_ifs with h
      · exact Nat.one_lt_two_pow (by omega)
      · exact Nat.two_pow_pos k
    simp [hk, Nat.testBit_lt_two_pow h1]

/-- One term of the packed product: at the position of the entry `(i, k)`, the natural-number
product of column `j` of `M` and row `j` of `N` has the product of the entries `(i, j)` and
`(j, k)`. -/
private theorem testBit_column_mul_row (M N j : ℕ) {i k : ℕ} (hk : k < n) :
    ((M >>> j &&& columnMask n) * (N >>> (n * j) % 2 ^ n)).testBit (n * i + k) =
      (decide (i < n) && M.testBit (n * i + j) && N.testBit (n * j + k)) := by
  have hr : N >>> (n * j) % 2 ^ n < 2 ^ n := Nat.mod_lt _ (Nat.two_pow_pos n)
  have hfield := Nat.bitField_mul_of_forall_bitField_mul_lt
    (w := n) (M := M >>> j &&& columnMask n) (r := N >>> (n * j) % 2 ^ n) (i := i) (fun l _ ↦ by
      rw [bitField_shiftRight_and_columnMask]
      split_ifs <;> omega)
  have hbit := Nat.testBit_bitField n ((M >>> j &&& columnMask n) * (N >>> (n * j) % 2 ^ n)) i k
  rw [hfield, bitField_shiftRight_and_columnMask] at hbit
  simp only [hk, decide_true, Bool.true_and] at hbit
  rw [← hbit]
  by_cases hi : i < n <;> by_cases hb : M.testBit (n * i + j) <;>
    simp [hi, hb, hk, Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]

/-! ### The matrix of a product and of the unit -/

/-- The packed unit is the identity matrix. -/
@[simp]
theorem toMatrix_one [Zero R] [One R] : toMatrix R (1 : BitMatrix n) = 1 := by
  ext i j
  have hiff : (∃ i' < n, n * i' + i' = n * i + j) ↔ i = j := by
    constructor
    · rintro ⟨i', hi', h⟩
      -- Division of the position `n * i' + i' = n * i + j` by `n` gives `i = i'` and `j = i'`.
      have h1 := (Nat.div_mod_unique i.pos).mpr ⟨Nat.add_comm j (n * i), j.isLt⟩
      have h2 := (Nat.div_mod_unique i.pos).mpr ⟨(Nat.add_comm i' (n * i')).trans h, hi'⟩
      exact Fin.ext ((h1.1.symm.trans h2.1).trans (h2.2.symm.trans h1.2))
    · rintro rfl
      exact ⟨i, i.isLt, rfl⟩
  simp only [BitMatrix.one_def, toMatrix_ofNat_apply, Nat.testBit_foldl_or, Nat.zero_testBit,
    Bool.false_or, List.any_eq_true, List.mem_range, Nat.testBit_two_pow, decide_eq_true_eq, hiff,
    Matrix.one_apply]

/-- **The packed product is the matrix product** over a semiring of characteristic two. -/
@[simp]
theorem toMatrix_mul [NonAssocSemiring R] [CharP R 2] (A B : BitMatrix n) :
    toMatrix R (A * B) = toMatrix R A * toMatrix R B := by
  ext i k
  -- Both sides are sums over the list of the indices `j`: the bit of the exclusive-or of the
  -- terms of the packed product, and the entry of the matrix product.
  rw [BitMatrix.mul_def, toMatrix_ofNat_apply, Matrix.mul_apply, ite_testBit_foldl_xor_of_charTwo,
    Fin.sum_univ_def, ← List.map_coe_finRange_eq_range, List.map_map]
  simp only [Nat.zero_testBit, Bool.false_eq_true, ite_false, zero_add]
  refine congrArg List.sum (List.map_congr_left fun j _ ↦ ?_)
  rw [Function.comp_apply, testBit_column_mul_row _ _ _ k.isLt]
  by_cases ha : A.toNat.testBit (n * i + j) <;> by_cases hb : B.toNat.testBit (n * j + k) <;>
    simp [ha, hb, i.isLt]

/-- A packed matrix is determined by its matrix over a type in which `1 ≠ 0`. -/
theorem toMatrix_injective [Zero R] [One R] [NeZero (1 : R)] :
    Function.Injective (toMatrix R : BitMatrix n → Matrix (Fin n) (Fin n) R) := by
  intro A B h
  refine BitMatrix.ext (Nat.eq_of_testBit_eq fun p ↦ ?_)
  by_cases hp : p < n * n
  · have hn : 0 < n := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hp
    have hq : p / n < n := Nat.div_lt_of_lt_mul hp
    have hpe : n * (p / n) + p % n = p := Nat.div_add_mod p n
    have hentry := congrFun (congrFun h ⟨p / n, hq⟩) ⟨p % n, Nat.mod_lt p hn⟩
    simp only [toMatrix_apply, hpe] at hentry
    by_cases ha : A.toNat.testBit p <;> by_cases hb : B.toNat.testBit p <;>
      simp_all
  · have hle : 2 ^ (n * n) ≤ 2 ^ p := Nat.pow_le_pow_right Nat.two_pos (by omega)
    rw [Nat.testBit_lt_two_pow (A.toNat_lt.trans_le hle),
      Nat.testBit_lt_two_pow (B.toNat_lt.trans_le hle)]

/-- Two packed matrices have the same matrix over a type in which `1 ≠ 0` exactly when they are
equal. -/
@[simp]
theorem toMatrix_inj [Zero R] [One R] [NeZero (1 : R)] {A B : BitMatrix n} :
    toMatrix R A = toMatrix R B ↔ A = B :=
  toMatrix_injective.eq_iff

/-! ### The monoid of packed matrices -/

/-- Packed matrices form a monoid under the packed product. The laws are those of the matrices
over `ZMod 2`, to which the packed matrices map injectively. -/
instance : Monoid (BitMatrix n) where
  mul_assoc A B C := toMatrix_injective (R := ZMod 2) (by simp only [toMatrix_mul, mul_assoc])
  one_mul A := toMatrix_injective (R := ZMod 2) (by simp only [toMatrix_mul, toMatrix_one, one_mul])
  mul_one A := toMatrix_injective (R := ZMod 2) (by simp only [toMatrix_mul, toMatrix_one, mul_one])

/-- **The matrix of a packed matrix as a monoid homomorphism**, over a semiring of characteristic
two. -/
def toMatrixHom (R : Type*) [Semiring R] [CharP R 2] :
    BitMatrix n →* Matrix (Fin n) (Fin n) R where
  toFun := toMatrix R
  map_one' := toMatrix_one
  map_mul' := toMatrix_mul

/-- The homomorphism `toMatrixHom` is the function `toMatrix`. -/
@[simp]
theorem coe_toMatrixHom [Semiring R] [CharP R 2] :
    ⇑(toMatrixHom R : BitMatrix n →* Matrix (Fin n) (Fin n) R) = toMatrix R :=
  (rfl)

/-- The matrix of a power of a packed matrix. -/
@[simp]
theorem toMatrix_pow [Semiring R] [CharP R 2] (A : BitMatrix n) (k : ℕ) :
    toMatrix R (A ^ k) = toMatrix R A ^ k :=
  map_pow (toMatrixHom R) A k

/-- **The invertible matrix of an invertible packed matrix**: the homomorphism from the units of
the packed matrices to the general linear group over a semiring of characteristic two. -/
def toGL (R : Type*) [Semiring R] [CharP R 2] : (BitMatrix n)ˣ →* GL (Fin n) R :=
  Units.map (toMatrixHom R)

/-- The underlying matrix of `toGL R u` is the matrix of the packed matrix `u`. -/
@[simp]
theorem coe_toGL [Semiring R] [CharP R 2] (u : (BitMatrix n)ˣ) :
    (toGL R u : Matrix (Fin n) (Fin n) R) = toMatrix R (u : BitMatrix n) :=
  (rfl)

/-- An invertible packed matrix is determined by its invertible matrix. -/
theorem toGL_injective [Semiring R] [CharP R 2] :
    Function.Injective (toGL R : (BitMatrix n)ˣ → GL (Fin n) R) :=
  haveI : Nontrivial R := CharP.nontrivial_of_char_ne_one (R := R) (v := 2) (by norm_num)
  Units.map_injective toMatrix_injective

end BitMatrix

end TauCeti
