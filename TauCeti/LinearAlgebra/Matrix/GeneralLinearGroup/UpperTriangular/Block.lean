/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `Matrix.BlockTriangular` and `Matrix.toSquareBlock` occur in the statements below.
public import Mathlib.LinearAlgebra.Matrix.Block
-- `TauCeti.upperTriangularGroup` is the block triangular group of the identity ranking.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
-- Non-public: the counting argument passes through the quotient by the kernel.
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Groups of invertible block triangular matrices and their orders

For a ranking `b : m → α` of the indices of a square matrix by a linear order, the invertible
matrices that are block upper triangular for `b` (`Matrix.BlockTriangular`) form a subgroup
`TauCeti.blockTriangularGroup R b` of `GL m R`, the standard parabolic subgroup with the blocks
`{i | b i = a}`. Reading off the diagonal blocks is a surjective homomorphism onto the Levi
factor `∏ₐ GL {i // b i = a} R`, whose kernel, the unipotent radical, is in bijection with the
entries strictly above the diagonal blocks. Over any commutative ring `R` this gives

`#P = ∏ₐ #GL {i // b i = a} R · #R ^ #{(i, j) | b i < b j}`

(`TauCeti.natCard_blockTriangularGroup`). It is stated with `Nat.card`, so that it needs no
finiteness assumption on `R`.

The case of one block indexed by `N` followed by `j` blocks indexed by `T`
(`TauCeti.exists_natCard_blockTriangularGroup_sum_eq`) is the order
`#GL N R · #GL T R ^ j · #R ^ e`, with `e` independent of `R`, of the level groups of the chain of
theta lifts in the roadmap `ShortGRH/DeterminantsOfThetaLiftChains`, §4.1 (a).

## Main declarations

* `Matrix.BlockTriangular.toSquareBlock_mul`: on a diagonal block, the product of block triangular
  matrices is the product of their blocks.
* `Matrix.blockUnipotent N`: the block unipotent matrix with the entries `N` above the diagonal
  blocks; `Matrix.det_blockUnipotent` says its determinant is `1`.
* `TauCeti.blockTriangularGroup R b`: the invertible matrices that are block upper triangular
  for `b`; `TauCeti.upperTriangularGroup_eq_blockTriangularGroup` identifies the upper triangular
  group as the case `b = id`.
* `TauCeti.BlockTriangularGroup.diagBlocks`: the homomorphism to the product of the general
  linear groups of the diagonal blocks, with `TauCeti.BlockTriangularGroup.diagBlocks_surjective`
  and `TauCeti.BlockTriangularGroup.mem_ker_diagBlocks_iff`.
* `TauCeti.BlockTriangularGroup.kerDiagBlocksEquiv`: its kernel is in bijection with the families
  of entries `(i, j)` with `b i < b j`.
* `TauCeti.natCard_blockTriangularGroup`: the order of the group.
* `TauCeti.exists_natCard_blockTriangularGroup_sum_eq`: the order for the blocks `N, T, …, T`.

## References

* The case of the blocks `N, T, …, T` is adapted from grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic, PBC), `src/New/Determinant/Chain/TriangleNorms.lean`,
  `New.exists_card_parabolic_blockNumber_eq`, which proves it by induction on `j`.
-/

public section

open Matrix

/-! ### Diagonal blocks of block triangular matrices -/

namespace Matrix

variable {m α R : Type*} [LinearOrder α] [CommRing R] {b : m → α}

/-- On a diagonal block, the product of two block triangular matrices is the product of their
diagonal blocks: a term `A i k * B k j` with `b i = b j = a` vanishes unless `b k = a`. -/
theorem BlockTriangular.toSquareBlock_mul [Fintype m] {A B : Matrix m m R}
    (hA : A.BlockTriangular b) (hB : B.BlockTriangular b) (a : α) :
    (A * B).toSquareBlock b a = A.toSquareBlock b a * B.toSquareBlock b a := by
  ext i j
  have h_out (k : {k // ¬b k = a}) : A i k * B k j = 0 := by
    rcases lt_or_gt_of_ne k.property with hk | hk
    · rw [hA (i.property.symm ▸ hk : b k < b i), zero_mul]
    · rw [hB (j.property.symm ▸ hk : b j < b k), mul_zero]
  rw [toSquareBlock_def, of_apply, Matrix.mul_apply,
    ← Fintype.sum_subtype_add_sum_subtype (fun k => b k = a), Fintype.sum_eq_zero _ h_out,
    add_zero]
  rfl

omit [LinearOrder α] in
/-- The diagonal blocks of the identity matrix are identity matrices. -/
@[simp]
theorem toSquareBlock_one [DecidableEq m] (b : m → α) (a : α) :
    (1 : Matrix m m R).toSquareBlock b a = 1 :=
  toBlock_one_self _

omit [LinearOrder α] [CommRing R] in
/-- Two matrices with the same diagonal blocks agree at the positions in a diagonal block. -/
theorem apply_eq_of_toSquareBlock_eq {A B : Matrix m m R} (h : ∀ a, A.toSquareBlock b a =
    B.toSquareBlock b a) {i j : m} (hij : b i = b j) : A i j = B i j := by
  simpa [toSquareBlock_def] using congr_fun₂ (h (b i)) ⟨i, rfl⟩ ⟨j, hij.symm⟩

/-- The block diagonal matrix with the diagonal blocks `M a` on the fibres `{i | b i = a}`, that
is `blockDiagonal' M` reindexed along `Equiv.sigmaFiberEquiv b`, is block triangular for `b`. -/
theorem blockTriangular_reindex_blockDiagonal'
    (M : (a : α) → Matrix {i // b i = a} {i // b i = a} R) :
    (reindex (Equiv.sigmaFiberEquiv b) (Equiv.sigmaFiberEquiv b) (blockDiagonal' M)).BlockTriangular
      b := fun i j hij => by
  simp [Equiv.sigmaFiberEquiv, blockDiagonal'_apply, hij.ne']

/-- The diagonal blocks of the block diagonal matrix with the blocks `M a` on the fibres of `b` are
the `M a`. -/
theorem toSquareBlock_reindex_blockDiagonal'
    (M : (a : α) → Matrix {i // b i = a} {i // b i = a} R) (a : α) :
    (reindex (Equiv.sigmaFiberEquiv b) (Equiv.sigmaFiberEquiv b) (blockDiagonal' M)).toSquareBlock
      b a = M a := by
  ext ⟨i, hi⟩ ⟨j, hj⟩
  subst hi
  have h_j : (Equiv.sigmaFiberEquiv b).symm j = ⟨b i, ⟨j, hj⟩⟩ := Sigma.subtype_ext hj rfl
  have h_i : (Equiv.sigmaFiberEquiv b).symm i = ⟨b i, ⟨i, rfl⟩⟩ := rfl
  simp [toSquareBlock_def, h_i, h_j]

/-- The unipotent matrix with the entries `N p` at the positions `p = (i, j)` with `b i < b j`,
identity diagonal blocks, and zeros below the diagonal blocks. -/
def blockUnipotent [DecidableEq m] (N : {p : m × m // b p.1 < b p.2} → R) : Matrix m m R :=
  of fun i j => if h : b i < b j then N ⟨(i, j), h⟩ else (1 : Matrix m m R) i j

/-- The block unipotent matrix is block upper triangular. -/
theorem blockTriangular_blockUnipotent [DecidableEq m] (N : {p : m × m // b p.1 < b p.2} → R) :
    (blockUnipotent N).BlockTriangular b := fun i j hij => by
  simp [blockUnipotent, hij.not_gt, one_apply_ne (ne_of_apply_ne b hij.ne')]

/-- The block unipotent matrix has determinant `1`: its diagonal blocks are identity matrices. -/
theorem det_blockUnipotent [Fintype m] [DecidableEq m] (N : {p : m × m // b p.1 < b p.2} → R) :
    (blockUnipotent N).det = 1 := by
  rw [(blockTriangular_blockUnipotent N).det]
  refine Finset.prod_eq_one fun a _ => ?_
  have h_block : (blockUnipotent N).toSquareBlock b a = 1 := by
    rw [← toSquareBlock_one b a]
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp [blockUnipotent, toSquareBlock_def, hi, hj]
  rw [h_block, det_one]

end Matrix

/-! ### The block triangular group -/

namespace TauCeti

universe u

variable {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] (R : Type*) [CommRing R]

/-- The subgroup of `GL m R` of matrices that are block upper triangular for the ranking
`b : m → α`: the `(i, j)` entry vanishes whenever `b j < b i`. -/
def blockTriangularGroup (b : m → α) : Subgroup (GL m R) where
  carrier := {g | (g : Matrix m m R).BlockTriangular b}
  one_mem' := blockTriangular_one
  mul_mem' hg hh := hg.mul hh
  inv_mem' {g} hg := by
    simpa only [Set.mem_ofPred_eq, coe_units_inv] using blockTriangular_inv_of_blockTriangular hg

variable {R} {b : m → α}

/-- Membership in the block triangular group: the matrix is block upper triangular. -/
@[simp]
theorem mem_blockTriangularGroup_iff {g : GL m R} :
    g ∈ blockTriangularGroup R b ↔ (g : Matrix m m R).BlockTriangular b :=
  Iff.rfl

namespace BlockTriangularGroup

variable (b) in
/-- The diagonal block `a` of an invertible block triangular matrix, as an invertible matrix:
a homomorphism `P →* GL {i // b i = a} R`. -/
def diagBlock (a : α) : blockTriangularGroup R b →* GL {i // b i = a} R where
  toFun g :=
    { val := ((g : GL m R) : Matrix m m R).toSquareBlock b a
      inv := (((g : GL m R)⁻¹ : GL m R) : Matrix m m R).toSquareBlock b a
      val_inv := by
        rw [← BlockTriangular.toSquareBlock_mul g.property (inv_mem g.property), ← Units.val_mul,
          mul_inv_cancel, Units.val_one, toSquareBlock_one]
      inv_val := by
        rw [← BlockTriangular.toSquareBlock_mul (inv_mem g.property) g.property, ← Units.val_mul,
          inv_mul_cancel, Units.val_one, toSquareBlock_one] }
  map_one' := Units.ext (toSquareBlock_one b a)
  map_mul' g h := Units.ext (BlockTriangular.toSquareBlock_mul g.property h.property a)

/-- The matrix of `diagBlock b a g` is the diagonal block `a` of `g`. -/
@[simp]
theorem coe_diagBlock (a : α) (g : blockTriangularGroup R b) :
    (diagBlock b a g : Matrix {i // b i = a} {i // b i = a} R) =
      ((g : GL m R) : Matrix m m R).toSquareBlock b a := by
  simp [diagBlock]

variable (R b) in
/-- The diagonal blocks of an invertible block triangular matrix: the projection
`P →* ∏ₐ GL {i // b i = a} R` of the parabolic subgroup onto its Levi factor. -/
def diagBlocks : blockTriangularGroup R b →* ((a : α) → GL {i // b i = a} R) :=
  MonoidHom.pi (diagBlock b)

/-- The component `a` of `diagBlocks R b g` is `diagBlock b a g`. -/
@[simp]
theorem diagBlocks_apply (g : blockTriangularGroup R b) (a : α) :
    diagBlocks R b g a = diagBlock b a g := by
  simp [diagBlocks]

section Section

variable [Fintype α]

variable (R b) in
/-- The block diagonal embedding of the Levi factor `∏ₐ GL {i // b i = a} R` in the parabolic
subgroup, a section of `diagBlocks`: `blockDiagonal'` reindexed along `Equiv.sigmaFiberEquiv b`. -/
noncomputable def blockDiagonalHom : ((a : α) → GL {i // b i = a} R) →* blockTriangularGroup R b :=
  ((Units.map ((reindexRingEquiv R (Equiv.sigmaFiberEquiv b)).toMonoidHom.comp
      (blockDiagonal'RingHom (fun a => {i // b i = a}) R).toMonoidHom)).comp
    MulEquiv.piUnits.symm.toMonoidHom).codRestrict _ fun g =>
      blockTriangular_reindex_blockDiagonal' fun a => (g a).val

/-- The block diagonal embedding is a section of the diagonal blocks. -/
@[simp]
theorem diagBlocks_blockDiagonalHom (g : (a : α) → GL {i // b i = a} R) :
    diagBlocks R b (blockDiagonalHom R b g) = g := by
  funext a
  ext : 1
  rw [diagBlocks_apply, coe_diagBlock]
  exact toSquareBlock_reindex_blockDiagonal' (fun a => (g a).val) a

end Section

/-- The diagonal blocks of the invertible block triangular matrices are arbitrary. -/
theorem diagBlocks_surjective [Finite α] : Function.Surjective (diagBlocks R b) := by
  have := Fintype.ofFinite α
  exact fun g => ⟨blockDiagonalHom R b g, diagBlocks_blockDiagonalHom g⟩

/-- An invertible block triangular matrix lies in the kernel of `diagBlocks`, the unipotent
radical, exactly when its diagonal blocks are identity matrices. -/
theorem mem_ker_diagBlocks_iff {g : blockTriangularGroup R b} :
    g ∈ (diagBlocks R b).ker ↔
      ∀ i j, b i = b j → ((g : GL m R) : Matrix m m R) i j = (1 : Matrix m m R) i j := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg i j hij
    refine apply_eq_of_toSquareBlock_eq (fun a => ?_) hij
    rw [← coe_diagBlock, ← diagBlocks_apply, hg]
    simp
  · intro hg
    funext a
    ext : 1
    rw [diagBlocks_apply, coe_diagBlock, Pi.one_apply, Units.val_one, ← toSquareBlock_one b a]
    ext ⟨i, hi⟩ ⟨j, hj⟩
    exact hg i j (hi.trans hj.symm)

/-- The unipotent matrix `blockUnipotent N` as an element of `GL m R`. -/
noncomputable def blockUnipotentGL (N : {p : m × m // b p.1 < b p.2} → R) : GL m R :=
  ((isUnit_iff_isUnit_det _).mpr (by rw [det_blockUnipotent]; exact isUnit_one) :
    IsUnit (blockUnipotent N)).unit

/-- The matrix of `blockUnipotentGL N` is `blockUnipotent N`. -/
@[simp]
theorem coe_blockUnipotentGL (N : {p : m × m // b p.1 < b p.2} → R) :
    (blockUnipotentGL N : Matrix m m R) = blockUnipotent N := by
  simp [blockUnipotentGL]

variable (R b) in
/-- The unipotent radical, the kernel of `diagBlocks`, is in bijection with the families of
entries at the positions `(i, j)` with `b i < b j`. -/
noncomputable def kerDiagBlocksEquiv :
    (diagBlocks R b).ker ≃ ({p : m × m // b p.1 < b p.2} → R) where
  toFun g p := (((g : blockTriangularGroup R b) : GL m R) : Matrix m m R) p.val.1 p.val.2
  invFun N :=
    ⟨⟨blockUnipotentGL N, by simpa using blockTriangular_blockUnipotent N⟩,
      mem_ker_diagBlocks_iff.mpr fun i j hij => by simp [blockUnipotent, hij]⟩
  left_inv g := by
    refine Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_)))
    simp only [coe_blockUnipotentGL, blockUnipotent, of_apply]
    split_ifs with h
    · rfl
    rcases (not_lt.mp h).eq_or_lt with h | h
    · exact (mem_ker_diagBlocks_iff.mp g.property i j h.symm).symm
    · rw [g.val.property h, one_apply_ne (ne_of_apply_ne b h.ne')]
  right_inv N := by
    funext p
    simp [blockUnipotent, p.property]

end BlockTriangularGroup

open BlockTriangularGroup

/-- **The order of a block triangular group.** The invertible matrices that are block upper
triangular for a ranking `b : m → α` by a finite linear order form a group of order
`∏ₐ #GL {i // b i = a} R · #R ^ #{(i, j) | b i < b j}`. -/
theorem natCard_blockTriangularGroup [Fintype α] (b : m → α) :
    Nat.card (blockTriangularGroup R b) =
      (∏ a, Nat.card (GL {i // b i = a} R)) *
        Nat.card R ^ Nat.card {p : m × m // b p.1 < b p.2} := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (diagBlocks R b).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ diagBlocks_surjective).toEquiv,
    Nat.card_pi, Nat.card_congr (kerDiagBlocksEquiv R b), Nat.card_fun]

section Sum

variable {N T : Type*} {j : ℕ}

/-- The block `0` of `N ⊕ Fin j × T`, ranked by `Sum.elim 0 (·.1.succ)`, is `N`. -/
def sumBlockZeroEquiv :
    {i : N ⊕ Fin j × T // Sum.elim (fun _ => 0) (fun p => p.1.succ) i = (0 : Fin (j + 1))} ≃ N where
  toFun i := match i with
    | ⟨.inl x, _⟩ => x
    | ⟨.inr p, h⟩ => absurd h (Fin.succ_ne_zero _)
  invFun x := ⟨.inl x, rfl⟩
  left_inv := by
    rintro ⟨x | p, h⟩
    · rfl
    · exact absurd h (Fin.succ_ne_zero _)

/-- The block `k + 1` of `N ⊕ Fin j × T`, ranked by `Sum.elim 0 (·.1.succ)`, is the `k`-th copy
of `T`. -/
def sumBlockSuccEquiv (k : Fin j) :
    {i : N ⊕ Fin j × T // Sum.elim (fun _ => 0) (fun p => p.1.succ) i = k.succ} ≃ T where
  toFun i := match i with
    | ⟨.inl _, h⟩ => absurd h.symm (Fin.succ_ne_zero _)
    | ⟨.inr p, _⟩ => p.2
  invFun t := ⟨.inr (k, t), rfl⟩
  left_inv := by
    rintro ⟨x | ⟨l, t⟩, h⟩
    · exact absurd h.symm (Fin.succ_ne_zero _)
    · obtain rfl : l = k := Fin.succ_injective _ h
      rfl

end Sum

/-- **The order of the block triangular group with blocks `N, T, …, T`.** Rank the indices
`N ⊕ Fin j × T` by sending `N` to the block `0` and the `k`-th copy of `T` to the block `k + 1`.
The invertible block upper triangular matrices form a group of order
`#GL N R · #GL T R ^ j · #R ^ e`, with `e` independent of the commutative ring `R`. -/
theorem exists_natCard_blockTriangularGroup_sum_eq (N T : Type*) [Fintype N] [DecidableEq N]
    [Fintype T] [DecidableEq T] (j : ℕ) :
    ∃ e : ℕ, ∀ (R : Type u) [CommRing R],
      Nat.card (blockTriangularGroup R
          (Sum.elim (fun _ => 0) (fun p => p.1.succ) : N ⊕ Fin j × T → Fin (j + 1))) =
        Nat.card (GL N R) * Nat.card (GL T R) ^ j * Nat.card R ^ e := by
  let b : N ⊕ Fin j × T → Fin (j + 1) := Sum.elim (fun _ => 0) (fun p => p.1.succ)
  refine ⟨Nat.card {p : (N ⊕ Fin j × T) × (N ⊕ Fin j × T) // b p.1 < b p.2}, fun R _ => ?_⟩
  rw [natCard_blockTriangularGroup, Fin.prod_univ_succ,
    Nat.card_congr (GeneralLinearGroup.reindex (R := R) sumBlockZeroEquiv).toEquiv,
    Fintype.prod_congr _ (fun _ => Nat.card (GL T R)) fun k =>
      Nat.card_congr (GeneralLinearGroup.reindex (R := R) (sumBlockSuccEquiv k)).toEquiv,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_assoc]

section UpperTriangular

variable (m : Type*) [Fintype m] [LinearOrder m] (R : Type*) [CommRing R]

/-- The upper triangular group is the block triangular group of the identity ranking. -/
theorem upperTriangularGroup_eq_blockTriangularGroup :
    upperTriangularGroup m R = blockTriangularGroup R (id : m → m) := by
  ext g
  rw [UpperTriangularGroup.mem_iff, mem_blockTriangularGroup_iff]

end UpperTriangular

end TauCeti
