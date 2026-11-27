/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- `TauCeti.blockTriangularGroup` is the group whose diagonal blocks are read off below.
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Basic
-- `Matrix.BlockTriangular.toSquareBlock_mul` makes the diagonal blocks multiplicative, and
-- `TauCeti.blockUnitriangular_unitDiagonalMatrixOfEntries` gives the unipotent radical.
public import TauCeti.LinearAlgebra.Matrix.LDU
-- Non-public: the counting argument passes through the quotient by the kernel.
import Mathlib.GroupTheory.Coset.Card
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Groups of invertible block triangular matrices and their orders

For a ranking `b : m → α` of the indices of a square matrix by a linear order, the invertible
matrices that are block upper triangular for `b` (`Matrix.BlockTriangular`) form the subgroup
`TauCeti.blockTriangularGroup R b` of `GL m R`, the standard parabolic subgroup with the blocks
`{i | b i = a}`. Reading off the diagonal blocks is a surjective homomorphism onto the Levi
factor `∏ₐ GL {i // b i = a} R`, whose kernel, the unipotent radical, is in bijection with the
entries strictly above the diagonal blocks. Over any commutative ring `R` this gives

`#P = ∏ₐ #GL {i // b i = a} R · #R ^ #{(i, j) | b i < b j}`

(`TauCeti.natCard_blockTriangularGroup`). It is stated with `Nat.card`, so that it needs no
finiteness assumption on `R`.

The case of one block indexed by `N` followed by `j` blocks indexed by `T`
(`TauCeti.exists_natCard_blockTriangularGroup_sum_eq`) is the order
`#GL N R · #GL T R ^ j · #R ^ e`, with `e` independent of `R`, of the level groups of a chain of
theta lifts.

## Main declarations

* `TauCeti.BlockTriangularGroup.diagBlocks`: the homomorphism to the product of the general
  linear groups of the diagonal blocks, with `TauCeti.BlockTriangularGroup.diagBlocks_surjective`
  and `TauCeti.BlockTriangularGroup.mem_ker_diagBlocks_iff`.
* `TauCeti.BlockTriangularGroup.kerDiagBlocksEquiv`: its kernel is in bijection with the families
  of entries `(i, j)` with `b i < b j`, through the unit diagonal matrices
  `TauCeti.BlockTriangularGroup.blockUnipotentGL`.
* `TauCeti.natCard_blockTriangularGroup`: the order of the group.
* `TauCeti.exists_natCard_blockTriangularGroup_sum_eq`: the order for the blocks `N, T, …, T`.

## References

* The case of the blocks `N, T, …, T` is adapted from grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic, PBC), `src/New/Determinant/Chain/TriangleNorms.lean`,
  `New.exists_card_parabolic_blockNumber_eq`, which proves it by induction on `j`.
-/

public section

open Matrix

namespace TauCeti

universe u

variable {m α : Type*} [Fintype m] [DecidableEq m] [LinearOrder α] {R : Type*} [CommRing R]
  {b : m → α}

namespace BlockTriangularGroup

variable (b) in
/-- The diagonal block `a` of an invertible block triangular matrix, as an invertible matrix:
a homomorphism `P →* GL {i // b i = a} R`. -/
def diagBlock (a : α) : blockTriangularGroup R b →* GL {i // b i = a} R where
  toFun g :=
    { val := ((g : GL m R) : Matrix m m R).toSquareBlock b a
      inv := (((g : GL m R)⁻¹ : GL m R) : Matrix m m R).toSquareBlock b a
      val_inv := by
        rw [← BlockTriangular.toSquareBlock_mul (mem_blockTriangularGroup_iff.mp g.property)
          (mem_blockTriangularGroup_iff.mp (inv_mem g.property)), ← Units.val_mul,
          mul_inv_cancel, Units.val_one, toSquareBlock_one]
      inv_val := by
        rw [← BlockTriangular.toSquareBlock_mul
          (mem_blockTriangularGroup_iff.mp (inv_mem g.property))
          (mem_blockTriangularGroup_iff.mp g.property), ← Units.val_mul,
          inv_mul_cancel, Units.val_one, toSquareBlock_one] }
  map_one' := Units.ext (toSquareBlock_one b a)
  map_mul' g h := Units.ext <| BlockTriangular.toSquareBlock_mul
    (mem_blockTriangularGroup_iff.mp g.property) (mem_blockTriangularGroup_iff.mp h.property) a

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
      mem_blockTriangularGroup_iff.mpr <| blockTriangular_reindex_blockDiagonal' fun a => (g a).val

/-- The matrix of `blockDiagonalHom R b g` is the block diagonal matrix with the diagonal blocks
`g a`, reindexed along `Equiv.sigmaFiberEquiv b`. -/
@[simp]
theorem coe_blockDiagonalHom (g : (a : α) → GL {i // b i = a} R) :
    ((blockDiagonalHom R b g : GL m R) : Matrix m m R) =
      reindex (Equiv.sigmaFiberEquiv b) (Equiv.sigmaFiberEquiv b)
        (blockDiagonal' fun a => (g a : Matrix {i // b i = a} {i // b i = a} R)) := by
  rfl

/-- The block diagonal embedding is a section of the diagonal blocks. -/
@[simp]
theorem diagBlocks_blockDiagonalHom (g : (a : α) → GL {i // b i = a} R) :
    diagBlocks R b (blockDiagonalHom R b g) = g := by
  funext a
  ext : 1
  rw [diagBlocks_apply, coe_diagBlock, coe_blockDiagonalHom]
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

/-- The unit diagonal matrix with the entries `N` above the diagonal blocks, as an element of
`GL m R`. -/
noncomputable def blockUnipotentGL (N : {p : m × m // b p.1 < b p.2} → R) : GL m R :=
  ((isUnit_iff_isUnit_det _).mpr
      (blockUnitriangular_unitDiagonalMatrixOfEntries (fun _ h => h) N).isUnit_det :
    IsUnit (unitDiagonalMatrixOfEntries (fun p : m × m => b p.1 < b p.2) N)).unit

/-- The matrix of `blockUnipotentGL N` is the unit diagonal matrix with the entries `N`. -/
@[simp]
theorem coe_blockUnipotentGL (N : {p : m × m // b p.1 < b p.2} → R) :
    (blockUnipotentGL N : Matrix m m R) =
      unitDiagonalMatrixOfEntries (fun p : m × m => b p.1 < b p.2) N := by
  simp [blockUnipotentGL]

variable (R b) in
/-- The unipotent radical, the kernel of `diagBlocks`, is in bijection with the families of
entries at the positions `(i, j)` with `b i < b j`. -/
noncomputable def kerDiagBlocksEquiv :
    (diagBlocks R b).ker ≃ ({p : m × m // b p.1 < b p.2} → R) where
  toFun g p := (((g : blockTriangularGroup R b) : GL m R) : Matrix m m R) p.val.1 p.val.2
  invFun N :=
    ⟨⟨blockUnipotentGL N, by
        simpa using
          (blockUnitriangular_unitDiagonalMatrixOfEntries (fun _ h => h) N).blockTriangular⟩,
      mem_ker_diagBlocks_iff.mpr fun _ _ hij => by
        rw [coe_blockUnipotentGL]
        exact (blockUnitriangular_unitDiagonalMatrixOfEntries (fun _ h => h) N).apply_of_eq hij⟩
  left_inv g := by
    refine Subtype.ext (Subtype.ext (Units.ext (Matrix.ext fun i j => ?_)))
    rw [coe_blockUnipotentGL]
    by_cases h_eq : i = j
    · subst h_eq
      rw [unitDiagonalMatrixOfEntries_apply_self,
        mem_ker_diagBlocks_iff.mp g.property i i rfl, one_apply_eq]
    by_cases h_lt : b i < b j
    · exact unitDiagonalMatrixOfEntries_apply_of_mem _ _ h_eq h_lt
    rw [unitDiagonalMatrixOfEntries_apply_of_notMem _ _ h_eq h_lt]
    rcases (not_lt.mp h_lt).eq_or_lt with h | h
    · rw [mem_ker_diagBlocks_iff.mp g.property i j h.symm, one_apply_ne h_eq]
    · rw [mem_blockTriangularGroup_iff.mp g.val.property h]
  right_inv N := by
    funext p
    exact unitDiagonalMatrixOfEntries_apply_of_mem _ N (ne_of_apply_ne b p.property.ne)
      p.property

/-- `kerDiagBlocksEquiv R b g` is the family of the entries of `g` above the diagonal blocks. -/
@[simp]
theorem kerDiagBlocksEquiv_apply (g : (diagBlocks R b).ker) (p : {p : m × m // b p.1 < b p.2}) :
    kerDiagBlocksEquiv R b g p =
      (((g : blockTriangularGroup R b) : GL m R) : Matrix m m R) p.val.1 p.val.2 := by
  rfl

/-- The element of the unipotent radical with the entries `N` above the diagonal blocks is
`blockUnipotentGL N`. -/
@[simp]
theorem coe_kerDiagBlocksEquiv_symm_apply (N : {p : m × m // b p.1 < b p.2} → R) :
    ((((kerDiagBlocksEquiv R b).symm N : (diagBlocks R b).ker) : blockTriangularGroup R b) :
      GL m R) = blockUnipotentGL N := by
  rfl

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
private def sumBlockZeroEquiv :
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
private def sumBlockSuccEquiv (k : Fin j) :
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

end TauCeti
