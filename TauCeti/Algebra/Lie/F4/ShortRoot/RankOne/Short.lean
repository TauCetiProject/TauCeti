/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence

/-!
# Integral rank-one actions at the short F₄ nodes

At either short node, the twenty-six-dimensional integral module restricts to eight standard
SL₂ blocks, six fixed coordinates, and a four-dimensional conjugation block. The latter is
End(ℤ²) in the ordered basis E₁₂, -E₁₁+E₂₂, -E₁₁, -E₂₁. In particular it is not replaced
by a direct sum of a three-dimensional module and a trivial line: that decomposition would
require dividing by two and would lose the prescribed zero-weight lattice.

The resulting faithful matrix homomorphism matches both numbered root parameters and the
simple coroot over every commutative ring, including rings of characteristic two. The index
`i : Fin 2` denotes zero-based node `i + 2`, that is, Bourbaki nodes 3 and 4.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, Chapter 6.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.

The block assembly follows `TauCeti.MinusculeWeightTable.sl2BlockSL`; the four-dimensional
block retains the two zero-weight vectors of `TauCeti.F4ShortRoot.raisingMatrix`.
-/

public section

open scoped Matrix MatrixGroups

namespace TauCeti.F4ShortRoot

private abbrev ShortBlockIndex := Fin 4 ⊕ ((Fin 2 × Fin 8) ⊕ Fin 6)

private def shortBlockNumber : Fin 2 → ShortBlockIndex → Fin 26
  | 0, .inl a => ![11, 12, 13, 14] a
  | 1, .inl a => ![10, 13, 12, 15] a
  | 0, .inr (.inl (b, a)) =>
      (![![1, 2], ![3, 5], ![4, 6], ![8, 10], ![15, 17], ![19, 21], ![20, 22], ![23, 24]] a) b
  | 1, .inr (.inl (b, a)) =>
      (![![0, 1], ![5, 7], ![6, 9], ![8, 11], ![14, 17], ![16, 19], ![18, 20], ![24, 25]] a) b
  | 0, .inr (.inr a) => ![0, 7, 9, 16, 18, 25] a
  | 1, .inr (.inr a) => ![2, 3, 4, 21, 22, 23] a

private theorem shortBlockNumber_bijective (i : Fin 2) :
    Function.Bijective (shortBlockNumber i) := by
  revert i
  decide +kernel

private noncomputable def shortBlockEquiv (i : Fin 2) : ShortBlockIndex ≃ Fin 26 :=
  Equiv.ofBijective (shortBlockNumber i) (shortBlockNumber_bijective i)

variable {R : Type*} [CommRing R]

-- On arbitrary two-by-two matrices this is X ↦ g X adj(g), so the third diagonal entry
-- is det(g). On SL₂ it is the conjugation action, with that entry equal to one.
private def shortConjugationBlock (g : Matrix (Fin 2) (Fin 2) R) : Matrix (Fin 4) (Fin 4) R :=
  !![g 0 0 ^ 2, 2 * g 0 0 * g 0 1, g 0 0 * g 0 1, g 0 1 ^ 2;
     g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, g 0 1 * g 1 0, g 0 1 * g 1 1;
     0, 0, g 0 0 * g 1 1 - g 0 1 * g 1 0, 0;
     g 1 0 ^ 2, 2 * g 1 0 * g 1 1, g 1 0 * g 1 1, g 1 1 ^ 2]

private def shortBlockMatrixHom :
    Matrix (Fin 2) (Fin 2) R →* Matrix ShortBlockIndex ShortBlockIndex R where
  toFun g := Matrix.fromBlocks (shortConjugationBlock g) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 ↦ g) 0 0 1)
  map_one' := by
    have h : shortConjugationBlock (1 : Matrix (Fin 2) (Fin 2) R) = 1 := by
      ext a b
      fin_cases a <;> fin_cases b <;> simp [shortConjugationBlock]
    simp only [h, ← Pi.one_def, Matrix.blockDiagonal_one, Matrix.fromBlocks_one]
  map_mul' g h := by
    have hc : shortConjugationBlock (g * h) =
        shortConjugationBlock g * shortConjugationBlock h := by
      ext a b
      fin_cases a <;> fin_cases b <;>
        simp [shortConjugationBlock, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring
    simp [hc, Matrix.fromBlocks_multiply, ← Matrix.blockDiagonal_mul]

/-- The integral SL₂ action at the short node `i + 2`, in the original twenty-six-element
weight basis. It includes the four-dimensional conjugation block on the two zero weights. -/
noncomputable def shortRankOneGL (i : Fin 2) : SL(2, R) →* GL (Fin 26) R :=
  ((shortBlockEquiv i).reindexGL R).toMonoidHom.comp
    ((Units.map shortBlockMatrixHom).comp Matrix.SpecialLinearGroup.toGL)

private theorem shortRankOneGL_submatrix (i : Fin 2) (g : SL(2, R)) :
    ((shortRankOneGL i g : GL (Fin 26) R) : Matrix (Fin 26) (Fin 26) R).submatrix
      (shortBlockEquiv i) (shortBlockEquiv i) =
        shortBlockMatrixHom (g : Matrix (Fin 2) (Fin 2) R) := by
  simp [shortRankOneGL, Matrix.submatrix_submatrix]

private def shortLinearBlock (s : Bool) : Matrix ShortBlockIndex ShortBlockIndex ℤ :=
  Matrix.fromBlocks
    (if s then !![0, 2, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]
      else !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 2, 1, 0]) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 ↦
      if s then !![0, 1; 0, 0] else !![0, 0; 1, 0]) 0 0 0)

private def shortQuadraticBlock (s : Bool) : Matrix ShortBlockIndex ShortBlockIndex ℤ :=
  Matrix.fromBlocks (if s then Matrix.single 0 3 1 else Matrix.single 3 0 1) 0 0 0

private theorem rootMatrix_shortBlock (s : Bool) (i : Fin 2) :
    (rootMatrix (if s then .inl (i.natAdd 2) else .inr (i.natAdd 2))).submatrix
      (shortBlockNumber i) (shortBlockNumber i) = shortLinearBlock s := by
  cases s <;> fin_cases i <;> ext a b
  all_goals rcases a with a | (⟨a, j⟩ | a) <;> rcases b with b | (⟨b, k⟩ | b)
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, rootMatrix_inl,
    rootMatrix_inr, Matrix.submatrix_apply, raisingMatrix_apply, loweringMatrix_apply,
    shortBlockNumber, shortLinearBlock, Matrix.fromBlocks, Matrix.blockDiagonal]
  all_goals revert a b; (try revert j); (try revert k); decide +kernel

private theorem rootDividedSquareMatrix_shortBlock (s : Bool) (i : Fin 2) :
    (rootDividedSquareMatrix (if s then .inl (i.natAdd 2) else .inr (i.natAdd 2))).submatrix
      (shortBlockNumber i) (shortBlockNumber i) = shortQuadraticBlock s := by
  cases s <;> fin_cases i <;> ext a b
  all_goals rcases a with a | (⟨a, j⟩ | a) <;> rcases b with b | (⟨b, k⟩ | b)
  all_goals simp only [Bool.false_eq_true, ite_false, ite_true, rootDividedSquareMatrix_inl,
    rootDividedSquareMatrix_inr, Matrix.submatrix_apply, raisingDividedSquareMatrix_apply,
    loweringDividedSquareMatrix_apply, shortBlockNumber, shortQuadraticBlock, Matrix.fromBlocks]
  all_goals revert a b; (try revert j); (try revert k); decide +kernel

private theorem shortBlockMatrixHom_transvection (s : Bool) (t : R) :
    shortBlockMatrixHom
        ((if s then Matrix.SpecialLinearGroup.transvection
            (by decide : (0 : Fin 2) ≠ 1) t
          else Matrix.SpecialLinearGroup.transvection
            (by decide : (1 : Fin 2) ≠ 0) t) : SL(2, R)) =
      1 + t • (shortLinearBlock s).map (Int.cast : ℤ → R) +
        t ^ 2 • (shortQuadraticBlock s).map (Int.cast : ℤ → R) := by
  cases s <;> ext a b
  all_goals rcases a with a | (⟨a, j⟩ | a) <;> rcases b with b | (⟨b, k⟩ | b)
  all_goals simp only [shortBlockMatrixHom, shortConjugationBlock, Fin.isValue,
    Bool.false_eq_true, ite_true, ite_false, Matrix.SpecialLinearGroup.transvection_coe,
    MonoidHom.coe_mk, OneHom.coe_mk, Matrix.add_apply, Matrix.one_apply_eq, one_ne_zero,
    and_true, not_false_eq_true, Matrix.single_apply_of_ne, add_zero, one_pow, mul_one,
    ne_eq, zero_ne_one, Matrix.one_apply_ne, and_self, mul_zero, OfNat.ofNat_ne_zero,
    zero_pow, Matrix.single_apply_same, zero_add, one_mul, and_false, zero_mul, sub_zero,
    Matrix.fromBlocks_apply₁₁, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_fin_one,
    shortLinearBlock, shortQuadraticBlock, Matrix.one_apply, Sum.inl.injEq, Matrix.smul_apply,
    Matrix.map_apply, smul_eq_mul, Matrix.single_apply, Int.cast_ite, Int.cast_one,
    Int.cast_zero, mul_ite, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, reduceCtorEq,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.blockDiagonal_apply,
    Sum.inr.injEq, Prod.ext_iff]
  all_goals fin_cases a <;> fin_cases b <;> simp
  all_goals ring

private theorem shortRankOneGL_transvection (s : Bool) (i : Fin 2) (t : R) :
    shortRankOneGL i (if s then Matrix.SpecialLinearGroup.transvection
        (by decide : (0 : Fin 2) ≠ 1) t
      else Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) =
        (rootSubgroupPoints (if s then .inl (i.natAdd 2) else .inr (i.natAdd 2)) R
          (Multiplicative.ofAdd t) : GL (Fin 26) R) := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (shortBlockEquiv i).surjective a
  obtain ⟨b, rfl⟩ := (shortBlockEquiv i).surjective b
  have hb := congr_fun₂ (shortBlockMatrixHom_transvection (R := R) s t) a b
  have hr := congr_fun₂ (rootMatrix_shortBlock s i) a b
  have hq := congr_fun₂ (rootDividedSquareMatrix_shortBlock s i) a b
  have hg := congr_fun₂ (shortRankOneGL_submatrix i
    (if s then Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t
      else Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t)) a b
  simp only [Matrix.submatrix_apply] at hr hq hg
  rw [hg, hb, coe_rootSubgroupPoints_eq]
  simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, toAdd_ofAdd,
    Matrix.one_apply, smul_eq_mul, shortBlockEquiv, Equiv.ofBijective_apply,
    (shortBlockNumber_bijective i).injective.eq_iff, hr, hq]

/-- The upper transvection is the positive short-root point, with its integral quadratic
coefficient and the same root parameter. -/
@[simp]
theorem shortRankOneGL_upper_transvection (i : Fin 2) (t : R) :
    shortRankOneGL i (Matrix.SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) t) =
        (rootSubgroupPoints (.inl (i.natAdd 2)) R (Multiplicative.ofAdd t) : GL (Fin 26) R) := by
  simpa only [ite_true] using shortRankOneGL_transvection true i t

/-- The lower transvection is the negative short-root point, with the same root parameter. -/
@[simp]
theorem shortRankOneGL_lower_transvection (i : Fin 2) (t : R) :
    shortRankOneGL i (Matrix.SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) t) =
        (rootSubgroupPoints (.inr (i.natAdd 2)) R (Multiplicative.ofAdd t) : GL (Fin 26) R) := by
  simpa only [Bool.false_eq_true, ite_false] using shortRankOneGL_transvection false i t

/-- The short-node SL₂ representation is faithful over every commutative ring, including
characteristic two: any of its eight standard blocks recovers the original matrix. -/
theorem shortRankOneGL_injective (i : Fin 2) :
    Function.Injective (shortRankOneGL i : SL(2, R) → GL (Fin 26) R) := by
  intro g h he
  apply Matrix.SpecialLinearGroup.ext
  intro a b
  have hg := congr_fun₂ (shortRankOneGL_submatrix i g)
    (.inr (.inl (a, 0))) (.inr (.inl (b, 0)))
  have hh := congr_fun₂ (shortRankOneGL_submatrix i h)
    (.inr (.inl (a, 0))) (.inr (.inl (b, 0)))
  rw [he] at hg
  rw [hh] at hg
  simpa [shortBlockMatrixHom, Matrix.blockDiagonal_apply] using hg.symm

private def shortBlockWeight : ShortBlockIndex → ℤ
  | .inl a => ![2, 0, 0, -2] a
  | .inr (.inl (a, _)) => ![1, -1] a
  | .inr (.inr _) => 0

private theorem weight_shortBlock (i : Fin 2) (a : ShortBlockIndex) :
    DynkinType.f4ShortRootWeight (shortBlockNumber i a) (i.natAdd 2) = shortBlockWeight a := by
  revert a i
  decide +kernel

/-- The diagonal of SL₂ maps to the numbered simple-coroot point at the short node. -/
@[simp]
theorem shortRankOneGL_diag2nUnit (i : Fin 2) (u : Rˣ) :
    shortRankOneGL i (Matrix.SpecialLinearGroup.diag2nUnit
      (by decide : (0 : Fin 2) ≠ 1) u) =
        (weightTorusPoints R (Pi.mulSingle (i.natAdd 2) u) : GL (Fin 26) R) := by
  apply Units.ext
  ext a b
  obtain ⟨a, rfl⟩ := (shortBlockEquiv i).surjective a
  obtain ⟨b, rfl⟩ := (shortBlockEquiv i).surjective b
  have hg := congr_fun₂ (shortRankOneGL_submatrix i
    (Matrix.SpecialLinearGroup.diag2nUnit (by decide : (0 : Fin 2) ≠ 1) u)) a b
  simp only [Matrix.submatrix_apply] at hg
  rw [hg, coe_weightTorusPoints, UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe]
  simp only [Matrix.diagonal_apply, (shortBlockEquiv i).injective.eq_iff]
  simp only [shortBlockEquiv, Equiv.ofBijective_apply, torusCharacter_mulSingle,
    weight_shortBlock]
  rcases a with a | (⟨a, j⟩ | a) <;> rcases b with b | (⟨b, k⟩ | b)
  all_goals simp only [Fin.isValue, Matrix.SpecialLinearGroup.diag2nUnit_coe,
    Sum.inl.injEq, Sum.inr.injEq, Prod.mk.injEq]
  all_goals fin_cases a <;> fin_cases b <;>
    simp [shortBlockMatrixHom, shortConjugationBlock, Matrix.diagonal_apply,
      shortBlockWeight, Prod.ext_iff]

end TauCeti.F4ShortRoot
