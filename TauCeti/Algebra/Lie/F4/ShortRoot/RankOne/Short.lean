/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.F4.ShortRoot.Carrier
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Elementary
public import TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.Diagonal.Basic

/-!
# Rank-one integration at the short nodes of the F₄ short-root module

The two short simple roots act on the twenty-six-dimensional integral module by eight
standard two-dimensional blocks, six fixed vectors, and a four-dimensional conjugation
block. In the latter block the ordered basis is
`E₀₁, diag(-1,1), E₁₁, -E₁₀`. In particular its zero-weight lattice is not split into a
trivial summand and an adjoint summand by dividing by two.

`shortRankOneGL` integrates these actions over every commutative ring, including
characteristic two. Its upper and lower unipotents have exactly the parameters of the
numbered root subgroups, and its diagonal is the numbered simple coroot. The index
`i : Fin 2` denotes `i.natAdd 2 : Fin 4`, namely Bourbaki nodes three and four.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, §12.
* R. W. Carter, *Simple Groups of Lie Type*, §5.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate VIII.
-/

public section

open scoped Matrix MatrixGroups
open Matrix

namespace TauCeti.F4ShortRoot

universe v

variable (A : Type v) [CommRing A]

private abbrev BlockIndex := Fin 4 ⊕ ((Fin 2 × Fin 8) ⊕ Fin 6)

private def blockIndex (i : Fin 2) : BlockIndex → Fin 26 :=
  Sum.elim
    (![![11, 12, 13, 14], ![10, 13, 12, 15]] i)
    (Sum.elim
      (fun p => (![![![1, 3, 4, 8, 15, 19, 20, 23], ![2, 5, 6, 10, 17, 21, 22, 24]],
        ![![0, 5, 6, 8, 14, 16, 18, 24], ![1, 7, 9, 11, 17, 19, 20, 25]]] i p.1 p.2))
      (![![0, 7, 9, 16, 18, 25], ![2, 3, 4, 21, 22, 23]] i))

private noncomputable def blockEquiv (i : Fin 2) : BlockIndex ≃ Fin 26 :=
  Equiv.ofBijective (blockIndex i) (by fin_cases i <;> decide)

-- This is conjugation on the four-dimensional matrix lattice in the basis above.
-- Keeping the determinant in the third row makes multiplicativity a polynomial identity.
private def conjugationBlock (g : Matrix (Fin 2) (Fin 2) A) : Matrix (Fin 4) (Fin 4) A :=
  !![g 0 0 ^ 2, 2 * g 0 0 * g 0 1, g 0 0 * g 0 1, g 0 1 ^ 2;
     g 0 0 * g 1 0, g 0 0 * g 1 1 + g 0 1 * g 1 0, g 0 1 * g 1 0, g 0 1 * g 1 1;
     0, 0, g 0 0 * g 1 1 - g 0 1 * g 1 0, 0;
     g 1 0 ^ 2, 2 * g 1 0 * g 1 1, g 1 0 * g 1 1, g 1 1 ^ 2]

private def conjugationBlockHom : Matrix (Fin 2) (Fin 2) A →* Matrix (Fin 4) (Fin 4) A where
  toFun := conjugationBlock A
  map_one' := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [conjugationBlock]
  map_mul' g h := by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [conjugationBlock, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

private def standardBlocksHom :
    Matrix (Fin 2) (Fin 2) A →* Matrix (Fin 2 × Fin 8) (Fin 2 × Fin 8) A :=
  (Matrix.blockDiagonalRingHom (Fin 2) (Fin 8) A).toMonoidHom.comp
    (MonoidHom.pi fun _ => MonoidHom.id _)

private def blockGL : SL(2, A) →* GL BlockIndex A :=
  fromBlocksGL.comp <|
    ((conjugationBlockHom A).comp SpecialLinearGroup.coeMonoidHom).toHomUnits.prod
      (fromBlocksGL.comp <|
        (((standardBlocksHom A).comp SpecialLinearGroup.coeMonoidHom).toHomUnits.prod
          (1 : SL(2, A) →* GL (Fin 6) A)))

/-- The faithful rank-one matrix action at either short simple node of the F₄ module. -/
noncomputable def shortRankOneGL (i : Fin 2) : SL(2, A) →* GL (Fin 26) A :=
  (Matrix.GeneralLinearGroup.reindex A (blockEquiv i)).toMonoidHom.comp (blockGL A)

private theorem shortRankOneGL_block (i : Fin 2) (g : SL(2, A)) :
    (shortRankOneGL A i g : Matrix (Fin 26) (Fin 26) A).submatrix
        (blockIndex i) (blockIndex i) =
      Matrix.fromBlocks (conjugationBlock A g) 0 0
        (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 => (g : Matrix (Fin 2) (Fin 2) A))
          0 0 1) := by
  ext a b
  simp [Matrix.submatrix_apply, shortRankOneGL, blockGL, Matrix.GeneralLinearGroup.reindex_apply,
    Matrix.coe_reindexRingEquiv, Matrix.reindex_apply,
    blockEquiv, conjugationBlockHom, standardBlocksHom, MonoidHom.pi]

/-- The rank-one action is faithful over every commutative coefficient ring. -/
theorem shortRankOneGL_injective (i : Fin 2) : Function.Injective (shortRankOneGL A i) := by
  intro g h heq
  apply SpecialLinearGroup.ext g h
  intro a b
  have hh := congrArg
    (fun m : GL (Fin 26) A => (m : Matrix (Fin 26) (Fin 26) A).submatrix
      (blockIndex i) (blockIndex i)) heq
  rw [shortRankOneGL_block, shortRankOneGL_block] at hh
  simpa only [Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₁₁,
    Matrix.blockDiagonal_apply, ↓reduceIte] using
    congrFun (congrFun hh (.inr (.inl (a, 0)))) (.inr (.inl (b, 0)))

private def rootBlock (positive : Bool) : Matrix BlockIndex BlockIndex ℤ :=
  Matrix.fromBlocks
    (if positive then !![0, 2, 1, 0; 0, 0, 0, 1; 0, 0, 0, 0; 0, 0, 0, 0]
      else !![0, 0, 0, 0; 1, 0, 0, 0; 0, 0, 0, 0; 0, 2, 1, 0]) 0 0
    (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 =>
      if positive then !![0, 1; 0, 0] else !![0, 0; 1, 0]) 0 0 0)

private def dividedSquareBlock (positive : Bool) : Matrix BlockIndex BlockIndex ℤ :=
  Matrix.fromBlocks (if positive then Matrix.single 0 3 1 else Matrix.single 3 0 1) 0 0 0

-- Reduce the block constructors to computable entry functions before kernel-checked
-- finite comparison. This avoids elaborating a separate goal for each of the 26² entries.
private theorem rootMatrix_block (i : Fin 2) (positive : Bool) :
    (rootMatrix (if positive then .inl (i.natAdd 2) else .inr (i.natAdd 2))).submatrix
      (blockIndex i) (blockIndex i) = rootBlock positive := by
  cases positive <;> rw [← Matrix.ext_iff]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, Matrix.submatrix_apply,
    rootMatrix_inl, rootMatrix_inr, raisingMatrix_apply, loweringMatrix_apply]
  all_goals dsimp [rootBlock, Matrix.fromBlocks, Matrix.blockDiagonal]
  all_goals fin_cases i <;> decide

private theorem rootDividedSquareMatrix_block (i : Fin 2) (positive : Bool) :
    (rootDividedSquareMatrix
      (if positive then .inl (i.natAdd 2) else .inr (i.natAdd 2))).submatrix
        (blockIndex i) (blockIndex i) = dividedSquareBlock positive := by
  cases positive <;> rw [← Matrix.ext_iff]
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, Matrix.submatrix_apply,
    rootDividedSquareMatrix_inl, rootDividedSquareMatrix_inr,
    raisingDividedSquareMatrix_apply, loweringDividedSquareMatrix_apply]
  all_goals dsimp [dividedSquareBlock, Matrix.fromBlocks, Matrix.single]
  all_goals fin_cases i <;> decide

private theorem block_transvection (positive : Bool) (t : A) :
    let g : SL(2, A) := if positive then
      SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t else
      SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t
    Matrix.fromBlocks (conjugationBlock A g) 0 0
      (Matrix.fromBlocks (Matrix.blockDiagonal fun _ : Fin 8 => (g : Matrix (Fin 2) (Fin 2) A))
        0 0 1) = 1 + t • (rootBlock positive).map (Int.cast : ℤ → A) +
          t ^ 2 • (dividedSquareBlock positive).map (Int.cast : ℤ → A) := by
  dsimp only
  ext a b
  cases positive <;> rcases a with a | (⟨a, c⟩ | a) <;>
    rcases b with b | (⟨b, d⟩ | b)
  all_goals simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, rootBlock, dividedSquareBlock,
    Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.zero_apply,
    Bool.false_eq_true, ↓reduceIte]
  all_goals fin_cases a <;> fin_cases b <;>
    simp [conjugationBlock, SpecialLinearGroup.transvection_coe,
      Matrix.blockDiagonal_apply, Matrix.one_apply, mul_comm]

private theorem shortRankOneGL_transvection (i : Fin 2) (positive : Bool) (t : A) :
    shortRankOneGL A i (if positive then
      SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) t else
      SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) t) =
      (rootSubgroupPoints (if positive then .inl (i.natAdd 2) else .inr (i.natAdd 2))
        A (Multiplicative.ofAdd t) : GL (Fin 26) A) := by
  apply Units.ext
  apply Matrix.submatrix_injective (r := blockIndex i) (c := blockIndex i)
    (blockEquiv i).surjective (blockEquiv i).surjective
  dsimp only
  rw [shortRankOneGL_block, coe_rootSubgroupPoints_eq]
  have hinj : Function.Injective (blockIndex i) := (blockEquiv i).injective
  simp only [Matrix.submatrix_add, Pi.add_apply, Matrix.submatrix_smul, Pi.smul_apply,
    Matrix.submatrix_one _ hinj, Matrix.submatrix_map,
    rootMatrix_block, rootDividedSquareMatrix_block, toAdd_ofAdd]
  exact block_transvection A positive t

/-- The upper transvection has the numbered positive short-root parameter. -/
@[simp]
theorem shortRankOneGL_upper_transvection (i : Fin 2) (t : A) :
    shortRankOneGL A i (SpecialLinearGroup.transvection
      (by decide : (0 : Fin 2) ≠ 1) t) =
      (rootSubgroupPoints (.inl (i.natAdd 2)) A (Multiplicative.ofAdd t) : GL (Fin 26) A) := by
  exact shortRankOneGL_transvection A i true t

/-- The lower transvection has the numbered negative short-root parameter. -/
@[simp]
theorem shortRankOneGL_lower_transvection (i : Fin 2) (t : A) :
    shortRankOneGL A i (SpecialLinearGroup.transvection
      (by decide : (1 : Fin 2) ≠ 0) t) =
      (rootSubgroupPoints (.inr (i.natAdd 2)) A (Multiplicative.ofAdd t) : GL (Fin 26) A) := by
  exact shortRankOneGL_transvection A i false t

private def blockWeight : BlockIndex → ℤ :=
  Sum.elim ![2, 0, 0, -2] (Sum.elim (fun p => if p.1 = 0 then 1 else -1) (fun _ => 0))

private theorem weight_block (i : Fin 2) :
    ∀ a, DynkinType.f4ShortRootWeight (blockIndex i a) (i.natAdd 2) = blockWeight a := by
  fin_cases i <;> decide

/-- The diagonal of the rank-one group is the numbered simple coroot. -/
@[simp]
theorem shortRankOneGL_diag2nUnit (i : Fin 2) (u : Aˣ) :
    shortRankOneGL A i (SpecialLinearGroup.diag2nUnit
      (by decide : (0 : Fin 2) ≠ 1) u) =
      (weightTorusPoints A (Pi.mulSingle (i.natAdd 2) u) : GL (Fin 26) A) := by
  apply Units.ext
  apply Matrix.submatrix_injective (r := blockIndex i) (c := blockIndex i)
    (blockEquiv i).surjective (blockEquiv i).surjective
  dsimp only
  rw [shortRankOneGL_block]
  ext a b
  simp only [Matrix.submatrix_apply, coe_weightTorusPoints,
    UniversalEnvelopingAlgebra.kostantTorusMatrix_apply, diagGL_coe,
    Matrix.diagonal_apply, torusCharacter_mulSingle, weight_block]
  have hinj : Function.Injective (blockIndex i) := (blockEquiv i).injective
  simp only [hinj.eq_iff]
  rcases a with a | (⟨a, c⟩ | a) <;> rcases b with b | (⟨b, d⟩ | b)
  all_goals fin_cases a <;> fin_cases b <;>
    simp [conjugationBlock, SpecialLinearGroup.diag2nUnit_coe, blockWeight,
      Matrix.diagonal_apply]

end TauCeti.F4ShortRoot
