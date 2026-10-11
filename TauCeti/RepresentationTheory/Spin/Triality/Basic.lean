/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BlockIntertwiners
public import TauCeti.Algebra.Lie.D4.Tripled.VectorBlock
public import TauCeti.RepresentationTheory.Spin.HalfSpin.D4Tripled

/-!
# Concrete intertwiners for type-D4 triality

The tripled type-`D₄` weight table cycles its natural block and its two half-spin blocks. This
file transports that cycle to the standard split vector representation and the exterior
half-spin modules. The alternating sign on the negative vector coordinates is included in the
vector comparison, while the exterior half-spin bases need no further sign changes.

The resulting cycle is
`V(ϖ₁) → V(ϖ₃) → V(ϖ₄) → V(ϖ₁)`. Each equivalence intertwines the positive, negative, and
Cartan Chevalley generators after applying the pinned order-three permutation to the Dynkin node.

## Main declarations

* `TauCeti.D4Tripled.vectorBlockEquiv`: the signed coordinate equivalence from the standard
  vector module to the natural block of the tripled table.
* `SpinPolarizationData.d4VectorToSpinMinusEquiv`,
  `SpinPolarizationData.d4SpinMinusToSpinPlusEquiv`, and
  `SpinPolarizationData.d4SpinPlusToVectorEquiv`: the concrete triality cycle.
* The corresponding `_serreE`, `_serreF`, and `_serreH` theorems: compatibility with all
  Chevalley generators.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate IV.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

/-! ## The signed vector-block equivalence -/

/-- The standard split vector coordinates, identified with the natural block of the tripled
type-`D₄` table. -/
noncomputable def vectorBlockIndexEquiv : (Fin 4 ⊕ Fin 4) ≃ Block 0 :=
  Equiv.ofBijective
    (fun a => ⟨vectorIndex a, d4TripledSummand_vectorIndex a⟩)
    ⟨fun _ _ h => vectorIndex_injective (congrArg Subtype.val h), fun a => by
      have ha : a.1 ∈ Set.range vectorIndex := by
        rw [range_vectorIndex]
        exact a.2
      obtain ⟨x, hx⟩ := ha
      exact ⟨x, Subtype.ext hx⟩⟩

/-- The underlying table coordinate of `vectorBlockIndexEquiv` is `vectorIndex`. -/
@[simp]
theorem coe_vectorBlockIndexEquiv (a : Fin 4 ⊕ Fin 4) :
    (vectorBlockIndexEquiv a).1 = vectorIndex a := by
  exact congrArg Subtype.val (Equiv.ofBijective_apply _ _ a)

private noncomputable def vectorSignEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] (Fin 4 ⊕ Fin 4 → ℚ) where
  toFun v a := vectorBasisSign a * v a
  invFun v a := vectorBasisSign a * v a
  left_inv v := by
    funext a
    dsimp
    rw [← mul_assoc, ← Int.cast_mul, vectorBasisSign_mul_self]
    simp
  right_inv v := by
    funext a
    dsimp
    rw [← mul_assoc, ← Int.cast_mul, vectorBasisSign_mul_self]
    simp
  map_add' x y := by
    funext a
    simp only [Pi.add_apply]
    ring
  map_smul' c x := by
    funext a
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- The standard split vector module, written in the signed coordinates of the natural block of
the tripled type-`D₄` table. -/
noncomputable def vectorBlockEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] (Block 0 → ℚ) :=
  vectorSignEquiv.trans
    (LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) vectorBlockIndexEquiv)

/-- Evaluation of the vector-block equivalence on a standard coordinate. -/
@[simp]
theorem vectorBlockEquiv_apply_apply (v : Fin 4 ⊕ Fin 4 → ℚ)
    (a : Fin 4 ⊕ Fin 4) :
    vectorBlockEquiv v (vectorBlockIndexEquiv a) = vectorBasisSign a * v a := by
  simp [vectorBlockEquiv, vectorSignEquiv]

private theorem cast_typeDStd_raisingMatrix (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b : ℚ) =
      TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i a b := by
  by_cases hi : (i : ℕ) + 1 < 4
  · rw [TypeDStd.raisingMatrix_of_chain 4 (by omega) hi,
      TypeDStd.raisingMatrix_of_chain 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]
  · rw [TypeDStd.raisingMatrix_of_fork 4 (by omega) hi,
      TypeDStd.raisingMatrix_of_fork 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem cast_typeDStd_loweringMatrix (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b : ℚ) =
      TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i a b := by
  by_cases hi : (i : ℕ) + 1 < 4
  · rw [TypeDStd.loweringMatrix_of_chain 4 (by omega) hi,
      TypeDStd.loweringMatrix_of_chain 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]
  · rw [TypeDStd.loweringMatrix_of_fork 4 (by omega) hi,
      TypeDStd.loweringMatrix_of_fork 4 (by omega) hi]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Matrix.fromBlocks, Matrix.single_apply]

private theorem cast_typeDStd_cartanGenerator (i : Fin 4) (a b : Fin 4 ⊕ Fin 4) :
    (((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b : ℚ) =
      ((TypeDStd.cartanGenerator (K := ℚ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℚ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℚ) a b := by
  rw [TypeDStd.val_cartanGenerator, TypeDStd.val_cartanGenerator]
  rcases a with a | a <;> rcases b with b | b <;>
    simp [typeDDiagonalMatrix_apply]

private theorem vectorBlockEquiv_mulVec
    (A : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℚ)
    (B : Matrix (Block 0) (Block 0) ℚ)
    (h : ∀ a b, (vectorBasisSign a : ℚ) * A a b =
      B (vectorBlockIndexEquiv a) (vectorBlockIndexEquiv b) * vectorBasisSign b)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (A *ᵥ v) = B *ᵥ vectorBlockEquiv v := by
  funext a
  obtain ⟨a, rfl⟩ := vectorBlockIndexEquiv.surjective a
  simp only [vectorBlockEquiv_apply_apply, Matrix.mulVec, dotProduct]
  rw [Finset.mul_sum]
  refine Fintype.sum_equiv vectorBlockIndexEquiv (fun b =>
    (vectorBasisSign a : ℚ) * (A a b * v b))
    (fun b => B (vectorBlockIndexEquiv a) b * vectorBlockEquiv v b) ?_
  intro b
  rw [vectorBlockEquiv_apply_apply]
  calc
    (vectorBasisSign a : ℚ) * (A a b * v b) =
        ((vectorBasisSign a : ℚ) * A a b) * v b := by ring
    _ = (B (vectorBlockIndexEquiv a) (vectorBlockIndexEquiv b) *
          (vectorBasisSign b : ℚ)) * v b := by rw [h]
    _ = _ := by ring

/-- The signed vector-block equivalence intertwines every positive simple-root operator with the
raising matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_raising_mulVec (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      blockRaisingMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockRaisingMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (raisingMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  change (raisingMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      (TypeDStd.raisingMatrix (K := ℤ) 4 (by omega) i a b : ℚ) at h
  rw [cast_typeDStd_raisingMatrix] at h
  exact h.symm

/-- The signed vector-block equivalence intertwines every negative simple-root operator with the
lowering matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_lowering_mulVec (i : Fin 4) (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv (TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      blockLoweringMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockLoweringMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (loweringMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  change (loweringMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      (TypeDStd.loweringMatrix (K := ℤ) 4 (by omega) i a b : ℚ) at h
  rw [cast_typeDStd_loweringMatrix] at h
  exact h.symm

/-- The signed vector-block equivalence intertwines every Cartan generator with the diagonal
weight matrix on the natural block. -/
@[simp]
theorem vectorBlockEquiv_cartanGenerator_mulVec (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    vectorBlockEquiv
        (typeDDiagonalMatrix (fun j =>
          (typeDSimpleRoot 4 (by omega) i j : ℚ)) *ᵥ v) =
      blockCartanGeneratorMatrix ℚ 0 i *ᵥ vectorBlockEquiv v := by
  apply vectorBlockEquiv_mulVec
  intro a b
  simp only [blockCartanGeneratorMatrix_apply, coe_vectorBlockIndexEquiv]
  have h := congrArg (Int.castRingHom ℚ) (cartanGeneratorMatrix_vectorIndex i a b)
  simp only [map_mul] at h
  change (cartanGeneratorMatrix i (vectorIndex a) (vectorIndex b) : ℚ) *
      (vectorBasisSign b : ℚ) =
    (vectorBasisSign a : ℚ) *
      ((((TypeDStd.cartanGenerator (K := ℤ) 4 (by omega) i :
        LieAlgebra.Orthogonal.typeD (Fin 4) ℤ) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ) a b : ℚ)) at h
  rw [cast_typeDStd_cartanGenerator] at h
  rw [TypeDStd.val_cartanGenerator] at h
  exact h.symm

end TauCeti.D4Tripled

namespace TauCeti.SpinPolarizationData

open TauCeti.DynkinType

universe u

variable {V : Type u} [AddCommGroup V] [Module ℚ V] {Q : QuadraticForm ℚ V}
  (P : SpinPolarizationData Q) (b : Module.Basis (Fin 4) ℚ P.W)

/-! ## The three concrete blocks -/

private noncomputable def d4BlockZeroToOneIndexEquiv :
    D4Tripled.Block 0 ≃ D4Tripled.Block 1 :=
  (D4Tripled.blockIndexEquiv 0).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (0 : Fin 3) = 1 by decide])

private noncomputable def d4BlockOneToTwoIndexEquiv :
    D4Tripled.Block 1 ≃ D4Tripled.Block 2 :=
  (D4Tripled.blockIndexEquiv 1).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (1 : Fin 3) = 2 by decide])

private noncomputable def d4BlockTwoToZeroIndexEquiv :
    D4Tripled.Block 2 ≃ D4Tripled.Block 0 :=
  (D4Tripled.blockIndexEquiv 2).trans
    (Equiv.subtypeEquivRight fun _ => by
      rw [show finRotate 3 (2 : Fin 3) = 0 by decide])

@[simp] private theorem coe_d4BlockZeroToOneIndexEquiv (a : D4Tripled.Block 0) :
    (d4BlockZeroToOneIndexEquiv a).1 = d4TripledTrialityPerm a.1 := rfl

@[simp] private theorem coe_d4BlockOneToTwoIndexEquiv (a : D4Tripled.Block 1) :
    (d4BlockOneToTwoIndexEquiv a).1 = d4TripledTrialityPerm a.1 := rfl

@[simp] private theorem coe_d4BlockTwoToZeroIndexEquiv (a : D4Tripled.Block 2) :
    (d4BlockTwoToZeroIndexEquiv a).1 = d4TripledTrialityPerm a.1 := rfl

private noncomputable def d4BlockZeroToOneEquiv :
    (D4Tripled.Block 0 → ℚ) ≃ₗ[ℚ] (D4Tripled.Block 1 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockZeroToOneIndexEquiv

private noncomputable def d4BlockOneToTwoEquiv :
    (D4Tripled.Block 1 → ℚ) ≃ₗ[ℚ] (D4Tripled.Block 2 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockOneToTwoIndexEquiv

private noncomputable def d4BlockTwoToZeroEquiv :
    (D4Tripled.Block 2 → ℚ) ≃ₗ[ℚ] (D4Tripled.Block 0 → ℚ) :=
  LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) d4BlockTwoToZeroIndexEquiv

private theorem blockCycleEquiv_mulVec {I J : Type*} [Fintype I] [Fintype J]
    (e : I ≃ J)
    (M : Matrix I I ℚ) (N : Matrix J J ℚ)
    (h : ∀ a b, N (e a) (e b) = M a b) (v : I → ℚ) :
    LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) e (M *ᵥ v) =
      N *ᵥ LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) e v := by
  classical
  funext a
  have hNM : N.submatrix e e = M := by
    ext x y
    exact h x y
  have hs := Matrix.submatrix_mulVec_equiv N v e e
  have ha := congrFun hs (e.symm a)
  have hcoe : LinearEquiv.piCongrLeft' ℚ (fun _ => ℚ) e v = v ∘ e.symm := by
    funext x
    simp
  rw [hcoe]
  simpa only [hNM, LinearEquiv.piCongrLeft'_apply, Function.comp_apply,
    Equiv.apply_symm_apply] using ha

private theorem blockRaisingMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    D4Tripled.blockRaisingMatrix ℚ j i =
      (D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [D4Tripled.blockRaisingMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.raisingMatrixQ_apply, D4Tripled.raisingMatrix_apply,
    D4Tripled.weightTable_weight, D4Tripled.weightTable_reflection]
  split_ifs <;> norm_num

private theorem blockLoweringMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    D4Tripled.blockLoweringMatrix ℚ j i =
      (D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [D4Tripled.blockLoweringMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.loweringMatrixQ_apply, D4Tripled.loweringMatrix_apply,
    D4Tripled.weightTable_weight, D4Tripled.weightTable_reflection]
  split_ifs <;> norm_num

private theorem blockCartanGeneratorMatrix_eq_submatrixQ (j : Fin 3) (i : Fin 4) :
    D4Tripled.blockCartanGeneratorMatrix ℚ j i =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix Subtype.val Subtype.val := by
  ext a b
  simp only [D4Tripled.blockCartanGeneratorMatrix_apply, Matrix.submatrix_apply,
    MinusculeWeightTable.cartanGeneratorMatrixQ_apply,
    D4Tripled.cartanGeneratorMatrix_apply, D4Tripled.weightTable_weight]
  split_ifs <;> norm_num

private theorem d4BlockZeroToOneEquiv_raising_mulVec (i : Fin 4)
    (v : D4Tripled.Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ,
    ← blockRaisingMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockRaisingMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.raisingMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockOneToTwoEquiv_raising_mulVec (i : Fin 4)
    (v : D4Tripled.Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ,
    ← blockRaisingMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockRaisingMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.raisingMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockTwoToZeroEquiv_raising_mulVec (i : Fin 4)
    (v : D4Tripled.Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((D4Tripled.weightTable.raisingMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockRaisingMatrix_eq_submatrixQ,
    ← blockRaisingMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockRaisingMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.raisingMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockZeroToOneEquiv_lowering_mulVec (i : Fin 4)
    (v : D4Tripled.Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockLoweringMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.loweringMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockOneToTwoEquiv_lowering_mulVec (i : Fin 4)
    (v : D4Tripled.Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockLoweringMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.loweringMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockTwoToZeroEquiv_lowering_mulVec (i : Fin 4)
    (v : D4Tripled.Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((D4Tripled.weightTable.loweringMatrixQ i).submatrix Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockLoweringMatrix_eq_submatrixQ, ← blockLoweringMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockLoweringMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.loweringMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockZeroToOneEquiv_cartanGenerator_mulVec (i : Fin 4)
    (v : D4Tripled.Block 0 → ℚ) :
    d4BlockZeroToOneEquiv
        ((D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix
          Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockZeroToOneEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockZeroToOneIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockCartanGeneratorMatrix_apply, coe_d4BlockZeroToOneIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.cartanGeneratorMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockOneToTwoEquiv_cartanGenerator_mulVec (i : Fin 4)
    (v : D4Tripled.Block 1 → ℚ) :
    d4BlockOneToTwoEquiv
        ((D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix
          Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockOneToTwoEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockOneToTwoIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockCartanGeneratorMatrix_apply, coe_d4BlockOneToTwoIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.cartanGeneratorMatrix_trialityPerm i a.1 b.1)

private theorem d4BlockTwoToZeroEquiv_cartanGenerator_mulVec (i : Fin 4)
    (v : D4Tripled.Block 2 → ℚ) :
    d4BlockTwoToZeroEquiv
        ((D4Tripled.weightTable.cartanGeneratorMatrixQ i).submatrix
          Subtype.val Subtype.val *ᵥ v) =
      (D4Tripled.weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ d4BlockTwoToZeroEquiv v := by
  apply blockCycleEquiv_mulVec d4BlockTwoToZeroIndexEquiv
  intro a b
  rw [← blockCartanGeneratorMatrix_eq_submatrixQ,
    ← blockCartanGeneratorMatrix_eq_submatrixQ]
  simp only [D4Tripled.blockCartanGeneratorMatrix_apply, coe_d4BlockTwoToZeroIndexEquiv]
  exact congrArg (Int.castRingHom ℚ)
    (D4Tripled.cartanGeneratorMatrix_trialityPerm i a.1 b.1)

/-! ## The concrete triality cycle -/

/-- Triality from the standard split vector module to the odd half-spin module. -/
noncomputable def d4VectorToSpinMinusEquiv :
    (Fin 4 ⊕ Fin 4 → ℚ) ≃ₗ[ℚ] spinMinus Q P :=
  D4Tripled.vectorBlockEquiv |>.trans
    d4BlockZeroToOneEquiv |>.trans
      (P.d4SpinMinusBlockEquiv b).symm

/-- Triality from the odd half-spin module to the even half-spin module. -/
noncomputable def d4SpinMinusToSpinPlusEquiv :
    spinMinus Q P ≃ₗ[ℚ] spinPlus Q P :=
  P.d4SpinMinusBlockEquiv b |>.trans
    d4BlockOneToTwoEquiv |>.trans
      (P.d4SpinPlusBlockEquiv b).symm

/-- Triality from the even half-spin module to the standard split vector module. -/
noncomputable def d4SpinPlusToVectorEquiv :
    spinPlus Q P ≃ₗ[ℚ] (Fin 4 ⊕ Fin 4 → ℚ) :=
  P.d4SpinPlusBlockEquiv b |>.trans
    d4BlockTwoToZeroEquiv |>.trans
      D4Tripled.vectorBlockEquiv.symm

/-- Three successive concrete triality intertwiners return every vector to itself. -/
@[simp]
theorem d4TrialityCycle_apply_apply_apply (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4SpinPlusToVectorEquiv b
        (P.d4SpinMinusToSpinPlusEquiv b (P.d4VectorToSpinMinusEquiv b v)) = v := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, d4SpinMinusToSpinPlusEquiv,
    d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
  funext a
  simp [d4BlockZeroToOneEquiv, d4BlockOneToTwoEquiv, d4BlockTwoToZeroEquiv,
    d4BlockZeroToOneIndexEquiv, d4BlockOneToTwoIndexEquiv,
    d4BlockTwoToZeroIndexEquiv, LinearEquiv.piCongrLeft'_apply]

/-- The vector-to-odd-spin equivalence intertwines positive generators after applying triality
to the Dynkin node. -/
@[simp]
theorem d4VectorToSpinMinusEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inl (trialityPermD4 i)))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreE]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_raising_mulVec,
    blockRaisingMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_raising_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines positive generators after applying triality to
the Dynkin node. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inl (trialityPermD4 i)))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreE]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreE]
  exact d4BlockOneToTwoEquiv_raising_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines positive generators after applying triality
to the Dynkin node. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreE (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inl i)) x) =
      TypeDStd.raisingMatrix (K := ℚ) 4 (by omega) (trialityPermD4 i) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreE]
  calc
    _ = (D4Tripled.weightTable.raisingMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_raising_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_raising_mulVec]
      simp only [LinearEquiv.apply_symm_apply, blockRaisingMatrix_eq_submatrixQ]

/-- The vector-to-odd-spin equivalence intertwines negative generators after applying triality
to the Dynkin node. -/
@[simp]
theorem d4VectorToSpinMinusEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) i *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inr (trialityPermD4 i)))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreF]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_lowering_mulVec,
    blockLoweringMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_lowering_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines negative generators after applying triality. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.rootGenerator 4 (by omega) (.inr (trialityPermD4 i)))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreF]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreF]
  exact d4BlockOneToTwoEquiv_lowering_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines negative generators after applying triality. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreF (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline
          (TypeDStd.rootGenerator 4 (by omega) (.inr i)) x) =
      TypeDStd.loweringMatrix (K := ℚ) 4 (by omega) (trialityPermD4 i) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreF]
  calc
    _ = (D4Tripled.weightTable.loweringMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_lowering_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_lowering_mulVec]
      simp only [LinearEquiv.apply_symm_apply, blockLoweringMatrix_eq_submatrixQ]

/-- The vector-to-odd-spin equivalence intertwines Cartan generators after applying triality to
the Dynkin node. -/
@[simp]
theorem d4VectorToSpinMinusEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (v : Fin 4 ⊕ Fin 4 → ℚ) :
    P.d4VectorToSpinMinusEquiv b
        (typeDDiagonalMatrix (fun j =>
          (typeDSimpleRoot 4 (by omega) i j : ℚ)) *ᵥ v) =
      P.typeDSpinMinusLieRep b hline
        (TypeDStd.cartanGenerator 4 (by omega) (trialityPermD4 i))
        (P.d4VectorToSpinMinusEquiv b v) := by
  apply (P.d4SpinMinusBlockEquiv b).injective
  rw [P.d4SpinMinusBlockEquiv_serreH]
  simp only [d4VectorToSpinMinusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [D4Tripled.vectorBlockEquiv_cartanGenerator_mulVec,
    blockCartanGeneratorMatrix_eq_submatrixQ,
    d4BlockZeroToOneEquiv_cartanGenerator_mulVec]
  rfl

/-- The odd-to-even-spin equivalence intertwines Cartan generators after applying triality. -/
@[simp]
theorem d4SpinMinusToSpinPlusEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinMinus Q P) :
    P.d4SpinMinusToSpinPlusEquiv b
        (P.typeDSpinMinusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      P.typeDSpinPlusLieRep b hline
        (TypeDStd.cartanGenerator 4 (by omega) (trialityPermD4 i))
        (P.d4SpinMinusToSpinPlusEquiv b x) := by
  apply (P.d4SpinPlusBlockEquiv b).injective
  rw [P.d4SpinPlusBlockEquiv_serreH]
  simp only [d4SpinMinusToSpinPlusEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinMinusBlockEquiv_serreH]
  exact d4BlockOneToTwoEquiv_cartanGenerator_mulVec i (P.d4SpinMinusBlockEquiv b x)

/-- The even-spin-to-vector equivalence intertwines Cartan generators after applying triality. -/
@[simp]
theorem d4SpinPlusToVectorEquiv_serreH (hline : P.line = ⊥) (i : Fin 4)
    (x : spinPlus Q P) :
    P.d4SpinPlusToVectorEquiv b
        (P.typeDSpinPlusLieRep b hline (TypeDStd.cartanGenerator 4 (by omega) i) x) =
      typeDDiagonalMatrix (fun j =>
        (typeDSimpleRoot 4 (by omega) (trialityPermD4 i) j : ℚ)) *ᵥ
        P.d4SpinPlusToVectorEquiv b x := by
  apply D4Tripled.vectorBlockEquiv.injective
  simp only [d4SpinPlusToVectorEquiv, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  rw [P.d4SpinPlusBlockEquiv_serreH]
  calc
    _ = (D4Tripled.weightTable.cartanGeneratorMatrixQ (trialityPermD4 i)).submatrix
          Subtype.val Subtype.val *ᵥ
        d4BlockTwoToZeroEquiv (P.d4SpinPlusBlockEquiv b x) :=
      d4BlockTwoToZeroEquiv_cartanGenerator_mulVec i (P.d4SpinPlusBlockEquiv b x)
    _ = _ := by
      rw [D4Tripled.vectorBlockEquiv_cartanGenerator_mulVec]
      simp only [LinearEquiv.apply_symm_apply,
        blockCartanGeneratorMatrix_eq_submatrixQ]

end TauCeti.SpinPolarizationData
