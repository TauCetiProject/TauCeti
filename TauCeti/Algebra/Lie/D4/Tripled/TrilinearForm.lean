/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.D4.Tripled.BlockIntertwiners

/-!
# The trilinear form on the three D4 triality blocks

The natural and two half-spin representations of type `D₄` carry a distinguished trilinear
form. This file constructs an integral normalization of that form on the three coordinate blocks
of the tripled minuscule weight table. Its coefficients are `0`, `1`, and `-1`.

The coefficient table is cyclic under the order-three permutation of the blocks. The resulting
iterated linear map is invariant under the diagonal action of every positive, negative, and
Cartan Chevalley generator. Because the coefficients are integral, the form and its invariance
are stated over an arbitrary commutative ring.

## Main declarations

* `TauCeti.D4Tripled.trialityCoefficient`: the signed integral coefficient of three basis
  vectors.
* `TauCeti.D4Tripled.trialityCoefficient_apply`: computation through the signed lookup table.
* `TauCeti.D4Tripled.trialityCoefficient_cyclic`: cyclic compatibility with triality.
* `TauCeti.D4Tripled.trialityTrilinearForm`: the bundled trilinear form over a commutative ring.
* `TauCeti.D4Tripled.trialityTrilinearForm_apply`: evaluation on arbitrary coordinate vectors.
* `TauCeti.D4Tripled.trialityTrilinearForm_ne_zero`: nonvanishing over a nontrivial ring.
* `TauCeti.D4Tripled.trialityTrilinearForm_cyclic`: cyclic compatibility of the bundled form.
* `TauCeti.D4Tripled.trialityTrilinearForm_raising_invariant` and its lowering and Cartan
  analogues: invariance under the diagonal Chevalley-generator action.

## References

* J. F. Adams, *Lectures on Exceptional Lie Groups*, Chapter 3.
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Lecture 20.
-/

open scoped Matrix

public section

namespace TauCeti.D4Tripled

open TauCeti.DynkinType

/-- The signed integral coefficient of three basis vectors in the natural, odd half-spin, and
even half-spin blocks. The absolute value stored in the table selects the third basis vector;
its sign is the coefficient. -/
def trialityCoefficient (a : Block 0) (b : Block 1) (c : Block 2) : ℤ :=
  let table : Fin 8 → Fin 8 → ℤ := ![
    ![0, 0, 0, -8, 0, 7, -6, 4],
    ![0, 0, 8, 0, -7, 0, 5, -3],
    ![0, -8, 0, 0, 6, -5, 0, 2],
    ![8, 0, 0, 0, -4, 3, -2, 0],
    ![0, 7, -6, 5, 0, 0, 0, -1],
    ![-7, 0, 4, -3, 0, 0, 1, 0],
    ![6, -4, 0, 2, 0, -1, 0, 0],
    ![-5, 3, -2, 0, 1, 0, 0, 0]]
  let localIndex {j : Fin 3} (x : Block j) : Fin 8 :=
    ⟨x.1.val % 8, Nat.mod_lt _ (by omega)⟩
  let q := table (localIndex a) (localIndex b)
  if q.natAbs = (localIndex c).val + 1 then q.sign else 0

/-- Compute a coefficient from the signed lookup table and the local indices of the three
coordinate blocks. -/
theorem trialityCoefficient_apply (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityCoefficient a b c =
      let table : Fin 8 → Fin 8 → ℤ := ![
        ![0, 0, 0, -8, 0, 7, -6, 4],
        ![0, 0, 8, 0, -7, 0, 5, -3],
        ![0, -8, 0, 0, 6, -5, 0, 2],
        ![8, 0, 0, 0, -4, 3, -2, 0],
        ![0, 7, -6, 5, 0, 0, 0, -1],
        ![-7, 0, 4, -3, 0, 0, 1, 0],
        ![6, -4, 0, 2, 0, -1, 0, 0],
        ![-5, 3, -2, 0, 1, 0, 0, 0]]
      let localIndex {j : Fin 3} (x : Block j) : Fin 8 :=
        ⟨x.1.val % 8, Nat.mod_lt _ (by omega)⟩
      let q := table (localIndex a) (localIndex b)
      if q.natAbs = (localIndex c).val + 1 then q.sign else 0 := by
  rfl

/-- The chosen integral normalization has a coefficient equal to `-1`; in particular, the form
constructed below is nonzero over every nontrivial ring. -/
@[simp]
theorem trialityCoefficient_normalization :
    trialityCoefficient ⟨0, by decide⟩ ⟨11, by decide⟩ ⟨23, by decide⟩ = -1 := by
  decide

/-- The coefficient table is preserved when triality rotates the three blocks. -/
theorem trialityCoefficient_cyclic (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityCoefficient a b c =
      trialityCoefficient (d4BlockTwoToZeroIndexEquiv c)
        (d4BlockZeroToOneIndexEquiv a) (d4BlockOneToTwoIndexEquiv b) := by
  have h : trialityCoefficient a b c =
      trialityCoefficient (blockIndexEquiv 2 c)
        (blockIndexEquiv 0 a) (blockIndexEquiv 1 b) := by
    revert a b c
    decide +kernel
  have h₂₀ : d4BlockTwoToZeroIndexEquiv c = blockIndexEquiv 2 c := by
    apply Subtype.ext
    simp
  have h₀₁ : d4BlockZeroToOneIndexEquiv a = blockIndexEquiv 0 a := by
    apply Subtype.ext
    simp
  have h₁₂ : d4BlockOneToTwoIndexEquiv b = blockIndexEquiv 1 b := by
    apply Subtype.ext
    simp
  simpa only [h₂₀, h₀₁, h₁₂] using h

private theorem trialityCoefficient_raising (i : Fin 4) (a : Block 0) (b : Block 1)
    (c : Block 2) :
    (∑ x, blockRaisingMatrix ℤ 0 i x a * trialityCoefficient x b c) +
      (∑ y, blockRaisingMatrix ℤ 1 i y b * trialityCoefficient a y c) +
        ∑ z, blockRaisingMatrix ℤ 2 i z c * trialityCoefficient a b z = 0 := by
  simp only [blockRaisingMatrix_apply, raisingMatrix_apply]
  revert i a b c
  decide +kernel

private theorem trialityCoefficient_lowering (i : Fin 4) (a : Block 0) (b : Block 1)
    (c : Block 2) :
    (∑ x, blockLoweringMatrix ℤ 0 i x a * trialityCoefficient x b c) +
      (∑ y, blockLoweringMatrix ℤ 1 i y b * trialityCoefficient a y c) +
        ∑ z, blockLoweringMatrix ℤ 2 i z c * trialityCoefficient a b z = 0 := by
  simp only [blockLoweringMatrix_apply, loweringMatrix_apply]
  revert i a b c
  decide +kernel

private theorem trialityCoefficient_cartan (i : Fin 4) (a : Block 0) (b : Block 1)
    (c : Block 2) :
    (∑ x, blockCartanGeneratorMatrix ℤ 0 i x a * trialityCoefficient x b c) +
      (∑ y, blockCartanGeneratorMatrix ℤ 1 i y b * trialityCoefficient a y c) +
        ∑ z, blockCartanGeneratorMatrix ℤ 2 i z c * trialityCoefficient a b z = 0 := by
  simp only [blockCartanGeneratorMatrix_apply, cartanGeneratorMatrix_apply]
  revert i a b c
  decide +kernel

/-- The integral triality form, extended to the coordinate blocks over a commutative ring. -/
noncomputable def trialityTrilinearForm (R : Type*) [CommRing R] :
    (Block 0 → R) →ₗ[R] (Block 1 → R) →ₗ[R] (Block 2 → R) →ₗ[R] R :=
  ∑ a, ∑ b, ∑ c,
    ((Pi.basisFun R (Block 0)).coord a).smulRight
      ((trialityCoefficient a b c : R) •
        (LinearMap.mul R R).compl₁₂
          ((Pi.basisFun R (Block 1)).coord b)
          ((Pi.basisFun R (Block 2)).coord c))

/-- The triality form is the sum of its signed coordinate monomials. -/
theorem trialityTrilinearForm_apply (R : Type*) [CommRing R]
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R v₀ v₁ v₂ =
      ∑ a, ∑ b, ∑ c, (trialityCoefficient a b c : R) * v₀ a * v₁ b * v₂ c := by
  classical
  simp [trialityTrilinearForm, mul_assoc, mul_comm, mul_left_comm]

/-- The triality form on three single-coordinate vectors is its signed integral coefficient. -/
@[simp]
theorem trialityTrilinearForm_single_one_single_one_single_one (R : Type*) [CommRing R]
    (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityTrilinearForm R (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) =
      (trialityCoefficient a b c : R) := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

/-- The triality trilinear form is nonzero over every nontrivial commutative ring. -/
theorem trialityTrilinearForm_ne_zero (R : Type*) [CommRing R] [Nontrivial R] :
    trialityTrilinearForm R ≠ 0 := by
  intro h
  have hEval := congrArg
    (fun f => f (Pi.single ⟨0, by decide⟩ 1) (Pi.single ⟨11, by decide⟩ 1)
      (Pi.single ⟨23, by decide⟩ 1)) h
  simp at hEval

private theorem trialityTrilinearForm_apply_single_one_single_one (R : Type*) [CommRing R]
    (v : Block 0 → R) (b : Block 1) (c : Block 2) :
    trialityTrilinearForm R v (Pi.single b 1) (Pi.single c 1) =
      ∑ a, v a * (trialityCoefficient a b c : R) := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private theorem trialityTrilinearForm_single_one_apply_single_one (R : Type*) [CommRing R]
    (a : Block 0) (v : Block 1 → R) (c : Block 2) :
    trialityTrilinearForm R (Pi.single a 1) v (Pi.single c 1) =
      ∑ b, (trialityCoefficient a b c : R) * v b := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private theorem trialityTrilinearForm_single_one_single_one_apply (R : Type*) [CommRing R]
    (a : Block 0) (b : Block 1) (v : Block 2 → R) :
    trialityTrilinearForm R (Pi.single a 1) (Pi.single b 1) v =
      ∑ c, (trialityCoefficient a b c : R) * v c := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

/-- The triality form is preserved when triality cyclically rotates its three coordinate blocks. -/
theorem trialityTrilinearForm_cyclic (R : Type*) [CommRing R]
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R v₀ v₁ v₂ =
      trialityTrilinearForm R
        (LinearEquiv.piCongrLeft' R (fun _ => R) d4BlockTwoToZeroIndexEquiv v₂)
        (LinearEquiv.piCongrLeft' R (fun _ => R) d4BlockZeroToOneIndexEquiv v₀)
        (LinearEquiv.piCongrLeft' R (fun _ => R) d4BlockOneToTwoIndexEquiv v₁) := by
  classical
  rw [trialityTrilinearForm_apply, trialityTrilinearForm_apply]
  let e : ((Block 0 × Block 1) × Block 2) ≃ ((Block 0 × Block 1) × Block 2) :=
    { toFun := fun x =>
        ((d4BlockTwoToZeroIndexEquiv x.2, d4BlockZeroToOneIndexEquiv x.1.1),
          d4BlockOneToTwoIndexEquiv x.1.2)
      invFun := fun x =>
        ((d4BlockZeroToOneIndexEquiv.symm x.1.2, d4BlockOneToTwoIndexEquiv.symm x.2),
          d4BlockTwoToZeroIndexEquiv.symm x.1.1)
      left_inv := by intro x; simp
      right_inv := by intro x; simp }
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type',
    ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  apply Fintype.sum_equiv e
  rintro ⟨⟨a, b⟩, c⟩
  rw [trialityCoefficient_cyclic]
  have he : e ((a, b), c) =
      ((d4BlockTwoToZeroIndexEquiv c, d4BlockZeroToOneIndexEquiv a),
        d4BlockOneToTwoIndexEquiv b) := rfl
  rw [he]
  simp only [LinearEquiv.piCongrLeft'_apply, Equiv.symm_apply_apply]
  ring

private theorem trialityTrilinearForm_invariant_of_coefficients
    (R : Type*) [CommRing R]
    (M₀ : Matrix (Block 0) (Block 0) R)
    (M₁ : Matrix (Block 1) (Block 1) R)
    (M₂ : Matrix (Block 2) (Block 2) R)
    (h : ∀ a b c,
      (∑ x, M₀ x a * (trialityCoefficient x b c : R)) +
        (∑ y, (trialityCoefficient a y c : R) * M₁ y b) +
          ∑ z, (trialityCoefficient a b z : R) * M₂ z c = 0) :
    (trialityTrilinearForm R).comp M₀.mulVecLin +
        (LinearMap.lcomp R ((Block 2 → R) →ₗ[R] R) M₁.mulVecLin).comp
          (trialityTrilinearForm R) +
      (LinearMap.compRight R (LinearMap.lcomp R R M₂.mulVecLin)).comp
        (trialityTrilinearForm R) = 0 := by
  apply (Pi.basisFun R (Block 0)).ext
  intro a
  apply (Pi.basisFun R (Block 1)).ext
  intro b
  apply (Pi.basisFun R (Block 2)).ext
  intro c
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.lcomp_apply,
    LinearMap.compRight_apply, Pi.basisFun_apply, LinearMap.zero_apply,
    Matrix.mulVecLin_apply, trialityTrilinearForm_apply_single_one_single_one,
    trialityTrilinearForm_single_one_apply_single_one,
    trialityTrilinearForm_single_one_single_one_apply, Matrix.mulVec,
    dotProduct_single, mul_one] using h a b c

private theorem trialityTrilinearForm_invariant_of_integer_coefficients
    (R : Type*) [CommRing R]
    (M₀ : Matrix (Block 0) (Block 0) ℤ)
    (M₁ : Matrix (Block 1) (Block 1) ℤ)
    (M₂ : Matrix (Block 2) (Block 2) ℤ)
    (h : ∀ a b c,
      (∑ x, M₀ x a * trialityCoefficient x b c) +
        (∑ y, M₁ y b * trialityCoefficient a y c) +
          ∑ z, M₂ z c * trialityCoefficient a b z = 0)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R ((M₀.map (Int.castRingHom R)) *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ ((M₁.map (Int.castRingHom R)) *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ ((M₂.map (Int.castRingHom R)) *ᵥ v₂) = 0 := by
  have hMap := trialityTrilinearForm_invariant_of_coefficients R
    (M₀.map (Int.castRingHom R)) (M₁.map (Int.castRingHom R))
    (M₂.map (Int.castRingHom R)) (fun a b c => by
      rw [← map_zero (Int.castRingHom R)]
      simpa only [Matrix.map_apply, map_add, map_sum, map_mul, Int.coe_castRingHom,
        mul_comm] using
        congrArg (Int.castRingHom R) (h a b c))
  have hApply := congrArg (fun T => T v₀ v₁ v₂) hMap
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.lcomp_apply,
    LinearMap.compRight_apply, LinearMap.zero_apply, Matrix.mulVecLin_apply] using hApply

private theorem map_blockRaisingMatrix (R : Type*) [CommRing R]
    (j : Fin 3) (i : Fin 4) :
    (blockRaisingMatrix ℤ j i).map (Int.castRingHom R) = blockRaisingMatrix R j i := by
  ext a b
  simp

private theorem map_blockLoweringMatrix (R : Type*) [CommRing R]
    (j : Fin 3) (i : Fin 4) :
    (blockLoweringMatrix ℤ j i).map (Int.castRingHom R) = blockLoweringMatrix R j i := by
  ext a b
  simp

private theorem map_blockCartanGeneratorMatrix (R : Type*) [CommRing R]
    (j : Fin 3) (i : Fin 4) :
    (blockCartanGeneratorMatrix ℤ j i).map (Int.castRingHom R) =
      blockCartanGeneratorMatrix R j i := by
  ext a b
  simp

/-- The triality form is invariant under the diagonal action of a positive Chevalley generator. -/
theorem trialityTrilinearForm_raising_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockRaisingMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockRaisingMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockRaisingMatrix R 2 i *ᵥ v₂) = 0 := by
  simpa only [map_blockRaisingMatrix] using
    trialityTrilinearForm_invariant_of_integer_coefficients R
      (blockRaisingMatrix ℤ 0 i) (blockRaisingMatrix ℤ 1 i) (blockRaisingMatrix ℤ 2 i)
      (trialityCoefficient_raising i) v₀ v₁ v₂

/-- The triality form is invariant under the diagonal action of a negative Chevalley generator. -/
theorem trialityTrilinearForm_lowering_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockLoweringMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockLoweringMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockLoweringMatrix R 2 i *ᵥ v₂) = 0 := by
  simpa only [map_blockLoweringMatrix] using
    trialityTrilinearForm_invariant_of_integer_coefficients R
      (blockLoweringMatrix ℤ 0 i) (blockLoweringMatrix ℤ 1 i) (blockLoweringMatrix ℤ 2 i)
      (trialityCoefficient_lowering i) v₀ v₁ v₂

/-- The triality form is invariant under the diagonal action of a Cartan Chevalley generator. -/
theorem trialityTrilinearForm_cartan_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockCartanGeneratorMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockCartanGeneratorMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockCartanGeneratorMatrix R 2 i *ᵥ v₂) = 0 := by
  simpa only [map_blockCartanGeneratorMatrix] using
    trialityTrilinearForm_invariant_of_integer_coefficients R
      (blockCartanGeneratorMatrix ℤ 0 i) (blockCartanGeneratorMatrix ℤ 1 i)
      (blockCartanGeneratorMatrix ℤ 2 i) (trialityCoefficient_cartan i) v₀ v₁ v₂

end TauCeti.D4Tripled
