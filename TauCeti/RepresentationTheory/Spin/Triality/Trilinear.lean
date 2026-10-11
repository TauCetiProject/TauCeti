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
Cartan Chevalley generator. Thus the construction works after base change to any commutative ring.

## Main declarations

* `TauCeti.D4Tripled.trialityCoefficient`: the signed integral coefficient of three basis
  vectors.
* `TauCeti.D4Tripled.trialityCoefficient_cyclic`: cyclic compatibility with triality.
* `TauCeti.D4Tripled.trialityTrilinearForm`: the bundled trilinear form over a commutative ring.
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
@[expose]
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

/-- The chosen integral normalization has a coefficient equal to `-1`; in particular, the form
constructed below is nonzero over every nontrivial ring. -/
@[simp]
theorem trialityCoefficient_normalization :
    trialityCoefficient ⟨0, by decide⟩ ⟨11, by decide⟩ ⟨23, by decide⟩ = -1 := by
  decide

/-- The coefficient table is preserved when triality rotates the three blocks. -/
theorem trialityCoefficient_cyclic (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityCoefficient a b c =
      trialityCoefficient
        ⟨d4TripledTrialityPerm c.1, by
          simpa using
            (d4TripledSummand_d4TripledTrialityPerm_eq_iff c.1 (2 : Fin 3)).2 c.2⟩
        ⟨d4TripledTrialityPerm a.1, by
          simpa using
            (d4TripledSummand_d4TripledTrialityPerm_eq_iff a.1 (0 : Fin 3)).2 a.2⟩
        ⟨d4TripledTrialityPerm b.1, by
          simpa using
            (d4TripledSummand_d4TripledTrialityPerm_eq_iff b.1 (1 : Fin 3)).2 b.2⟩ := by
  revert a b c
  decide +kernel

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

/-- The triality form on coordinate basis vectors is its signed integral coefficient. -/
@[simp]
theorem trialityTrilinearForm_basis (R : Type*) [CommRing R]
    (a : Block 0) (b : Block 1) (c : Block 2) :
    trialityTrilinearForm R (Pi.single a 1) (Pi.single b 1) (Pi.single c 1) =
      (trialityCoefficient a b c : R) := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private theorem trialityTrilinearForm_apply_basis_basis (R : Type*) [CommRing R]
    (v : Block 0 → R) (b : Block 1) (c : Block 2) :
    trialityTrilinearForm R v (Pi.single b 1) (Pi.single c 1) =
      ∑ a, v a * (trialityCoefficient a b c : R) := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private theorem trialityTrilinearForm_basis_apply_basis (R : Type*) [CommRing R]
    (a : Block 0) (v : Block 1 → R) (c : Block 2) :
    trialityTrilinearForm R (Pi.single a 1) v (Pi.single c 1) =
      ∑ b, (trialityCoefficient a b c : R) * v b := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private theorem trialityTrilinearForm_basis_basis_apply (R : Type*) [CommRing R]
    (a : Block 0) (b : Block 1) (v : Block 2 → R) :
    trialityTrilinearForm R (Pi.single a 1) (Pi.single b 1) v =
      ∑ c, (trialityCoefficient a b c : R) * v c := by
  classical
  simp [trialityTrilinearForm, Pi.single_apply]

private noncomputable def trilinearDiagonalAction {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (T : A →ₗ[R] B →ₗ[R] C →ₗ[R] R)
    (f : Module.End R A) (g : Module.End R B) (h : Module.End R C) :
    A →ₗ[R] B →ₗ[R] C →ₗ[R] R :=
  T.comp f + (LinearMap.lcomp R (C →ₗ[R] R) g).comp T +
    (LinearMap.compRight R (LinearMap.lcomp R R h)).comp T

private theorem trilinearDiagonalAction_apply {R A B C : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup C] [Module R C]
    (T : A →ₗ[R] B →ₗ[R] C →ₗ[R] R)
    (f : Module.End R A) (g : Module.End R B) (h : Module.End R C)
    (a : A) (b : B) (c : C) :
    trilinearDiagonalAction T f g h a b c =
      T (f a) b c + T a (g b) c + T a b (h c) := rfl

private theorem trialityTrilinearForm_invariant_of_coefficients
    (R : Type*) [CommRing R]
    (M₀ : Matrix (Block 0) (Block 0) R)
    (M₁ : Matrix (Block 1) (Block 1) R)
    (M₂ : Matrix (Block 2) (Block 2) R)
    (h : ∀ a b c,
      (∑ x, M₀ x a * (trialityCoefficient x b c : R)) +
        (∑ y, (trialityCoefficient a y c : R) * M₁ y b) +
          ∑ z, (trialityCoefficient a b z : R) * M₂ z c = 0) :
    trilinearDiagonalAction (trialityTrilinearForm R)
      M₀.mulVecLin M₁.mulVecLin M₂.mulVecLin = 0 := by
  apply (Pi.basisFun R (Block 0)).ext
  intro a
  apply (Pi.basisFun R (Block 1)).ext
  intro b
  apply (Pi.basisFun R (Block 2)).ext
  intro c
  simpa only [trilinearDiagonalAction_apply, Pi.basisFun_apply,
    LinearMap.zero_apply, Matrix.mulVecLin_apply,
    trialityTrilinearForm_apply_basis_basis,
    trialityTrilinearForm_basis_apply_basis,
    trialityTrilinearForm_basis_basis_apply, Matrix.mulVec,
    dotProduct_single, mul_one] using h a b c

private theorem trialityTrilinearForm_raising_invariant_map
    (R : Type*) [CommRing R] (i : Fin 4) :
    trilinearDiagonalAction (trialityTrilinearForm R)
      (blockRaisingMatrix R 0 i).mulVecLin
      (blockRaisingMatrix R 1 i).mulVecLin
      (blockRaisingMatrix R 2 i).mulVecLin = 0 := by
  apply trialityTrilinearForm_invariant_of_coefficients
  intro a b c
  rw [← map_zero (Int.castRingHom R)]
  convert congrArg (Int.castRingHom R) (trialityCoefficient_raising i a b c) using 1
  all_goals simp [mul_comm]

private theorem trialityTrilinearForm_lowering_invariant_map
    (R : Type*) [CommRing R] (i : Fin 4) :
    trilinearDiagonalAction (trialityTrilinearForm R)
      (blockLoweringMatrix R 0 i).mulVecLin
      (blockLoweringMatrix R 1 i).mulVecLin
      (blockLoweringMatrix R 2 i).mulVecLin = 0 := by
  apply trialityTrilinearForm_invariant_of_coefficients
  intro a b c
  rw [← map_zero (Int.castRingHom R)]
  convert congrArg (Int.castRingHom R) (trialityCoefficient_lowering i a b c) using 1
  all_goals simp [mul_comm]

private theorem trialityTrilinearForm_cartan_invariant_map
    (R : Type*) [CommRing R] (i : Fin 4) :
    trilinearDiagonalAction (trialityTrilinearForm R)
      (blockCartanGeneratorMatrix R 0 i).mulVecLin
      (blockCartanGeneratorMatrix R 1 i).mulVecLin
      (blockCartanGeneratorMatrix R 2 i).mulVecLin = 0 := by
  apply trialityTrilinearForm_invariant_of_coefficients
  intro a b c
  rw [← map_zero (Int.castRingHom R)]
  convert congrArg (Int.castRingHom R) (trialityCoefficient_cartan i a b c) using 1
  all_goals simp [mul_comm]

/-- The triality form is invariant under the diagonal action of a positive Chevalley generator. -/
theorem trialityTrilinearForm_raising_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockRaisingMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockRaisingMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockRaisingMatrix R 2 i *ᵥ v₂) = 0 := by
  have h := congrArg (fun T => T v₀ v₁ v₂)
    (trialityTrilinearForm_raising_invariant_map R i)
  simpa [trilinearDiagonalAction] using h

/-- The triality form is invariant under the diagonal action of a negative Chevalley generator. -/
theorem trialityTrilinearForm_lowering_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockLoweringMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockLoweringMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockLoweringMatrix R 2 i *ᵥ v₂) = 0 := by
  have h := congrArg (fun T => T v₀ v₁ v₂)
    (trialityTrilinearForm_lowering_invariant_map R i)
  simpa [trilinearDiagonalAction] using h

/-- The triality form is invariant under the diagonal action of a Cartan Chevalley generator. -/
theorem trialityTrilinearForm_cartan_invariant (R : Type*) [CommRing R] (i : Fin 4)
    (v₀ : Block 0 → R) (v₁ : Block 1 → R) (v₂ : Block 2 → R) :
    trialityTrilinearForm R (blockCartanGeneratorMatrix R 0 i *ᵥ v₀) v₁ v₂ +
        trialityTrilinearForm R v₀ (blockCartanGeneratorMatrix R 1 i *ᵥ v₁) v₂ +
      trialityTrilinearForm R v₀ v₁ (blockCartanGeneratorMatrix R 2 i *ᵥ v₂) = 0 := by
  have h := congrArg (fun T => T v₀ v₁ v₂)
    (trialityTrilinearForm_cartan_invariant_map R i)
  simpa [trilinearDiagonalAction] using h

end TauCeti.D4Tripled
