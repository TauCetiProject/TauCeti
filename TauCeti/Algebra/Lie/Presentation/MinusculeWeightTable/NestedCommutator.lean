/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Presentation.MinusculeWeightTable.Basic
public import TauCeti.LinearAlgebra.Matrix.UnipotentCommutator

/-!
# Adjacent-root nested commutators for minuscule weight tables

The square-zero matrices of a minuscule weight table satisfy the nested Chevalley commutator
identity over every commutative ring at nodes whose two Cartan entries are `-1`.
The raising and lowering forms below apply to any units with the specified matrix values.

The argument is extracted from the adjacent-root calculation in
`TauCeti.Algebra.Lie.E7.Minuscule.ChevalleyRelations`.

## References

* R. W. Carter, *Simple Groups of Lie Type*, Theorem 5.2.2.
-/

public section

namespace TauCeti.MinusculeWeightTable

open scoped commutatorElement

attribute [local instance 100] LieRing.ofAssociativeRing

variable {B ι : Type*} [Fintype ι] [DecidableEq ι] (T : MinusculeWeightTable B ι)

/-- At a simply laced edge, two raising unipotents followed by the matching lowering
unipotent have nested commutator equal to the first raising unipotent at the product parameter.
The identity holds over every commutative ring. -/
theorem coe_commutatorElement_commutatorElement_raisingMatrix {i j : B}
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    {R : Type*} [CommRing R] (t s r : R) (x y z : (Matrix ι ι R)ˣ)
    (hx : (x : Matrix ι ι R) = 1 + t • (T.raisingMatrix i).map (Int.cast : ℤ → R))
    (hy : (y : Matrix ι ι R) = 1 + s • (T.raisingMatrix j).map (Int.cast : ℤ → R))
    (hz : (z : Matrix ι ι R) = 1 + r • (T.loweringMatrix j).map (Int.cast : ℤ → R)) :
    (↑⁅⁅x, y⁆, z⁆ : Matrix ι ι R) =
      1 + (t * s * r) • (T.raisingMatrix i).map (Int.cast : ℤ → R) := by
  have hne : i ≠ j := ne_of_apply_ne (T.cartanMatrix i)
    (by rw [T.cartanMatrix_diag, hij]; norm_num)
  have hAC := T.isSerreSystem.lie_E_F_of_ne i j hne
  have hABC : ⁅⁅T.raisingMatrix i, T.raisingMatrix j⁆, T.loweringMatrix j⁆ =
      T.raisingMatrix i := by
    rw [T.isSerreSystem.lie_lie_E_E_F_of_ne hne, hji, neg_one_zsmul, neg_neg]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (T.raisingMatrix i) (T.raisingMatrix j) (T.loweringMatrix j)
    (by simpa only [pow_two] using T.raisingMatrix_pow_two i)
    (by simpa only [pow_two] using T.raisingMatrix_pow_two j)
    (by simpa only [pow_two] using T.loweringMatrix_pow_two j)
    hAC hABC (T.isSerreSystem.lie_E_lie_E_E_eq_zero_of_eq_neg_one hij)
    (T.isSerreSystem.lie_E_lie_E_E_eq_zero_of_eq_neg_one hji) t s r x y z hx hy hz

/-- The sign-reversed adjacent-root nested commutator identity for lowering unipotents
of a minuscule weight table, over every commutative ring. -/
theorem coe_commutatorElement_commutatorElement_loweringMatrix {i j : B}
    (hij : T.cartanMatrix i j = -1) (hji : T.cartanMatrix j i = -1)
    {R : Type*} [CommRing R] (t s r : R) (x y z : (Matrix ι ι R)ˣ)
    (hx : (x : Matrix ι ι R) = 1 + t • (T.loweringMatrix i).map (Int.cast : ℤ → R))
    (hy : (y : Matrix ι ι R) = 1 + s • (T.loweringMatrix j).map (Int.cast : ℤ → R))
    (hz : (z : Matrix ι ι R) = 1 + r • (T.raisingMatrix j).map (Int.cast : ℤ → R)) :
    (↑⁅⁅x, y⁆, z⁆ : Matrix ι ι R) =
      1 + (t * s * r) • (T.loweringMatrix i).map (Int.cast : ℤ → R) := by
  have hne : i ≠ j := ne_of_apply_ne (T.cartanMatrix i)
    (by rw [T.cartanMatrix_diag, hij]; norm_num)
  have hAC : ⁅T.loweringMatrix i, T.raisingMatrix j⁆ = 0 := by
    rw [← lie_skew, T.isSerreSystem.lie_E_F_of_ne j i hne.symm, neg_zero]
  have hABC : ⁅⁅T.loweringMatrix i, T.loweringMatrix j⁆, T.raisingMatrix j⁆ =
      T.loweringMatrix i := by
    rw [T.isSerreSystem.lie_lie_F_F_E_of_ne hne, hji, neg_one_zsmul, neg_neg]
  exact Matrix.coe_commutatorElement_commutatorElement_eq_one_add_smul
    (T.loweringMatrix i) (T.loweringMatrix j) (T.raisingMatrix j)
    (by simpa only [pow_two] using T.loweringMatrix_pow_two i)
    (by simpa only [pow_two] using T.loweringMatrix_pow_two j)
    (by simpa only [pow_two] using T.raisingMatrix_pow_two j)
    hAC hABC (T.isSerreSystem.lie_F_lie_F_F_eq_zero_of_eq_neg_one hij)
    (T.isSerreSystem.lie_F_lie_F_F_eq_zero_of_eq_neg_one hji) t s r x y z hx hy hz

end TauCeti.MinusculeWeightTable
