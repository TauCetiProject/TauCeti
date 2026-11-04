/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# Splitting a monogenic algebra by evaluation

For a monic polynomial of degree `d`, evaluation at `d` roots with pairwise unit
differences identifies its root algebra with a product of `d` copies of the base ring.
The unit-difference hypothesis, rather than mere distinctness, makes the statement valid
over arbitrary commutative rings, including nonreduced rings. This is the Vandermonde
form of the Chinese remainder theorem for linear factors.
-/

public section

open Polynomial

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {f : R[X]}

/-- Evaluation at a degree-sized family of roots of a monic polynomial is bijective
when the differences of distinct roots are units. -/
theorem pi_bijective_of_isUnit_sub (hf : f.Monic)
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = f.natDegree)
    (s : ι → AdjoinRoot f →ₐ[R] R)
    (hs : ∀ i j, i ≠ j → IsUnit (s j (root f) - s i (root f))) :
    Function.Bijective (AlgHom.pi s) := by
  classical
  -- Enumerate the roots to compare evaluation with the power-basis Vandermonde matrix.
  let index : Fin f.natDegree ≃ ι := Fintype.equivOfCardEq (by simpa using hι.symm)
  let b : Module.Basis (Fin f.natDegree) R (AdjoinRoot f) := (powerBasis' hf).basis
  have hb (j : Fin f.natDegree) : b j = root f ^ (j : ℕ) :=
    (powerBasis' hf).basis_eq_pow j
  let v := fun i ↦ s (index i) (root f)
  have eval_eq_sum (x : AdjoinRoot f) (i : Fin f.natDegree) :
      s (index i) x = ∑ j, b.repr x j * v i ^ (j : ℕ) := by
    conv_lhs => rw [← b.sum_repr x]
    simp only [map_sum, map_smul, hb, map_pow, smul_eq_mul, v]
  have hd : IsUnit (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde]
    rw [IsUnit.prod_iff]
    intro i _
    rw [IsUnit.prod_iff]
    intro j hj
    exact hs (index i) (index j) (index.injective.ne (ne_of_lt (Finset.mem_Ioi.mp hj)))
  let e := b.equivFun.trans
    (Matrix.toLinearEquiv (Pi.basisFun R (Fin f.natDegree)) (Matrix.vandermonde v) hd)
  have he (x : AdjoinRoot f) : e x = AlgHom.pi (s ∘ index) x := by
    ext i
    dsimp only [e, LinearEquiv.trans_apply]
    rw [Matrix.toLinearEquiv_apply, Matrix.toLin_eq_toLin', Matrix.toLin'_apply]
    simp only [Matrix.mulVec, dotProduct, Matrix.vandermonde_apply,
      Module.Basis.equivFun_apply, AlgHom.pi_apply, Function.comp_apply]
    rw [eval_eq_sum]
    exact Finset.sum_congr rfl (fun j _ ↦ mul_comm _ _)
  have hb := congrArg Function.Bijective (funext he) ▸ e.bijective
  -- Transport back to the original labels only after proving the matrix criterion.
  have hreindex : (AlgHom.pi (s ∘ index) : AdjoinRoot f → Fin f.natDegree → R) =
      (Equiv.piCongrLeft' (fun _ : ι ↦ R) index.symm) ∘ AlgHom.pi s := by
    ext x i
    simp only [Function.comp_apply, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
      AlgHom.pi_apply]
  rw [hreindex] at hb
  exact (Equiv.comp_bijective _ _).mp hb

end AdjoinRoot
