/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.AdjoinRoot
import Mathlib.LinearAlgebra.Vandermonde
import TauCeti.Algebra.Algebra.Pi

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
  have hd : IsUnit (Matrix.vandermonde v).det := by
    rw [Matrix.det_vandermonde]
    rw [IsUnit.prod_iff]
    intro i _
    rw [IsUnit.prod_iff]
    intro j hj
    exact hs (index i) (index j) (index.injective.ne (ne_of_lt (Finset.mem_Ioi.mp hj)))
  have hM : (Matrix.of fun i j ↦ s (index i) (b j)) = Matrix.vandermonde v := by
    ext i j
    simp only [Matrix.of_apply, hb, map_pow, Matrix.vandermonde_apply, v]
  have hbij := AlgHom.pi_bijective_of_isUnit_det (s ∘ index) b (hM.symm ▸ hd)
  -- Transport back to the original labels only after proving the matrix criterion.
  have hreindex : (AlgHom.pi (s ∘ index) : AdjoinRoot f → Fin f.natDegree → R) =
      (Equiv.piCongrLeft' (fun _ : ι ↦ R) index.symm) ∘ AlgHom.pi s := by
    ext x i
    simp only [Function.comp_apply, Equiv.piCongrLeft'_apply, Equiv.symm_symm,
      AlgHom.pi_apply]
  rw [hreindex] at hbij
  exact (Equiv.comp_bijective _ _).mp hbij

end AdjoinRoot
