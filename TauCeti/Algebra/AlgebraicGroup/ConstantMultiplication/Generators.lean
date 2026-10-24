/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.ConstantMultiplication.Basic

/-!
# Diagonal and elementary matrices preserving a constant multiplication

Fix constant structure matrices `C : Fin n → Matrix (Fin n) (Fin n) R`, so that
`eₖ * eⱼ = ∑ᵢ (Cₖ)ᵢⱼ eᵢ`. This file gives entrywise criteria for the two kinds of matrices that
generate a Chevalley-type group in a weight basis to preserve that multiplication.

* A diagonal matrix with entries `dᵢ` preserves it exactly when `dᵢ (Cₖ)ᵢⱼ = dₖ (Cₖ)ᵢⱼ dⱼ` for
  all `i`, `j`, `k`: every nonzero structure constant relates three diagonal entries.
* If a constant matrix `X` is a derivation of the multiplication,
  `X Cₖ = ∑ₐ Xₐₖ Cₐ + Cₖ X`, and the second-order terms vanish, `(∑ₐ Xₐₖ Cₐ) X = 0`, then
  `1 + u X` preserves the multiplication for every scalar `u` of every commutative algebra. This
  is the form taken by a root subgroup `u ↦ 1 + u X` of a minuscule representation, where `X`
  squares to zero.

The derivation equation is the tangent equation of the subgroup scheme preserving the
multiplication, `TauCeti.ConstantMultiplication.mem_lieSubalgebra_definingHopfIdeal_iff`; the
second criterion integrates it along a square-zero direction.

## Main results

* `TauCeti.ConstantMultiplication.preserves_diagonal_iff`: the diagonal criterion.
* `TauCeti.ConstantMultiplication.preserves_one_add_smul`: the elementary-matrix criterion.

## References

* J. S. Milne, *Algebraic Groups* (2017), §2.3 and §10.a.
* R. W. Carter, *Simple Groups of Lie Type*, §§4.4 and 7.1.
-/

public section

open Matrix

namespace TauCeti.ConstantMultiplication

universe u v

variable {R : Type u} [CommRing R] {n : ℕ} (C : Fin n → Matrix (Fin n) (Fin n) R)
variable {S : Type v} [CommRing S] [Algebra R S]

/-- **A diagonal matrix preserves a constant multiplication exactly when every structure constant
relates its diagonal entries**: `dᵢ (Cₖ)ᵢⱼ = dₖ (Cₖ)ᵢⱼ dⱼ` for all `i`, `j`, `k`. -/
theorem preserves_diagonal_iff (d : Fin n → S) :
    Preserves R n C (diagonal d) ↔
      ∀ k i j, d i * algebraMap R S (C k i j) = d k * algebraMap R S (C k i j) * d j := by
  have himage : ∀ k, imageStructureMatrix R n C (diagonal d) k = d k • (C k).map (algebraMap R S) :=
    fun k => by
      rw [imageStructureMatrix_def]
      simp only [diagonal_apply, ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
        ite_true]
  simp only [preserves_def, himage, ← Matrix.ext_iff, diagonal_mul, mul_diagonal,
    Matrix.smul_apply, map_apply, smul_eq_mul]

/-- **An elementary matrix `1 + u X` preserves a constant multiplication** when `X` is a derivation
of it whose second-order terms vanish: `X Cₖ = ∑ₐ Xₐₖ Cₐ + Cₖ X` and `(∑ₐ Xₐₖ Cₐ) X = 0` for every
`k`. The scalar `u` may lie in any commutative `R`-algebra. -/
theorem preserves_one_add_smul {X : Matrix (Fin n) (Fin n) R}
    (hder : ∀ k, X * C k = ∑ a, X a k • C a + C k * X)
    (hsq : ∀ k, (∑ a, X a k • C a) * X = 0) (t : S) :
    Preserves R n C (1 + t • X.map (algebraMap R S)) := by
  let f := (algebraMap R S).mapMatrix (m := Fin n)
  have hf : ∀ M : Matrix (Fin n) (Fin n) R, M.map (algebraMap R S) = f M := fun _ => rfl
  have hsum : ∀ k, f (∑ a, X a k • C a) =
      ∑ a, (X.map (algebraMap R S)) a k • (C a).map (algebraMap R S) := fun k => by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hf, Matrix.map_smul' _ _ _ (map_mul (algebraMap R S)), map_apply]
  rw [preserves_def]
  intro k
  have hder' := congrArg f (hder k)
  have hsq' := congrArg f (hsq k)
  rw [map_mul, map_add, map_mul, hsum] at hder'
  rw [map_mul, hsum, map_zero] at hsq'
  simp only [← hf] at hder' hsq'
  have himage : imageStructureMatrix R n C (1 + t • X.map (algebraMap R S)) k =
      (C k).map (algebraMap R S) +
        t • ∑ a, (X.map (algebraMap R S)) a k • (C a).map (algebraMap R S) := by
    rw [imageStructureMatrix_def]
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, smul_eq_mul, add_smul,
      Finset.sum_add_distrib, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ,
      ite_true, Finset.smul_sum, mul_smul]
  rw [himage, add_mul, one_mul, smul_mul_assoc, hder']
  simp only [mul_add, add_mul, mul_one, mul_smul_comm, smul_mul_assoc, hsq', smul_zero, add_zero,
    smul_add]
  abel

end TauCeti.ConstantMultiplication
