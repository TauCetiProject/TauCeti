/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Symmetric.Stable.Bialgebra
public import Mathlib.RingTheory.HopfAlgebra.Primitive
import TauCeti.Algebra.HopfAlgebra.Antipode
import TauCeti.RingTheory.MvPolynomial.Symmetric.Complete.Elementary

/-!
# The Hopf algebra of symmetric functions

The alphabet-splitting bialgebra of symmetric functions is a Hopf algebra over every
commutative ring. Its antipode sends the elementary symmetric function `e_n` to
`(-1)^n h_n`, the complete homogeneous function `h_n` to `(-1)^n e_n`, and the
positive power sum `p_n` to `-p_n`.

The antipode is constructed on the free elementary generators. The identity
`H(t) E(-t) = 1` supplies the antipode laws, without division or a restriction on
characteristic. The involutivity theorem for commutative Hopf algebras then gives
its values on the complete homogeneous functions.

## References

* [I. G. Macdonald, *Symmetric Functions and Hall Polynomials*][macdonald1995],
  Chapter I, Section 5, Example 25.
* The construction uses Mathlib's `HopfAlgebra.ofAlgHom` and the existing
  `TauCeti.SymmetricFunction.instBialgebra`.
-/

public section

open Finset MvPolynomial TensorProduct

namespace TauCeti.SymmetricFunction

variable (R : Type*) [CommRing R]

private theorem antipode_aux_of_stableEsymm (n : ℕ) :
    ((aeval fun r => (-1 : SymmetricFunction R) ^ (r + 1) *
        DirectSum.of _ (r + 1) (stableHsymm R (r + 1))).comp
      (esymmAlgEquiv R).symm.toAlgHom) (DirectSum.of _ n (stableEsymm R n)) =
        (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n) := by
  cases n with
  | zero => simp
  | succ r => simp

private theorem left_antipode_law
    (S : SymmetricFunction R →ₐ[R] SymmetricFunction R)
    (hS : ∀ n, S (DirectSum.of _ n (stableEsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n)) :
    (Algebra.TensorProduct.lift S (.id R _) fun _ _ => Commute.all _ _).comp
        (Bialgebra.comulAlgHom R _) =
      (Algebra.ofId R _).comp (Bialgebra.counitAlgHom R _) := by
  apply algHom_ext
  intro n
  simp only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, comul_of_stableEsymm,
    map_sum, Algebra.TensorProduct.lift_tmul, AlgHom.id_apply, hS,
    Bialgebra.counitAlgHom_apply, counit_of_ne_zero R (Nat.succ_ne_zero n), map_zero]
  apply ext_specialization (R := R)
  intro d
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, specialization_of,
    coe_stableSymmetricProj_stableHsymm, coe_stableSymmetricProj_stableEsymm, map_zero]
  have h := sum_antidiagonal_hsymm_mul_neg_one_pow_mul_esymm (σ := Fin d) R (n + 1)
  simp only [Nat.succ_ne_zero, ite_false] at h
  have hp (p : ℕ × ℕ) (hp : p ∈ antidiagonal (n + 1)) :
      (-1 : MvPolynomial (Fin d) R) ^ p.1 * hsymm (Fin d) R p.1 * esymm (Fin d) R p.2 =
        (-1 : MvPolynomial (Fin d) R) ^ (n + 1) *
          (hsymm (Fin d) R p.1 * ((-1) ^ p.2 * esymm (Fin d) R p.2)) := by
    rw [← mem_antidiagonal.mp hp, pow_add]
    ring_nf
    simp [Nat.mul_comm p.2 2, pow_mul]
  simp_rw [Finset.sum_congr rfl hp, ← mul_sum, h, mul_zero]

private theorem right_antipode_law
    (S : SymmetricFunction R →ₐ[R] SymmetricFunction R)
    (hS : ∀ n, S (DirectSum.of _ n (stableEsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n)) :
    (Algebra.TensorProduct.lift (.id R _) S fun _ _ => Commute.all _ _).comp
        (Bialgebra.comulAlgHom R _) =
      (Algebra.ofId R _).comp (Bialgebra.counitAlgHom R _) := by
  rw [← left_antipode_law R S hS]
  refine DFunLike.ext _ _ fun x => ?_
  simpa only [AlgHom.comp_apply, Bialgebra.comulAlgHom_apply, AlgHom.convMul_apply] using
    congr($(mul_comm (WithConv.toConv (.id R _)) (WithConv.toConv S)) x)

/-- The alphabet-splitting bialgebra of symmetric functions is a Hopf algebra, with
antipode `S(e_n) = (-1)^n h_n`. -/
noncomputable instance instHopfAlgebra : _root_.HopfAlgebra R (SymmetricFunction R) :=
  .ofAlgHom
    ((aeval fun r => (-1 : SymmetricFunction R) ^ (r + 1) *
        DirectSum.of _ (r + 1) (stableHsymm R (r + 1))).comp
      (esymmAlgEquiv R).symm.toAlgHom)
    (by exact left_antipode_law R _ (antipode_aux_of_stableEsymm R))
    (by exact right_antipode_law R _ (antipode_aux_of_stableEsymm R))

/-- The antipode sends `e_n` to `(-1)^n h_n`, including the unit in degree zero. -/
@[simp]
theorem antipode_of_stableEsymm (n : ℕ) :
    HopfAlgebraStruct.antipode R (DirectSum.of _ n (stableEsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableHsymm R n) := by
  exact antipode_aux_of_stableEsymm R n

/-- The antipode sends `h_n` to `(-1)^n e_n`, including the unit in degree zero. -/
@[simp]
theorem antipode_of_stableHsymm (n : ℕ) :
    HopfAlgebraStruct.antipode R (DirectSum.of _ n (stableHsymm R n)) =
      (-1 : SymmetricFunction R) ^ n * DirectSum.of _ n (stableEsymm R n) := by
  have h := TauCeti.HopfAlgebra.antipode_antipode
    (R := R) (DirectSum.of _ n (stableEsymm R n) : SymmetricFunction R)
  have hsign : HopfAlgebraStruct.antipode R ((-1 : SymmetricFunction R) ^ n) =
      (-1 : SymmetricFunction R) ^ n := by
    simp only [← _root_.HopfAlgebra.antipodeAlgHom_apply, map_pow, map_neg, map_one]
  rw [antipode_of_stableEsymm, _root_.HopfAlgebra.antipode_mul_distrib, hsign] at h
  calc
    _ = (-1 : SymmetricFunction R) ^ n *
        ((-1 : SymmetricFunction R) ^ n *
          HopfAlgebraStruct.antipode R (DirectSum.of _ n (stableHsymm R n))) := by
      simp [← mul_assoc, ← mul_pow]
    _ = _ := by rw [h]

/-- The antipode negates each positive power sum, since power sums are primitive. -/
@[simp]
theorem antipode_of_stablePsum {n : ℕ} (hn : n ≠ 0) :
    HopfAlgebraStruct.antipode R (DirectSum.of _ n (stablePsum R hn)) =
      -(DirectSum.of _ n (stablePsum R hn) : SymmetricFunction R) := by
  apply Bialgebra.IsPrimitiveElem.antipode_eq_neg
  constructor
  · exact counit_of_ne_zero R hn _
  · simpa only [add_comm] using comul_of_stablePsum R hn

end TauCeti.SymmetricFunction
