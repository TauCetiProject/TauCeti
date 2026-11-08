/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Orthogonal.TypeB.SpinCarrier.IntegralMatrix
public import TauCeti.Algebra.Lie.Sl2.Gauss
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Opposite-root Gauss factorization in the type-B spin carrier

The positive and negative simple-root points admit rank-one Gauss factorization over every
commutative ring when `1 + a * b` is a unit. The middle factor is the corresponding coordinate
of the existing spin weight torus, not an independently chosen diagonal element.

The calculation includes the short terminal root and uses integral root-string identities
before changing coefficients; in particular no invertibility of two is needed. It supplies
opposite-root collection for the numbered root parametrizations, without identifying the
carrier with an independently pinned group scheme.

## References

* C. Chevalley, *The Algebraic Theory of Spinors*, Chapter II.
* R. Steinberg, *Lectures on Chevalley Groups*, §3.
* R. W. Carter, *Simple Groups of Lie Type*, §6.4.

The formal construction uses `TypeBSpinCarrier.rootIntMatrix` and its integral weight support,
and the square-zero root-string identities of `TauCeti.Sl2`.
-/

public section

namespace TauCeti.TypeBSpinCarrier

open TauCeti.UniversalEnvelopingAlgebra

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n : ℕ)

/-- Opposite simple-root points factor through the numbered coroot of the spin weight torus
on the rank-one open cell. This includes the short terminal root over rings of characteristic
two, and requires neither root parameter to be a unit. -/
theorem rootSubgroupPoints_inl_mul_inr_gauss (i : Fin (n + 1))
    (A : Type*) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd a) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd b) =
      rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (b * (↑(u⁻¹) : A))) *
        weightTorusPoints n A (Pi.mulSingle i u) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (a * (↑(u⁻¹) : A))) := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_rootSubgroupPoints_eq_one_add_smul,
    toAdd_ofAdd, coe_weightTorusPoints_mulSingle]
  -- Establish the root-string identities over ℤ before specializing the coefficient ring.
  let f : Matrix (Fin (dimension n)) (Fin (dimension n)) ℤ →+*
      Matrix (Fin (dimension n)) (Fin (dimension n)) A := (Int.castRingHom A).mapMatrix
  have hEE := congrArg f (rootIntMatrix_mul_self_eq_zero n (.inl i))
  have hFF := congrArg f (rootIntMatrix_mul_self_eq_zero n (.inr i))
  have hEFE := congrArg f (rootIntMatrix_inl_mul_inr_mul_inl n i)
  have hFEF := congrArg f (rootIntMatrix_inr_mul_inl_mul_inr n i)
  simp only [map_mul, map_zero, f, RingHom.mapMatrix_apply,
    Int.coe_castRingHom] at hEE hFF hEFE hFEF
  rw [Matrix.map_mul_intCast, Matrix.map_mul_intCast]
  exact Sl2.gauss_of_mul_self_eq_zero hEE hFF hEFE hFEF a b u hu

/-- The reverse-order opposite-root factorization has the inverse coroot in its middle
factor. It holds under the same unit condition as the positive-first formula. -/
theorem rootSubgroupPoints_inr_mul_inl_gauss (i : Fin (n + 1))
    (A : Type*) [CommRing A] (a b : A) (u : Aˣ) (hu : (u : A) = 1 + a * b) :
    rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd b) *
        rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd a) =
      rootSubgroupPoints n (.inl i) A (Multiplicative.ofAdd (a * (↑(u⁻¹) : A))) *
        weightTorusPoints n A (Pi.mulSingle i u⁻¹) *
        rootSubgroupPoints n (.inr i) A (Multiplicative.ofAdd (b * (↑(u⁻¹) : A))) := by
  have h := rootSubgroupPoints_inl_mul_inr_gauss n i A (-a) (-b) u (by simpa using hu)
  have hi := congrArg Inv.inv h
  simpa only [mul_inv_rev, neg_mul, ofAdd_neg, map_inv, inv_inv,
    ← map_inv (weightTorusPoints n A), ← Pi.mulSingle_inv, mul_assoc] using hi

end TauCeti.TypeBSpinCarrier
