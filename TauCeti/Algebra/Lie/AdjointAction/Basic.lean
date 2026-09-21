/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Data.Nat.Choose.Sum

/-!
# The iterated adjoint action of an associative algebra

Let `A` be an associative `R`-algebra, bracketed by its ring commutator, and let
`ad R A a : Module.End R A` be the inner derivation `b ↦ ⁅a, b⁆`.  Two powers are in play and
they must not be confused: `a ^ n` is a power in the ring `A`, while `ad R A a ^ n` is a power in
the endomorphism ring `Module.End R A`, that is, the `n`-fold iterated commutator with `a`.

This file expands the second kind over an arbitrary commutative ring `R`.  Since `ad R A a` is the
difference of the commuting endomorphisms `LinearMap.mulLeft R a` and `LinearMap.mulRight R a`, the
`n`-fold iterated commutator is their binomial expansion: a sum of the products
`a ^ m * b * (-a) ^ (n - m)`, with the sign absorbed into `(-a) ^ (n - m)` rather than carried as a
separate `(-1) ^ k`.  Alongside it, `ad_eq_zero_iff_mem_center` records that the adjoint action of
`a` vanishes exactly when `a` is central.

Over an algebra of exponential characteristic `p` the expansion collapses at `n = p ^ e`, which is
the subject of `TauCeti.Algebra.Lie.AdjointAction.Frobenius`.

## Main statements

* `TauCeti.LieAlgebra.ad_pow_eq_sum` and `TauCeti.LieAlgebra.ad_pow_apply`: the
  iterated-commutator expansion of `ad R A a ^ n`, at operator level and evaluated.
* `TauCeti.LieAlgebra.ad_eq_zero_iff_mem_center`: `ad R A a` vanishes exactly on the centre.

## References

* N. Jacobson, *Lie Algebras*, Interscience (1962), Chapter V.
-/

public section

namespace TauCeti.LieAlgebra

open Finset

attribute [local instance 100] LieRing.ofAssociativeRing

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- **The iterated-commutator expansion, at operator level.**  Left and right multiplication by
`a` commute by associativity, so the `n`-fold commutator with `a` is their binomial expansion.
The sign that usually accompanies such an expansion is absorbed into `(-a) ^ (n - m)`. -/
theorem ad_pow_eq_sum (a : A) (n : ℕ) :
    LieAlgebra.ad R A a ^ n =
      ∑ m ∈ range (n + 1),
        n.choose m • (LinearMap.mulLeft R (a ^ m) * LinearMap.mulRight R ((-a) ^ (n - m))) := by
  have hneg : LinearMap.mulRight R (-a) = -LinearMap.mulRight R a := by
    ext b
    simp
  have hcomm : Commute (LinearMap.mulLeft R a) (LinearMap.mulRight R (-a)) :=
    LinearMap.commute_mulLeft_right a (-a)
  rw [LieAlgebra.ad_eq_lmul_left_sub_lmul_right, Pi.sub_apply, sub_eq_add_neg, ← hneg,
    hcomm.add_pow n]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  rw [LinearMap.pow_mulLeft, LinearMap.pow_mulRight, nsmul_eq_mul]
  exact (Nat.cast_commute (n.choose m) _).eq.symm

/-- **The iterated-commutator expansion, evaluated.**  This is `ad_pow_eq_sum` applied to an
element: the `n`-fold commutator of `a` with `b` is the binomial sum of the products
`a ^ m * b * (-a) ^ (n - m)`. -/
theorem ad_pow_apply (a b : A) (n : ℕ) :
    (LieAlgebra.ad R A a ^ n) b =
      ∑ m ∈ range (n + 1), n.choose m • (a ^ m * b * (-a) ^ (n - m)) := by
  rw [ad_pow_eq_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun m _ ↦ ?_
  simp only [LinearMap.smul_apply, Module.End.mul_apply, LinearMap.mulLeft_apply,
    LinearMap.mulRight_apply, mul_assoc]

/-- The adjoint action of `a` vanishes exactly when `a` is central. -/
theorem ad_eq_zero_iff_mem_center (a : A) :
    LieAlgebra.ad R A a = 0 ↔ a ∈ Subalgebra.center R A := by
  rw [LinearMap.ext_iff, Subalgebra.mem_center_iff]
  refine forall_congr' fun b ↦ ?_
  rw [LieAlgebra.ad_apply, Ring.lie_def, LinearMap.zero_apply, sub_eq_zero, eq_comm]

end TauCeti.LieAlgebra
