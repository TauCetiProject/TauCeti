/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.IntegralClosure

/-!
# Naturality and local invariants of the integral-closure double-coset law

This file extends the canonical integral-closure double-coset bijection with equivariance,
naturality under enlarging the subgroup, and local-invariant formulas evaluated on a double
coset. The bijection and the formulas on representatives are supplied by
`TauCeti.NumberTheory.RamificationInertia.DoubleCoset.IntegralClosure`.

The prime bijection only requires an integrally closed base. The local-degree formulas use a
Dedekind base, without finite residue fields or residue separability. Only the separate
ramification-index formula assumes residue separability.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_smul_mk`: change of the chosen
  prime by the Galois action agrees with right multiplication of representatives.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_natural`: enlarging the subgroup
  agrees with contraction of primes.
* `ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex`
  the local degree of a double coset is an index of conjugate decomposition groups.
* `Ideal.ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex_inertia`:
  under residue separability, the ramification index is an index of conjugate inertia groups.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, section 9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

namespace Ideal

variable {A K M B : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M] [Algebra A M]
  [IsScalarTower A K M] [CommRing B] [Algebra A B] [Algebra B M]
  [IsScalarTower A B M] [IsIntegralClosure B A M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

variable (Q : Ideal B) [Q.IsPrime] (p : Ideal A) [Q.LiesOver p]
  (H : Subgroup Gal(M/K)) [Algebra A (fixedField H)] [IsScalarTower A K (fixedField H)]
  (C : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)] [IsIntegralClosure C A (fixedField H)]
  [Algebra C B] [Algebra C M] [IsScalarTower A C B] [IsScalarTower C (fixedField H) M]
  [IsScalarTower C B M]

section Bijection

variable [IsDomain A] [IsIntegrallyClosed A]

/-- Changing the chosen prime from `Q` to `τ • Q` agrees with right multiplication of
representatives by `τ`. The action on the integral closure may be any compatible action
commuting with the base ring, including the canonical restricted Galois action. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_smul_mk
    [SMulCommClass Gal(M/K) A B] (τ σ : Gal(M/K)) :
    ((τ • Q).doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C
      (DoubleCoset.mk H _ σ) : Ideal C) =
      Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C
        (DoubleCoset.mk H _ (σ * τ)) := by
  simp only [doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk, mul_smul]

/-- Enlarging the subgroup and contracting to its integral closure give the same prime
under the integral-closure double-coset bijection. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_natural
    {H' : Subgroup Gal(M/K)} (h : H ≤ H')
    (C' : Type*) [CommRing C'] [Algebra A (fixedField H')]
    [IsScalarTower A K (fixedField H')] [Algebra A C'] [Algebra C' (fixedField H')]
    [IsScalarTower A C' (fixedField H')] [IsIntegralClosure C' A (fixedField H')]
    [Algebra C' B] [Algebra C' M] [IsScalarTower A C' B]
    [IsScalarTower C' (fixedField H') M] [IsScalarTower C' B M]
    [Algebra C' C] [IsScalarTower C' C B]
    (q : DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K))) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H' C'
        (DoubleCoset.quotientMapOfLELeft h (stabilizer Gal(M/K) Q) q)).1 =
      (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q).1.under C' := by
  induction q using Quotient.inductionOn' with
  | h σ =>
    simp only [DoubleCoset.quotientMapOfLELeft_apply_mk,
      doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk, under_under]

end Bijection

section Invariants

variable [IsDedekindDomain A] [Q.IsMaximal]

/-- The local degree of the prime attached to a double coset is the relative index of its
conjugate decomposition group. Residue separability is not required. -/
theorem
    ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex
    (q : DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K))) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).ramificationIdx A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).inertiaDeg A =
      H.relIndex (MulAut.conj q.out • stabilizer Gal(M/K) Q) := by
  conv_lhs =>
    rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]
  exact Q.ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex_of_isIntegralClosure H C q.out

/-- Under residue separability, the ramification index of the prime attached to a double
coset is the relative index of its conjugate inertia group. -/
theorem ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex_inertia
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ Q)]
    (q : DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K))) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).ramificationIdx A =
      H.relIndex (MulAut.conj q.out • Q.inertia Gal(M/K)) := by
  conv_lhs =>
    rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]
  exact Q.ramificationIdx_under_smul_eq_relIndex_inertia_of_isIntegralClosure p H C q.out

end Invariants

end Ideal
