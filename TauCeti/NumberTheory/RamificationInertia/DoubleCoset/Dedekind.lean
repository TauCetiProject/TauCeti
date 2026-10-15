/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Inertia
public import TauCeti.RingTheory.IntegralClosure.GaloisGroup
-- Proof-only: integral closures over finite extensions of Dedekind fraction fields are Dedekind.
import TauCeti.RingTheory.DedekindDomain.IntegralClosure

/-!
# The double-coset splitting law over a Dedekind base

This file specializes the invariant-ring double-coset law to integral closures over an
arbitrary Dedekind domain. Let `A` have fraction field `K`, let `M / K` be finite Galois, and let
`B` be the integral closure of `A` in `M`. For a subgroup `H` of `Gal(M/K)`, let `C` be the
integral closure of `A` in the fixed field `M ^ H`. Then the primes of `C` over a prime `p` of
`A` are indexed by `H \ Gal(M/K) / D(Q)`.

Unlike the specialization to rings of integers of number fields, these results do not assume
finite residue fields. The prime bijection only requires that the base be integrally closed; the
local-degree formulas use the Dedekind hypothesis. Neither the bijection nor the local-degree
formula requires residue separability; the separate ramification-index formula assumes it
explicitly.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure`: the double-coset bijection for
  integral closures over an integrally closed base.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk`: the class of `σ` maps to the
  contraction of `σ • Q`.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_smul_mk`: indexing through `τ • Q`
  sends the class of `σ` to the prime that indexing through `Q` attaches to `σ * τ`.
* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_natural`: enlarging the subgroup
  agrees with contraction between the corresponding integral closures.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_smul_of_isIntegralClosure_eq_relIndex`: the
  residue-separability-free `e * f` formula.
* `Ideal.ramificationIdx_under_smul_of_isIntegralClosure_eq_relIndex_inertia`: the
  residue-separable `e` formula.
* The same two formulas for the prime attached to a double coset, in namespace `Ideal`:
  `ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex`
  and `ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex_inertia`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, section 9.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

namespace Ideal

variable {A B C K M : Type*}
  [CommRing A] [CommRing B] [CommRing C] [Field K] [Field M]
  [Algebra A K] [Algebra K M] [Algebra A M] [IsScalarTower A K M]
  [Algebra A B] [Algebra B M] [IsScalarTower A B M]
  [IsFractionRing A K]
  [IsIntegralClosure B A M]
  [IsGalois K M]

variable [FiniteDimensional K M]

variable (H : Subgroup (M ≃ₐ[K] M))
  [Algebra A C] [Algebra C ↥(fixedField H)] [Algebra C M]
  [IsScalarTower A C ↥(fixedField H)] [IsScalarTower C ↥(fixedField H) M]
  [IsScalarTower A C M]
  [IsIntegralClosure C A ↥(fixedField H)]
  [Algebra C B] [IsScalarTower C B M]

variable (p : Ideal A) (Q : Ideal B) [Q.LiesOver p]

-- Derive the faithfulness, domain, fraction-field, and Galois-group instances that the
-- invariant-ring API needs from the integral-closure setup `C ⊆ B` over `A` in `M ^ H ⊆ M`.
-- It expects the `IsIntegralClosure.MulSemiringAction A K M B` action to be in context.
local macro "integral_closure_galois_setup " A:term:max K:term:max M:term:max B:term:max
    C:term:max H:term:max : tactic => `(tactic| (
  have : FaithfulSMul $C ↥(IntermediateField.fixedField $H) :=
    IsIntegralClosure.faithfulSMul $A $C _
  have : FaithfulSMul $C $M := .trans $C ↥(IntermediateField.fixedField $H) $M
  have : FaithfulSMul $C $B := .tower_bot $C $B $M
  have : Algebra.IsIntegral $A $B := IsIntegralClosure.isIntegral_algebra $A $M
  have : IsDomain $A := (IsFractionRing.injective $A $K).isDomain
  have : IsDomain $B :=
    (IsIntegralClosure.algebraMap_injective $B $A $M).isDomain (algebraMap $B $M)
  have : IsFractionRing $B $M := IsIntegralClosure.isFractionRing_of_finite_extension $A $K $M $B
  have : IsGaloisGroup ($M ≃ₐ[$K] $M) $A $B :=
    IsGaloisGroup.of_isFractionRing ($M ≃ₐ[$K] $M) $A $B $K $M
  have : IsGaloisGroup $H $C $B :=
    TauCeti.IsIntegralClosure.isGaloisGroup_fixedField $A $K $M $B $C $H))

-- Extend `integral_closure_galois_setup` by the Dedekind, finiteness, and torsion-freeness
-- instances that the invariant-ring local-degree formulas need over a Dedekind base.
local macro "integral_closure_local_degree_setup " A:term:max K:term:max M:term:max B:term:max
    C:term:max H:term:max : tactic => `(tactic| (
  have : IsDedekindDomain $B := TauCeti.IsIntegralClosure.isDedekindDomain $A $K $M $B
  have : IsDedekindDomain $C :=
    TauCeti.IsIntegralClosure.isDedekindDomain $A $K ↥(IntermediateField.fixedField $H) $C
  integral_closure_galois_setup $A $K $M $B $C $H
  have : Module.Finite $A $B := IsIntegralClosure.finite $A $K $M $B
  have : Module.IsTorsionFree $A $M := .trans_faithfulSMul $A $K $M
  have : Module.IsTorsionFree $A $B := IsIntegralClosure.isTorsionFree $A $M))

section Equivalence

variable [IsIntegrallyClosed A] [Q.IsPrime] [IsScalarTower A C B]

/-- **The double-coset splitting law over an integrally closed base.** For integral closures
`B/A` and `C/A` in `M/K` and `M^H/K`, respectively, the primes of `C` above `p` are indexed by
the double cosets of `H` and the decomposition group of `Q`. -/
noncomputable def doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)) ≃ p.primesOver C := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_galois_setup A K M B C H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C

/-- The integral-closure double-coset law sends the class of `σ` to the contraction of
`σ • Q`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
      (A := A) (B := B) (C := C) (K := K) (M := M) H p Q
      (DoubleCoset.mk H _ σ) : Ideal C) = (σ • Q).under C := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_galois_setup A K M B C H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk p H C σ

/-- The inverse of the integral-closure double-coset bijection sends a prime to the class of `σ`
exactly when that prime is the contraction of `σ • Q`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_symm_apply_eq_mk_iff
    (q : p.primesOver C) (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
        (A := A) (B := B) (C := C) (K := K) (M := M) H p Q).symm q =
        DoubleCoset.mk H _ σ ↔
      q.1 = (σ • Q).under C := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_galois_setup A K M B C H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_symm_apply_eq_mk_iff p H C q σ

/-- **The integral-closure double-coset law is compatible with the action of `Gal(M/K)`.**
Indexing the primes of `C` above `p` through the translate `τ • Q` instead of `Q` sends the class
of `σ` to the prime that the indexing through `Q` attaches to the class of `σ * τ`. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_smul_mk (τ σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    haveI := TauCeti.IsIntegralClosure.smulCommClass A K M B
    (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
      (A := A) (B := B) (C := C) (K := K) (M := M) H p (τ • Q)
      (DoubleCoset.mk H _ σ) : Ideal C) =
    Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
      (A := A) (B := B) (C := C) (K := K) (M := M) H p Q (DoubleCoset.mk H _ (σ * τ)) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  simp only [doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk, mul_smul]

/-- Enlarging the subgroup and contracting to the corresponding integral closure give the same
prime under the integral-closure double-coset splitting bijection. -/
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_natural
    {H' : Subgroup (M ≃ₐ[K] M)} (h : H ≤ H')
    (C' : Type*) [CommRing C']
    [Algebra A C'] [Algebra C' ↥(fixedField H')] [Algebra C' M]
    [IsScalarTower A C' ↥(fixedField H')] [IsScalarTower C' ↥(fixedField H') M]
    [IsScalarTower A C' M]
    [IsIntegralClosure C' A ↥(fixedField H')]
    [Algebra C' B] [IsScalarTower A C' B] [IsScalarTower C' B M]
    [Algebra C' C] [IsScalarTower C' C B] :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ∀ q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)),
      (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
          (A := A) (B := B) (C := C') (K := K) (M := M) H' p Q
          (DoubleCoset.quotientMapOfLELeft h (stabilizer (M ≃ₐ[K] M) Q) q)).1 =
        (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
          (A := A) (B := B) (C := C) (K := K) (M := M) H p Q q).1.under C' := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_galois_setup A K M B C H
  integral_closure_galois_setup A K M B C' H'
  intro q
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_natural p H C h C' q

end Equivalence

section Invariants

variable [IsDedekindDomain A] [Q.IsMaximal] [IsScalarTower A C B]

/-- The local degree of the contraction of `σ • Q` is the relative index of the
corresponding conjugate decomposition group. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_of_isIntegralClosure_eq_relIndex
    (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ((σ • Q).under C).ramificationIdx A * ((σ • Q).under C).inertiaDeg A =
      H.relIndex (MulAut.conj σ • stabilizer (M ≃ₐ[K] M) Q) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_local_degree_setup A K M B C H
  let _ : (σ • Q).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  rw [(Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex (σ • Q) H C),
    stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    TauCeti.map_conj_eq_conj_smul]

/-- The local degree of the prime attached to a double coset is the relative index of the
corresponding conjugate decomposition group. The representative `q.out` is immaterial because the
left-hand side depends only on the double coset. -/
theorem
    ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex
    : letI := IsIntegralClosure.MulSemiringAction A K M B
    ∀ q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)),
      (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
          (A := A) (B := B) (C := C) (K := K) (M := M) H p Q q : Ideal C).ramificationIdx A *
        (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
          (A := A) (B := B) (C := C) (K := K) (M := M) H p Q q : Ideal C).inertiaDeg A =
        H.relIndex (MulAut.conj q.out • stabilizer (M ≃ₐ[K] M) Q) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  intro q
  conv_lhs =>
    rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]
  exact ramificationIdx_mul_inertiaDeg_under_smul_of_isIntegralClosure_eq_relIndex H Q q.out

variable [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)]

/-- Under residue separability, the ramification index of the contraction of `σ • Q` is the
relative index of the corresponding conjugate inertia group. -/
theorem ramificationIdx_under_smul_of_isIntegralClosure_eq_relIndex_inertia
    (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ((σ • Q).under C).ramificationIdx A =
      H.relIndex (MulAut.conj σ • Q.inertia (M ≃ₐ[K] M)) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  integral_closure_local_degree_setup A K M B C H
  exact Q.ramificationIdx_under_smul_eq_relIndex_inertia H C σ

/-- Under residue separability, the ramification index of the prime attached to a double coset is
the relative index of the corresponding conjugate inertia group. The representative `q.out` is
immaterial because the left-hand side depends only on the double coset. -/
theorem ramificationIdx_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex_inertia :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ∀ q : DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)),
      (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
          (A := A) (B := B) (C := C) (K := K) (M := M) H p Q q : Ideal C).ramificationIdx A =
        H.relIndex (MulAut.conj q.out • Q.inertia (M ≃ₐ[K] M)) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  intro q
  conv_lhs =>
    rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]
  exact ramificationIdx_under_smul_of_isIntegralClosure_eq_relIndex_inertia H Q q.out

end Invariants

end Ideal

end
