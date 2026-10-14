/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Inertia
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
finite residue fields. The prime bijection and local-degree formula require no residue
separability; the separate ramification-index formula assumes it explicitly.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure`: the double-coset bijection for
  integral closures over a Dedekind base.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk`: the class of `σ` maps to the
  contraction of `σ • Q`.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_smul_of_isIntegralClosure_eq_relIndex`: the
  residue-separability-free `e * f` formula.
* `Ideal.ramificationIdx_under_smul_of_isIntegralClosure_eq_relIndex_inertia`: the
  residue-separable `e` formula.

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
  [IsFractionRing A K] [IsFractionRing B M]
  [IsIntegralClosure B A M]
  [IsDedekindDomain A] [IsGalois K M]

variable [FiniteDimensional K M]

variable (H : Subgroup (M ≃ₐ[K] M))
  [Algebra A C] [Algebra C ↥(fixedField H)] [Algebra C M]
  [IsScalarTower A C ↥(fixedField H)] [IsScalarTower C ↥(fixedField H) M]
  [IsScalarTower A C M]
  [IsFractionRing C ↥(fixedField H)] [IsIntegralClosure C A ↥(fixedField H)]
  [Algebra C B] [IsScalarTower C B M]

/-- The subgroup fixing an intermediate field is a Galois group for the corresponding
integral-closure extension. The action is the restriction of `Gal(M/K)` on `B`. -/
private theorem isGaloisGroup_integralClosure_fixedField :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    IsGaloisGroup H C B := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  let _ : IsDedekindDomain C :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K ↥(fixedField H) C
  let _ : Algebra.IsIntegral A C :=
    IsIntegralClosure.isIntegral_algebra A ↥(fixedField H)
  let _ : IsIntegralClosure B C M :=
    IsIntegralClosure.tower_top (R := A) (A := C) (B := M) (C := B)
  let _ : Algebra.IsIntegral C B := IsIntegralClosure.isIntegral_algebra C M
  let hsmall := IsIntegralClosure.MulSemiringAction C ↥(fixedField H) M B
  let _ := hsmall
  let _ : IsGaloisGroup (M ≃ₐ[↥(fixedField H)] M) C B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[↥(fixedField H)] M) C B ↥(fixedField H) M
  exact IsGaloisGroup.of_mulEquiv (subgroupEquivAlgEquiv H) fun h x ↦ by
    apply IsFractionRing.injective B M
    -- Expose the two integral-closure actions so their restrictions can be compared in `M`.
    change algebraMap B M (galRestrict C ↥(fixedField H) M B (subgroupEquivAlgEquiv H h) x) =
      algebraMap B M (galRestrict A K M B h.1 x)
    rw [algebraMap_galRestrict_apply, algebraMap_galRestrict_apply]
    rfl

omit [IsFractionRing B M] [IsGalois K M] [FiniteDimensional K M] in
include H in
/-- The map from the integral closure in a fixed field to the integral closure upstairs is
injective. -/
private theorem faithfulSMul_integralClosure_fixedField : FaithfulSMul C B := by
  rw [faithfulSMul_iff_algebraMap_injective]
  intro x y h
  apply IsFractionRing.injective C ↥(fixedField H)
  apply (algebraMap ↥(fixedField H) M).injective
  rw [← IsScalarTower.algebraMap_apply C ↥(fixedField H) M,
    ← IsScalarTower.algebraMap_apply C ↥(fixedField H) M]
  have h' := congrArg (algebraMap B M) h
  rw [← IsScalarTower.algebraMap_apply C B M,
    ← IsScalarTower.algebraMap_apply C B M] at h'
  exact h'

variable (p : Ideal A) (Q : Ideal B) [Q.IsMaximal] [Q.LiesOver p]

section Equivalence

variable [IsScalarTower A C B]

/-- **The double-coset splitting law over a Dedekind base.** For integral closures `B/A` and
`C/A` in `M/K` and `M^H/K`, respectively, the primes of `C` above `p` are indexed by the double
cosets of `H` and the decomposition group of `Q`. -/
noncomputable def doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    DoubleCoset.Quotient (H : Set (M ≃ₐ[K] M))
        (stabilizer (M ≃ₐ[K] M) Q : Set (M ≃ₐ[K] M)) ≃ p.primesOver C := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  let _ : FaithfulSMul C B := faithfulSMul_integralClosure_fixedField H
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A M
  let _ : IsGaloisGroup (M ≃ₐ[K] M) A B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) A B K M
  let _ : IsGaloisGroup H C B := isGaloisGroup_integralClosure_fixedField H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C

/-- The Dedekind double-coset law sends the class of `σ` to the contraction of `σ • Q`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    (Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure
      (A := A) (B := B) (C := C) (K := K) (M := M) H p Q
      (DoubleCoset.mk H _ σ) : Ideal C) = (σ • Q).under C := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  let _ : FaithfulSMul C B := faithfulSMul_integralClosure_fixedField H
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A M
  let _ : IsGaloisGroup (M ≃ₐ[K] M) A B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) A B K M
  let _ : IsGaloisGroup H C B := isGaloisGroup_integralClosure_fixedField H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk p H C σ

/-- The inverse of the Dedekind double-coset bijection sends a prime to the class of `σ`
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
  let _ : FaithfulSMul C B := faithfulSMul_integralClosure_fixedField H
  let _ : IsDedekindDomain C :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K ↥(fixedField H) C
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A M
  let _ : IsGaloisGroup (M ≃ₐ[K] M) A B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) A B K M
  let _ : IsGaloisGroup H C B := isGaloisGroup_integralClosure_fixedField H
  exact Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant_symm_apply_eq_mk_iff p H C q σ

end Equivalence

section Invariants

variable [Module.Finite A B] [Module.IsTorsionFree A B] [IsScalarTower A C B]

/-- The local degree of the contraction of `σ • Q` is the relative index of the
corresponding conjugate decomposition group. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_of_isIntegralClosure_eq_relIndex
    (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ((σ • Q).under C).ramificationIdx A * ((σ • Q).under C).inertiaDeg A =
      H.relIndex (MulAut.conj σ • stabilizer (M ≃ₐ[K] M) Q) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  let _ : IsDedekindDomain B :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K M B
  let _ : IsDedekindDomain C :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K ↥(fixedField H) C
  let _ : FaithfulSMul C B := faithfulSMul_integralClosure_fixedField H
  let _ : Module.IsTorsionFree C B := inferInstance
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A M
  let _ : IsGaloisGroup (M ≃ₐ[K] M) A B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) A B K M
  let _ : IsGaloisGroup H C B := isGaloisGroup_integralClosure_fixedField H
  let _ : (σ • Q).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  rw [(Ideal.ramificationIdx_mul_inertiaDeg_under_eq_relIndex (σ • Q) H C),
    stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    TauCeti.map_conj_eq_conj_smul]

variable [Algebra.IsSeparable (A ⧸ Q.under A) (B ⧸ Q)]

/-- Under residue separability, the ramification index of the contraction of `σ • Q` is the
relative index of the corresponding conjugate inertia group. -/
theorem ramificationIdx_under_smul_of_isIntegralClosure_eq_relIndex_inertia
    (σ : M ≃ₐ[K] M) :
    letI := IsIntegralClosure.MulSemiringAction A K M B
    ((σ • Q).under C).ramificationIdx A =
      H.relIndex (MulAut.conj σ • Q.inertia (M ≃ₐ[K] M)) := by
  let _ := IsIntegralClosure.MulSemiringAction A K M B
  let _ : IsDedekindDomain B :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K M B
  let _ : IsDedekindDomain C :=
    TauCeti.IsIntegralClosure.isDedekindDomain A K ↥(fixedField H) C
  let _ : FaithfulSMul C B := faithfulSMul_integralClosure_fixedField H
  let _ : Module.IsTorsionFree C B := inferInstance
  let _ : Algebra.IsIntegral A B := IsIntegralClosure.isIntegral_algebra A M
  let _ : IsGaloisGroup (M ≃ₐ[K] M) A B :=
    IsGaloisGroup.of_isFractionRing (M ≃ₐ[K] M) A B K M
  let _ : IsGaloisGroup H C B := isGaloisGroup_integralClosure_fixedField H
  exact Q.ramificationIdx_under_smul_eq_relIndex_inertia H C σ

end Invariants

end Ideal

end
