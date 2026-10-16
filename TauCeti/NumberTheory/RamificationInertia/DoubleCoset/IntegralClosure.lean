/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.RingTheory.IsGaloisGroup.Dedekind
public import TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Inertia
public import TauCeti.RingTheory.IsGaloisGroup.IntegralClosure
public import TauCeti.RepresentationTheory.Induction.Mackey.Subgroup

/-!
# The double coset law over a Dedekind base

Let `A` be a domain with fraction field `K`, let `M / K` be a finite Galois extension with group
`G = Gal(M/K)`, and let `B` be the integral closure of `A` in `M`. For a subgroup `H` of `G`, let
`C` be the integral closure of `A` in the fixed field `M ^ H`, an intermediate field that need not
be Galois over `K`. Fix a prime `p` of `A` and a prime `Q` of `B` above it, with decomposition
group `D`. The primes of `C` above `p` are indexed by the double cosets `H \ G / D`, the class of
`σ` corresponding to the contraction `σ Q ∩ C`.

This is the double coset law for an arbitrary integrally closed base, with no hypothesis on the
residue fields. Over a Dedekind base the local invariants of the prime `𝔮_σ = σ Q ∩ C` are read
off the double coset:

* `e(𝔮_σ / p) · f(𝔮_σ / p) = [σDσ⁻¹ : H ∩ σDσ⁻¹]`, so that `e · f · |H| = |HσD|`;
* `e(𝔮_σ / p) = [σIσ⁻¹ : H ∩ σIσ⁻¹]` when the residue extension at `Q` is separable, where `I` is
  the inertia group of `Q`;
* the products `e · f` sum, over `H \ G / D`, to `[M ^ H : K]`.

Finite residue fields are never assumed. The statements specialize the invariant-ring double
coset law of `TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Basic` and
`TauCeti.NumberTheory.RamificationInertia.DoubleCoset.Invariant.Inertia`: the work here is to
recognize `G` and `H` as Galois groups of the integral closures, via
`IsGaloisGroup.of_isIntegralClosure` and `IsGaloisGroup.of_isIntegralClosure_fixedField`,
and to supply the finiteness and flatness that a Dedekind base provides, via
`IsIntegralClosure.finite` and `TauCeti.IsIntegralClosure.flat`. Rings of integers of
number fields are the case `A = 𝓞 K`, `B = 𝓞 M`, `C = 𝓞 (M ^ H)`.

## Main definitions

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure`: the bijection
  `H \ G / D ≃ p.primesOver C`.

## Main results

* `Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk`: the class of `σ` is sent to
  `σ Q ∩ C`.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex_of_isIntegralClosure`:
  `e · f = [σDσ⁻¹ : H ∩ σDσ⁻¹]`.
* `Ideal.ramificationIdx_mul_inertiaDeg_under_smul_mul_card_of_isIntegralClosure`:
  `e · f · |H| = |HσD|`.
* `Ideal.ramificationIdx_under_smul_eq_relIndex_inertia_of_isIntegralClosure`:
  `e = [σIσ⁻¹ : H ∩ σIσ⁻¹]` for a separable residue extension.
* `Ideal.sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsIntegralClosure_eq_finrank`: the
  fundamental identity `Σ e · f = [M ^ H : K]` indexed by double cosets.

The same canonical API also includes naturality under enlarging the subgroup and equivariance
under translating the chosen prime, together with the decomposition-group and inertia-group
formulas evaluated directly on a double coset. Naturality and equivariance only require an
integrally closed base; the local-invariant formulas require a Dedekind base.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9, page 55.
* G. J. Janusz, *Algebraic Number Fields*, Chapter I.
-/

public section

open IntermediateField MulAction
open scoped Pointwise

namespace Ideal

variable {A K M B : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [Field M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M] [Algebra A M] [IsScalarTower A K M]
  [CommRing B] [Algebra A B] [Algebra B M] [IsScalarTower A B M] [IsIntegralClosure B A M]
  [MulSemiringAction Gal(M/K) B] [SMulDistribClass Gal(M/K) B M]

variable (Q : Ideal B) [Q.IsPrime] (p : Ideal A) [Q.LiesOver p]
  (H : Subgroup Gal(M/K)) [Algebra A (fixedField H)] [IsScalarTower A K (fixedField H)]
  (C : Type*) [CommRing C] [Algebra A C] [Algebra C (fixedField H)]
  [IsScalarTower A C (fixedField H)]
  [IsIntegralClosure C A (fixedField H)]
  [Algebra C B] [Algebra C M] [IsScalarTower A C B] [IsScalarTower C (fixedField H) M]
  [IsScalarTower C B M]

section Bijection

variable [IsDomain A] [IsIntegrallyClosed A]

/-- **The double coset law over an integrally closed base.** For `M / K` finite Galois with
group `G`, a subgroup `H` of `G`, the integral closures `B` and `C` of `A` in `M` and in `M ^ H`,
and a prime `Q` of `B` above `p` with decomposition group `D`, the primes of `C` above `p` are
indexed by the double cosets `H \ G / D`.

The class of `σ` corresponds to the contraction `σ Q ∩ C`, by
`Ideal.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk`. -/
noncomputable def doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure :
    DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K)) ≃
      p.primesOver C :=
  have := IsGaloisGroup.of_isIntegralClosure Gal(M/K) A B K M
  have := (TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C).1
  have := (TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C).2
  Q.doubleCosetQuotientEquivPrimesOverOfIsInvariant p H C

/-- The double coset law sends the class of `σ` to the contraction `σ Q ∩ C`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk (σ : Gal(M/K)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C
      (DoubleCoset.mk H _ σ) : Ideal C) = (σ • Q).under C := by
  have := IsGaloisGroup.of_isIntegralClosure Gal(M/K) A B K M
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  rw [doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure,
    doubleCosetQuotientEquivPrimesOverOfIsInvariant_mk]

/-- The inverse of the double coset law sends a prime `q` to the class of `σ` exactly when `q` is
the contraction `σ Q ∩ C`. -/
@[simp]
theorem doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_symm_apply_eq_mk_iff
    (q : p.primesOver C) (σ : Gal(M/K)) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C).symm q =
        DoubleCoset.mk H _ σ ↔ q.1 = (σ • Q).under C := by
  rw [Equiv.symm_apply_eq, Subtype.ext_iff,
    doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]

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

section Dedekind

variable [IsDedekindDomain A]

omit [Q.IsPrime] in
/-- **The local degree of `σ Q ∩ C` is an index of decomposition groups**:
`e · f = [σDσ⁻¹ : H ∩ σDσ⁻¹]`, where `D` is the decomposition group of the maximal ideal `Q`.
No separability of the residue extension is needed. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex_of_isIntegralClosure
    [Q.IsMaximal] (σ : Gal(M/K)) :
    ((σ • Q).under C).ramificationIdx A * ((σ • Q).under C).inertiaDeg A =
      H.relIndex (MulAut.conj σ • stabilizer Gal(M/K) Q) := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  obtain ⟨_, _, _⟩ := TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField
    (A := A) (K := K) (M := M) H C
  have : (σ • Q).IsMaximal := by
    rw [pointwise_smul_eq_comap]
    infer_instance
  rw [ramificationIdx_mul_inertiaDeg_under_eq_relIndex (σ • Q) H C,
    stabilizer_smul_eq_stabilizer_map_conj, MulEquiv.toMonoidHom_eq_coe,
    TauCeti.map_conj_eq_conj_smul]

omit [Q.IsPrime] in
/-- **The local degree of `σ Q ∩ C` counts the double coset `HσD`**: `e · f · |H| = |HσD|`,
where `D` is the decomposition group of the maximal ideal `Q`. -/
theorem ramificationIdx_mul_inertiaDeg_under_smul_mul_card_of_isIntegralClosure
    [Q.IsMaximal] (σ : Gal(M/K)) :
    ((σ • Q).under C).ramificationIdx A * ((σ • Q).under C).inertiaDeg A * Nat.card H =
      Nat.card (DoubleCoset.doubleCoset σ (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q)) := by
  rw [ramificationIdx_mul_inertiaDeg_under_smul_eq_relIndex_of_isIntegralClosure Q H C,
    TauCeti.card_doubleCoset_eq_card_mul_relIndex, mul_comm]

omit [Q.IsPrime] in
/-- **The ramification index of `σ Q ∩ C` is an index of inertia groups**:
`e = [σIσ⁻¹ : H ∩ σIσ⁻¹]`, where `I` is the inertia group of the maximal ideal `Q`, provided the
residue extension of `Q` over `p` is separable. The residue fields need not be finite. -/
theorem ramificationIdx_under_smul_eq_relIndex_inertia_of_isIntegralClosure [Q.IsMaximal]
    [Algebra.IsSeparable (A ⧸ p) (B ⧸ Q)] (σ : Gal(M/K)) :
    ((σ • Q).under C).ramificationIdx A = H.relIndex (MulAut.conj σ • Q.inertia Gal(M/K)) := by
  obtain ⟨_, _, _, _⟩ :=
    TauCeti.IsIntegralClosure.isDomain_and_finite_and_flat_and_isGaloisGroup
      (A := A) (K := K) (M := M) (B := B)
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  obtain ⟨_, _, _⟩ := TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField
    (A := A) (K := K) (M := M) H C
  obtain rfl := Q.over_def p
  exact ramificationIdx_under_smul_eq_relIndex_inertia Q H C σ

/-- **The fundamental identity in double-coset coordinates.** The ramification indices times the
residue degrees of the primes of `C` above `p`, indexed by `H \ G / D`, sum to `[M ^ H : K]`. -/
theorem sum_ramificationIdx_mul_inertiaDeg_doubleCosetOfIsIntegralClosure_eq_finrank :
    (∑ᶠ q : DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K)),
      (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).ramificationIdx
          A *
        (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).inertiaDeg
          A) =
      Module.finrank K (fixedField H) := by
  classical
  obtain ⟨_, _⟩ := TauCeti.IsIntegralClosure.isGaloisGroup_fixedField_and_faithfulSMul
    (A := A) (B := B) H C
  obtain ⟨_, _, _⟩ := TauCeti.IsIntegralClosure.isDedekindDomain_and_finite_and_flat_fixedField
    (A := A) (K := K) (M := M) H C
  have : p.IsPrime := isPrime_of_liesOver Q p
  let e := Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C
  let _ := Fintype.ofFinite
    (DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K)))
  let _ : Fintype (p.primesOver C) := Fintype.ofEquiv _ e
  have : IsFractionRing C (fixedField H) :=
    IsIntegralClosure.isFractionRing_of_finite_extension A K (fixedField H) C
  rw [finsum_eq_sum_of_fintype, e.sum_comp fun q : p.primesOver C ↦
      q.1.ramificationIdx A * q.1.inertiaDeg A, sum_ramification_inertia_eq_finrank p C,
    IsFractionRing.finrank_eq A K C (fixedField H)]

/-- The local degree of the prime attached to a double coset is the relative index of its
conjugate decomposition group. Residue separability is not required. -/
theorem
    ramificationIdx_mul_inertiaDeg_doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_eq_relIndex
    [Q.IsMaximal]
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
    [Q.IsMaximal] [Algebra.IsSeparable (A ⧸ p) (B ⧸ Q)]
    (q : DoubleCoset.Quotient (H : Set Gal(M/K)) (stabilizer Gal(M/K) Q : Set Gal(M/K))) :
    (Q.doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure p H C q : Ideal C).ramificationIdx A =
      H.relIndex (MulAut.conj q.out • Q.inertia Gal(M/K)) := by
  conv_lhs =>
    rw [← DoubleCoset.out_eq' q, doubleCosetQuotientEquivPrimesOverOfIsIntegralClosure_mk]
  exact Q.ramificationIdx_under_smul_eq_relIndex_inertia_of_isIntegralClosure p H C q.out


end Dedekind

end Ideal
