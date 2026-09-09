/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.GenusCharacter
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Ramification
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap
import TauCeti.NumberTheory.NumberField.Frobenius.Tower
import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.NarrowClassGroup
import TauCeti.NumberTheory.Multiquadratic.Legendre.PrimeDiscriminants

/-!
# The genus-field isomorphism on Artin symbols

For a squarefree nonsquare integer \(d\), the candidate genus field is an unramified abelian
extension of its embedded quadratic base \(K = \mathbb{Q}(\sqrt d)\). The isomorphism

\[
  \operatorname{Gal}(K_{\mathrm{gen}}/K) \cong \mathrm{Cl}^+(K)/\mathrm{Cl}^+(K)^2
\]

constructed from sign patterns and genus characters agrees with the inverse Artin map on every
degree-one prime above an odd rational prime away from the discriminant. Namely, the Frobenius at
such a prime is sent to the elementary-2 class of that prime.

This module exposes the local compatibility between relative Frobenius elements and singleton
genus characters: both associate to each prime discriminant the same quadratic character value.
Consequently, the sign-pattern isomorphism identifies Frobenius and Artin elements with the
elementary-2 narrow ideal classes of the primes below them.

This is the local compatibility that determines the Artin map on ideals. The classical account is
in D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and F. Lemmermeyer,
*Reciprocity Laws: From Euler to Eisenstein*, §2.2.

## Main results

* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius`:
  the genus-field isomorphism sends a relative Frobenius to the class of its degree-one prime.
* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_artinElement`:
  the same statement for the canonical Artin automorphism.
-/

public section

open NumberField
open scoped IsMulCommutative NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- Relative automorphisms of the candidate genus field commute because their restrictions to
the abelian Galois group over `ℚ` commute. -/
theorem candidateGenusFieldRelativeAut_comm (hd : Squarefree d)
    (σ τ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd) :
    σ * τ = τ * σ := by
  apply AlgEquiv.restrictScalars_injective ℚ
  exact IsMulCommutative.is_comm.comm (σ.restrictScalars ℚ) (τ.restrictScalars ℚ)

/-- **The genus-field isomorphism sends Frobenius to the prime class.**
Let q be an odd rational prime not dividing the discriminant of K = ℚ(√d), let qIdeal be a
degree-one prime of K above q, and let Q be a prime of the candidate genus field above qIdeal.
Every relative arithmetic Frobenius σ at Q is sent by the genus-field isomorphism to the class
of qIdeal in the maximal elementary-2 quotient of the narrow class group. -/
theorem autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (hqD : ¬ (q : ℤ) ∣ fundamentalDiscriminant d)
    (qIdeal : Ideal (𝓞 (candidateGenusFieldBase hd)))
    (hnorm : Ideal.absNorm qIdeal = q)
    (Q : Ideal (𝓞 (candidateGenusField hd))) [Q.LiesOver qIdeal]
    (σ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
    (hσ : IsArithFrobAt (𝓞 (candidateGenusFieldBase hd)) σ Q) :
    autCandidateGenusFieldEquivNarrowElementaryTwoQuotient hd hnsq σ =
      Multiplicative.ofAdd
        (TauCeti.elementaryTwoQuotientMk
          (NarrowClassGroup.mk0
            ⟨qIdeal, by
              rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors, hnorm]
              exact (Fact.out : q.Prime).ne_zero⟩)) := by
  have hprimeNorm : (Ideal.absNorm qIdeal).Prime := by
    rw [hnorm]
    exact Fact.out
  let _ : qIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprimeNorm
  let _ : qIdeal.LiesOver (Ideal.span {(q : ℤ)}) := ⟨by
    simpa [hnorm, Ideal.under_def] using
      Ideal.span_singleton_absNorm (I := qIdeal) hprimeNorm⟩
  have hqIdeal : qIdeal ∈ (Ideal (𝓞 (candidateGenusFieldBase hd)))⁰ := by
    rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors, hnorm]
    exact (Fact.out : q.Prime).ne_zero
  have hcop : IsCoprime (q : ℤ) (∏ P ∈ genusPrimeDiscriminants hd, P) := by
    rw [(genusPrimeDiscriminants_spec hd).2.2]
    exact (Nat.prime_iff_prime_int.mp Fact.out).coprime_iff_not_dvd.mpr hqD
  let _ : Q.LiesOver (Ideal.span {(q : ℤ)}) :=
    Ideal.LiesOver.trans Q qIdeal (Ideal.span {(q : ℤ)})
  have hσint : IsArithFrobAt ℤ (σ.restrictScalars ℚ) Q :=
    NumberField.isArithFrobAt_int_of_absNorm_eq qIdeal hnorm Q hσ
  have heq :
      (narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).symm
          ⟨candidateGenusFieldRelativeSignPattern hd σ,
            candidateGenusFieldRelativeSignPattern_mem hd σ⟩ =
        TauCeti.elementaryTwoQuotientMk
          (NarrowClassGroup.mk0 ⟨qIdeal, hqIdeal⟩) := by
    apply (narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).injective
    rw [(narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).apply_symm_apply]
    apply Subtype.ext
    have hsignCoe :
        (↑(⟨candidateGenusFieldRelativeSignPattern hd σ,
            candidateGenusFieldRelativeSignPattern_mem hd σ⟩ :
          ↑(candidateGenusFieldRelativeSignSubmodule hd)) :
            {P // P ∈ genusPrimeDiscriminants hd} → ZMod 2) =
          candidateGenusFieldRelativeSignPattern hd σ := rfl
    rw [hsignCoe, narrowElementaryTwoQuotientEquivRelativeSign_apply_coe]
    funext P
    let u : ℤˣ :=
      genusCharFunNarrowClassGroupHom
        (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
        (genusPrimeDiscriminants_spec hd).2.2
        (minpoly_candidateGenusFieldBaseGen hd hnsq)
        (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd
        (Finset.singleton_subset_iff.mpr P.property)
        (NarrowClassGroup.mk0 ⟨qIdeal, hqIdeal⟩)
    rw [candidateGenusFieldBaseGenusCharLinearMap_apply,
      genusCharFunElementaryTwoQuotientFamilyLinearMap_apply,
      genusCharFunElementaryTwoQuotientLinearMap_mk,
      candidateGenusFieldRelativeSignPattern_apply,
      TauCeti.additiveIntUnitsLinearEquiv_apply]
    -- The two sign encodings are definitionally if-expressions; name the genus-character unit
    -- above so their equality reduces to equivalence of their respective fixed-sign tests.
    change (if σ (candidateGenusFieldGen hd P) = candidateGenusFieldGen hd P then 0 else 1) =
      if u = 1 then 0 else 1
    have hqRadicand : ¬ (q : ℤ) ∣ primeDiscriminantRadicand P.val := by
      intro hdiv
      apply hqD
      exact ((dvd_primeDiscriminant_iff_dvd_radicand P.val hodd).mpr hdiv).trans
        ((genusPrimeDiscriminants_spec hd).2.2 ▸
          Finset.dvd_prod_of_mem (fun P => P) P.property)
    have hroot : candidateGenusFieldGen hd P ^ 2 =
        algebraMap ℤ (candidateGenusField hd) (primeDiscriminantRadicand P.val) := by
      rw [candidateGenusFieldGen_sq]
      simp
    have hfix :
        σ (candidateGenusFieldGen hd P) = candidateGenusFieldGen hd P ↔
          legendreSym q (primeDiscriminantRadicand P.val) = 1 :=
      NumberField.isArithFrobAt_apply_sqrt_eq_self_iff
        hodd hqRadicand hroot Q hσint
    have hchar : (u : ℤ) =
          legendreSym q (primeDiscriminantRadicand P.val) := by
      dsimp only [u]
      rw [genusCharFunNarrowClassGroupHom_mk0_eq_primeDiscriminantCharFun_absNorm
        (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
        (genusPrimeDiscriminants_spec hd).2.2
        (minpoly_candidateGenusFieldBaseGen hd hnsq)
        (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd qIdeal hqIdeal P.val P.property (by
          rw [hnorm]
          exact IsCoprime.prod_right_iff.mp hcop P.val P.property),
        hnorm,
        primeDiscriminantCharFun_eq_legendreSym
          ((genusPrimeDiscriminants_spec hd).1 P.val P.property) hodd,
        legendreSym_eq_legendreSym_primeDiscriminantRadicand P.val hodd]
    have hunit :
        u = 1 ↔ legendreSym q (primeDiscriminantRadicand P.val) = 1 := by
      rw [← Units.val_eq_one, hchar]
    simp only [hfix, hunit]
  rw [autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_apply]
  exact congrArg (fun x : NarrowClassGroup.ElementaryTwoQuotient
    (candidateGenusFieldBase hd) => Multiplicative.ofAdd x) heq

/-- **The genus-field isomorphism sends the Artin automorphism to the prime class.**
Under the hypotheses of the Frobenius theorem, the canonical Artin element at qIdeal maps to the
elementary-2 class of qIdeal. Thus the sign-pattern/genus-character isomorphism agrees locally
with the inverse ideal-theoretic Artin map. -/
theorem autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_artinElement
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    {q : ℕ} [Fact q.Prime] (hodd : q ≠ 2)
    (hqD : ¬ (q : ℤ) ∣ fundamentalDiscriminant d)
    (qIdeal : Ideal (𝓞 (candidateGenusFieldBase hd)))
    (hnorm : Ideal.absNorm qIdeal = q) :
    let hprimeNorm : (Ideal.absNorm qIdeal).Prime := by
      rw [hnorm]
      exact Fact.out
    let _ : qIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprimeNorm
    let _ : qIdeal.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (by
      intro hbot
      rw [hbot, Ideal.absNorm_bot] at hnorm
      exact (Fact.out : q.Prime).ne_zero hnorm.symm)
    autCandidateGenusFieldEquivNarrowElementaryTwoQuotient hd hnsq
        (NumberFieldArithmetic.artinElement
          (candidateGenusFieldRelativeAut_comm hd) qIdeal
          (fun Q hQ hQl =>
            (isUnramifiedIn_candidateGenusField hd hnsq qIdeal) Q hQ hQl)) =
      Multiplicative.ofAdd
        (TauCeti.elementaryTwoQuotientMk
          (NarrowClassGroup.mk0
            ⟨qIdeal, by
              rw [← Ideal.absNorm_ne_zero_iff_mem_nonZeroDivisors, hnorm]
              exact (Fact.out : q.Prime).ne_zero⟩)) := by
  have hprimeNorm : (Ideal.absNorm qIdeal).Prime := by
    rw [hnorm]
    exact Fact.out
  let _ : qIdeal.IsPrime := Ideal.isPrime_of_irreducible_absNorm hprimeNorm
  let _ : qIdeal.LiesOver (Ideal.span {(q : ℤ)}) := ⟨by
    simpa [hnorm, Ideal.under_def] using
      Ideal.span_singleton_absNorm (I := qIdeal) hprimeNorm⟩
  let _ : qIdeal.IsMaximal := Ideal.IsPrime.isMaximal inferInstance (by
    intro hbot
    rw [hbot, Ideal.absNorm_bot] at hnorm
    exact (Fact.out : q.Prime).ne_zero hnorm.symm)
  obtain ⟨Q, hQprime, hQlies⟩ :=
    (inferInstance :
      Nonempty (qIdeal.primesOver (𝓞 (candidateGenusField hd))))
  let _ : Q.IsPrime := hQprime
  let _ : Q.LiesOver qIdeal := hQlies
  apply autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius
    hd hnsq hodd hqD qIdeal hnorm Q
  exact NumberFieldArithmetic.isArithFrobAt_artinElement
    (candidateGenusFieldRelativeAut_comm hd) qIdeal
      (fun Q hQ hQl =>
        (isUnramifiedIn_candidateGenusField hd hnsq qIdeal) Q hQ hQl) Q

end TauCeti.Multiquadratic
