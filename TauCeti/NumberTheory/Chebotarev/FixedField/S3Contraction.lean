/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.ExceptionalPrimes
public import TauCeti.NumberTheory.NumberField.SplittingField
import TauCeti.Algebra.Polynomial.XPowSubC
import TauCeti.FieldTheory.GaloisGroups.Cubic
import TauCeti.NumberTheory.NumberField.Cyclotomic.Ramification
import TauCeti.NumberTheory.NumberField.Frobenius.FixedField.Inertia
import TauCeti.NumberTheory.NumberField.Index.DedekindCriterion
import TauCeti.NumberTheory.NumberField.Index.RootField
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.NumberTheory.NumberField.Minpoly
import TauCeti.RingTheory.RootsOfUnity.Adjoin

/-!
# The exceptional prime in the S₃ contraction example

Let `L` be the splitting field of `X³ - 2` over `ℚ`, and let `E = ℚ(∛2)` be the fixed
field of the stabilizer of one root. This file constructs a prime of `E` above `2` that is
unramified in `L / E`, although the prime below it ramifies in `L / ℚ`. Consequently the primes
of `E` lying above `ramifiedPrimes ℚ L` strictly contain the primes that ramify in `L / E`.

The arithmetic has two parts. Dedekind's criterion and Kummer--Dedekind show that every prime
above `2` in `E` has ramification index three. On the other hand, adjoining the quotient of two
distinct roots gives a primitive cube root of unity, so `L / E` is `3`-cyclotomic and is
unramified above `2`.

The Galois group of `L / ℚ` has order six by `natCard_gal_X_pow_three_sub_two`, identifying this
as the `S₃` witness required by the fixed-field contraction.

## Main result

* `exists_mem_primesAboveRamifiedPrimes_not_mem_ramifiedPrimes_X_pow_three_sub_two`: the explicit
  strict-containment witness above `2`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9.
-/

open Polynomial IntermediateField MulAction
open scoped NumberField

namespace TauCeti

noncomputable section

private theorem rootElementMinpoly
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]
    {beta : L} (hbeta : beta ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L) :
    let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
    ∃ theta : NumberField.IntegralPrimitiveElement E,
      minpoly ℤ theta.1 = X ^ 3 - 2 := by
  have hbetaInt : IsIntegral ℤ beta := by
    refine ⟨X ^ 3 - 2, by monicity; norm_num, ?_⟩
    rw [← aeval_def]
    simpa only [map_sub, map_pow, aeval_X, map_ofNat] using (Polynomial.mem_rootSet.mp hbeta).2
  let thetaL : 𝓞 L := ⟨beta, hbetaInt⟩
  have hminQ : minpoly ℚ (thetaL : L) = X ^ 3 - 2 :=
    (minpoly.eq_of_irreducible_of_monic irreducible_X_pow_three_sub_two
      (Polynomial.mem_rootSet.mp hbeta).2 (by monicity; norm_num)).symm
  refine ⟨NumberField.rootIntegralPrimitiveElement (θ := thetaL) (hminQ ▸ hbeta), ?_⟩
  rw [NumberField.minpoly_rootIntegralPrimitiveElement]
  apply Polynomial.map_injective _ (algebraMap ℤ ℚ).injective_int
  rw [← NumberField.RingOfIntegers.minpoly_rat_coe, hminQ]
  simp

private theorem ramificationIdx_eq_three_of_minpoly_eq_X_pow_three_sub_two
    {K : Type*} [Field K] [NumberField K]
    (theta : NumberField.IntegralPrimitiveElement K)
    (hmin : minpoly ℤ theta.1 = X ^ 3 - C 2)
    (P : Ideal (𝓞 K)) [P.IsPrime] [P.LiesOver (Ideal.span {(2 : ℤ)})] :
    P.ramificationIdx ℤ = 3 := by
  let phi : Fin 1 → (ZMod 2)[X] := fun _ ↦ X
  let e : Fin 1 → ℕ := fun _ ↦ 3
  let Phi : Fin 1 → ℤ[X] := fun _ ↦ X
  let H : ℤ[X] := -1
  have hphi : ∀ i, Irreducible (phi i) := by
    intro _
    exact irreducible_X
  have hphim : ∀ i, (phi i).Monic := by
    intro _
    exact monic_X
  have hinj : Function.Injective phi := by
    intro i j _
    exact Subsingleton.elim i j
  have he : ∀ i, 0 < e i := by simp [e]
  have hPhi : ∀ i, (Phi i).map (Int.castRingHom (ZMod 2)) = phi i := by
    simp [Phi, phi]
  have hH : C (2 : ℤ) * H = minpoly ℤ theta.1 - ∏ i, Phi i ^ e i := by
    rw [hmin]
    simp [H, Phi, e]
  have hcrit : ∀ i, e i = 1 ∨ ¬ phi i ∣ H.map (Int.castRingHom (ZMod 2)) := by
    intro i
    right
    intro hdvd
    have hdegree := Polynomial.natDegree_le_of_dvd hdvd (by norm_num :
      H.map (Int.castRingHom (ZMod 2)) ≠ 0)
    simp [phi, H] at hdegree
  have hindex : ¬ 2 ∣ theta.index :=
    theta.not_dvd_index_of_forall_eq_one_or_not_dvd_map
      hphi hphim hinj he hPhi hH hcrit
  have hexp : ¬ 2 ∣ RingOfIntegers.exponent theta.1 := fun h ↦
    hindex (h.trans theta.exponent_dvd_index)
  obtain ⟨⟨q, hq⟩, hqP⟩ :=
    (NumberField.Ideal.primesOverSpanEquivMonicFactorsMod hexp).symm.surjective
      ⟨P, inferInstance, inferInstance⟩
  have hram := NumberField.Ideal.ramificationIdx_primesOverSpanEquivMonicFactorsMod_symm_apply'
    hexp hq
  rw [hqP] at hram
  rw [hram, hmin]
  have htwo : Int.castRingHom (ZMod 2) 2 = 0 := by decide
  have hmap : (X ^ 3 - C (2 : ℤ)).map (Int.castRingHom (ZMod 2)) = X ^ 3 := by
    simp only [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C, htwo,
      C_0, sub_zero]
  rw [hmap]
  have hqX : q = X := by
    rw [RingOfIntegers.monicFactorsMod, hmin, hmap, Multiset.mem_toFinset] at hq
    rw [irreducible_X.normalizedFactors_pow] at hq
    simpa [monic_X.normalize_eq_self] using hq
  rw [hqX]
  exact multiplicity_pow_self_of_prime prime_X 3

/-- A root of `X ^ 3 - 2` in a `ℚ`-algebra that is a domain has cube equal to `2`. -/
private theorem pow_three_eq_two_of_mem_rootSet
    {L : Type*} [CommRing L] [IsDomain L] [Algebra ℚ L] {x : L}
    (hx : x ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L) : x ^ 3 = 2 := by
  have h := (mem_rootSet_X_pow_sub_C (F := ℚ) (a := 2) (n := 3) (by norm_num)).mp
    (by simpa only [map_ofNat] using hx)
  simpa only [map_ofNat] using h

private theorem two_ne_zero_of_algebra_rat {L : Type*} [Field L] [Algebra ℚ L] :
    (2 : L) ≠ 0 := by
  simpa only [map_ofNat, map_zero] using
    (algebraMap ℚ L).injective.ne (by norm_num : (2 : ℚ) ≠ 0)

/-- The quotient of two distinct roots of `X ^ 3 - 2` is a primitive cube root of unity. -/
private theorem isPrimitiveRoot_div_of_mem_rootSet
    {L : Type*} [Field L] [Algebra ℚ L] {beta gamma : L}
    (hbeta : beta ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L)
    (hgamma : gamma ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L) (hne : gamma ≠ beta) :
    IsPrimitiveRoot (gamma / beta) 3 := by
  have hbeta3 := pow_three_eq_two_of_mem_rootSet hbeta
  have hbeta0 : beta ≠ 0 := by
    rintro rfl
    exact two_ne_zero_of_algebra_rat (by simpa using hbeta3.symm)
  have hzeta3 : (gamma / beta) ^ 3 = 1 := by
    rw [div_pow, pow_three_eq_two_of_mem_rootSet hgamma, hbeta3,
      div_self two_ne_zero_of_algebra_rat]
  have hzeta1 : gamma / beta ≠ 1 := fun hz ↦ hne ((div_eq_one_iff_eq hbeta0).mp hz)
  refine IsPrimitiveRoot.mk_of_lt _ (by decide) hzeta3 fun l hl hlt ↦ ?_
  interval_cases l
  · simpa only [pow_one] using hzeta1
  · intro hzeta2
    apply hzeta1
    calc
      gamma / beta = (gamma / beta) ^ 3 := by rw [pow_succ, hzeta2, one_mul]
      _ = 1 := hzeta3

/-- In the splitting field of `X ^ 3 - 2`, the quotient of a root by a fixed root generates the
field over any intermediate field containing that fixed root. -/
private theorem adjoin_div_eq_top_of_mem
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [Polynomial.IsSplittingField ℚ L (X ^ 3 - 2 : ℚ[X])]
    {beta gamma : L} (E : IntermediateField ℚ L)
    (hbeta : beta ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L)
    (hgamma : gamma ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L) (hne : gamma ≠ beta)
    (hbetaE : beta ∈ E) :
    IntermediateField.adjoin E ({gamma / beta} : Set L) = ⊤ := by
  let _ : SMul ℚ E := E.algebra'.toSMul
  let _ : Algebra ℚ E := E.algebra'
  let _ : IsScalarTower ℚ E L := E.isScalarTower_mid'
  have hzeta := isPrimitiveRoot_div_of_mem_rootSet hbeta hgamma hne
  have hbeta3 := pow_three_eq_two_of_mem_rootSet hbeta
  have hbeta0 : beta ≠ 0 := by
    rintro rfl
    exact two_ne_zero_of_algebra_rat (by simpa using hbeta3.symm)
  have htopE : IntermediateField.adjoin E ((X ^ 3 - 2 : ℚ[X]).rootSet L) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ
      (isSplittingField_iff_intermediateField.mp inferInstance).2
  apply top_unique
  rw [← htopE]
  refine IntermediateField.adjoin_le_iff.mpr fun delta hdelta ↦ ?_
  have hmu : (delta / beta) ^ 3 = 1 := by
    rw [div_pow, pow_three_eq_two_of_mem_rootSet hdelta, hbeta3,
      div_self two_ne_zero_of_algebra_rat]
  have hbeta_mem : beta ∈ IntermediateField.adjoin E ({gamma / beta} : Set L) :=
    IntermediateField.algebraMap_mem _ (⟨beta, hbetaE⟩ : E)
  have := (IntermediateField.adjoin E ({gamma / beta} : Set L)).mul_mem hbeta_mem
    (hzeta.mem_adjoin_of_pow_eq_one hmu)
  rwa [mul_div_cancel₀ delta hbeta0] at this

private theorem isCyclotomicExtension_fixedField_stabilizer_root
    {L : Type*} [Field L] [Algebra ℚ L] [FiniteDimensional ℚ L]
    [Polynomial.IsSplittingField ℚ L (X ^ 3 - 2 : ℚ[X])]
    {beta gamma : L}
    (hbeta : beta ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L)
    (hgamma : gamma ∈ (X ^ 3 - 2 : ℚ[X]).rootSet L)
    (hne : gamma ≠ beta) :
    let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
    IsCyclotomicExtension {3} E L := by
  let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
  let _ : SMul ℚ E := E.algebra'.toSMul
  let _ : Algebra ℚ E := E.algebra'
  let _ : IsScalarTower ℚ E L := E.isScalarTower_mid'
  let _ : FiniteDimensional E L := IntermediateField.finiteDimensional_right E
  have hzeta := isPrimitiveRoot_div_of_mem_rootSet hbeta hgamma hne
  have hadjoin := adjoin_div_eq_top_of_mem E hbeta hgamma hne (mem_fixedField_stabilizer beta)
  have _ := hzeta.intermediateField_adjoin_isCyclotomicExtension E
  exact IsCyclotomicExtension.equiv (S := {3}) (A := E) (B := E⟮gamma / beta⟯) (C := L)
    ((IntermediateField.equivOfEq hadjoin).trans IntermediateField.topEquiv)

open IsDedekindDomain (HeightOneSpectrum)

/-- The splitting field of `X ^ 3 - 2` contains two distinct roots of it. -/
private theorem exists_ne_mem_rootSet_X_pow_three_sub_two :
    ∃ beta gamma : (X ^ 3 - 2 : ℚ[X]).SplittingField,
      beta ∈ (X ^ 3 - 2 : ℚ[X]).rootSet (X ^ 3 - 2 : ℚ[X]).SplittingField ∧
      gamma ∈ (X ^ 3 - 2 : ℚ[X]).rootSet (X ^ 3 - 2 : ℚ[X]).SplittingField ∧ gamma ≠ beta := by
  let f : ℚ[X] := X ^ 3 - 2
  have hsep : f.Separable := irreducible_X_pow_three_sub_two.separable
  have hcard : Fintype.card (f.rootSet f.SplittingField) = 3 := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits f)]
    dsimp [f]
    compute_degree
    norm_num
  let rootsEquiv : f.rootSet f.SplittingField ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  refine ⟨(rootsEquiv.symm 0).1, (rootsEquiv.symm 1).1, (rootsEquiv.symm 0).2,
    (rootsEquiv.symm 1).2, fun h ↦ ?_⟩
  have : (1 : Fin 3) = 0 := rootsEquiv.symm.injective (Subtype.ext h)
  simp at this

/-- The prime `2` has a prime of the cubic root field above it with ramification index three. -/
private theorem exists_prime_liesOver_two_ramificationIdx_eq_three
    {K : Type*} [Field K] [NumberField K] (theta : NumberField.IntegralPrimitiveElement K)
    (hmin : minpoly ℤ theta.1 = X ^ 3 - C 2) :
    ∃ P : Ideal (𝓞 K), P.IsPrime ∧ P.LiesOver (Ideal.span {(2 : ℤ)}) ∧
      P.ramificationIdx ℤ = 3 := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : (Ideal.span {(2 : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime 2
  let _ : (Ideal.span {(2 : ℤ)}).IsPrime :=
    (inferInstance : (Ideal.span {(2 : ℤ)}).IsMaximal).isPrime
  let P0 : (Ideal.span {(2 : ℤ)}).primesOver (𝓞 K) := Classical.choice inferInstance
  exact ⟨P0.1, P0.2.1, P0.2.2,
    ramificationIdx_eq_three_of_minpoly_eq_X_pow_three_sub_two theta hmin P0.1⟩

/-- A prime `P` of a cyclotomic Galois subextension above `2` with ramification index three is a
prime above a ramified prime that does not ramify in the extension. -/
private theorem exists_mem_primesAboveRamifiedPrimes_not_mem_ramifiedPrimes_of_isCyclotomic
    {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L] (E : IntermediateField ℚ L)
    [IsGalois E L] (hcyc : IsCyclotomicExtension {3} E L) (P : Ideal (𝓞 E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(2 : ℤ)})] (hramP : P.ramificationIdx ℤ = 3) :
    ∃ P : HeightOneSpectrum (𝓞 E),
      P.asIdeal.under ℤ = Ideal.span {(2 : ℤ)} ∧
        P ∈ NumberField.Chebotarev.primesAboveRamifiedPrimes ℚ L E ∧
          P ∉ NumberField.Chebotarev.ramifiedPrimes E L := by
  let _ : IsScalarTower ℚ E L := E.isScalarTower_mid'
  let p2 : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let Q0 : P.primesOver (𝓞 L) := Classical.choice inferInstance
  let Q : Ideal (𝓞 L) := Q0.1
  let _ : Q.IsPrime := Q0.2.1
  let _ : Q.LiesOver P := Q0.2.2
  let _ : Q.LiesOver p2 := Ideal.LiesOver.trans Q P p2
  have hthree : (3 : 𝓞 E) ∉ P := by
    intro h
    have h' : (3 : ℤ) ∈ Ideal.span {(2 : ℤ)} :=
      (Ideal.mem_of_liesOver P p2 (3 : ℤ)).mpr (by simpa using h)
    rw [Ideal.mem_span_singleton] at h'
    norm_num at h'
  have hUnramified : Algebra.IsUnramifiedAt (𝓞 E) Q :=
    IsCyclotomicExtension.isUnramifiedAt_of_natCast_notMem L 3 hthree Q
  let _ : Algebra.IsUnramifiedAt (𝓞 E) Q := hUnramified
  have hramQE : Q.ramificationIdx (𝓞 E) = 1 :=
    Ideal.ramificationIdx_eq_one_of_isUnramifiedAt
  have hramQ : Q.ramificationIdx ℤ = 3 := by
    rw [Ideal.ramificationIdx_tower P Q, hramP, hramQE, mul_one]
  have hp2ne : p2 ≠ ⊥ := by simp [p2]
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hp2ne Q
  let QQ : HeightOneSpectrum (𝓞 L) := ⟨Q, inferInstance, hQne⟩
  have hcardInertia : Nat.card (Q.inertia (L ≃ₐ[ℚ] L)) = 3 := by
    rw [Ideal.card_inertia_eq_ramificationIdx (𝓞 ℚ),
      Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q, hramQ]
  have hinertia : Q.inertia (L ≃ₐ[ℚ] L) ≠ ⊥ := by
    intro hbot
    rw [hbot] at hcardInertia
    simp at hcardInertia
  refine ⟨QQ.under (𝓞 E), ?_, ?_, ?_⟩
  · rw [HeightOneSpectrum.under_asIdeal, Ideal.under_under]
    exact (Q.over_def p2).symm
  · exact (NumberField.Chebotarev.under_mem_primesAboveRamifiedPrimes_iff_inertia_ne_bot
      (K := ℚ) (L := L) (E := E) QQ).mpr hinertia
  · exact (NumberField.Chebotarev.under_notMem_ramifiedPrimes_iff_isUnramifiedAt
      (K := E) (L := L) QQ).mpr hUnramified

public section

/-- In the splitting field of `X ^ 3 - 2`, a prime of a cubic root field above `2` belongs to
the fixed-field exceptional set even though it is unramified in the splitting field. -/
theorem exists_mem_primesAboveRamifiedPrimes_not_mem_ramifiedPrimes_X_pow_three_sub_two :
    let f : ℚ[X] := X ^ 3 - 2
    let L := f.SplittingField
    ∃ beta : L, beta ∈ f.rootSet L ∧
      let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
      ∃ P : HeightOneSpectrum (𝓞 E),
        P.asIdeal.under ℤ = Ideal.span {(2 : ℤ)} ∧
          P ∈ NumberField.Chebotarev.primesAboveRamifiedPrimes ℚ L E ∧
            P ∉ NumberField.Chebotarev.ramifiedPrimes E L := by
  let f : ℚ[X] := X ^ 3 - 2
  let L := f.SplittingField
  let _ : IsGalois ℚ L :=
    IsGalois.of_separable_splitting_field irreducible_X_pow_three_sub_two.separable
  obtain ⟨beta, gamma, hbeta, hgamma, hgammaBeta⟩ := exists_ne_mem_rootSet_X_pow_three_sub_two
  refine ⟨beta, hbeta, ?_⟩
  let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
  let _ : IsScalarTower ℚ E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L (stabilizer (L ≃ₐ[ℚ] L) beta)
  have hcyc : IsCyclotomicExtension {3} E L :=
    isCyclotomicExtension_fixedField_stabilizer_root hbeta hgamma hgammaBeta
  obtain ⟨theta, htheta⟩ := rootElementMinpoly hbeta
  obtain ⟨P, _, _, hramP⟩ :=
    exists_prime_liesOver_two_ramificationIdx_eq_three theta (by simpa using htheta)
  exact exists_mem_primesAboveRamifiedPrimes_not_mem_ramifiedPrimes_of_isCyclotomic E hcyc P
    hramP

end
end
end TauCeti
