/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.FixedField.ExceptionalPrimes
public import TauCeti.NumberTheory.NumberField.SplittingField
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
    intro i
    exact irreducible_X
  have hphim : ∀ i, (phi i).Monic := by
    intro i
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
  let zeta : L := gamma / beta
  have hbeta3 : beta ^ 3 = 2 := by
    rw [Polynomial.mem_rootSet] at hbeta
    apply sub_eq_zero.mp
    simpa only [map_sub, map_pow, aeval_X, map_ofNat] using hbeta.2
  have hgamma3 : gamma ^ 3 = 2 := by
    rw [Polynomial.mem_rootSet] at hgamma
    apply sub_eq_zero.mp
    simpa only [map_sub, map_pow, aeval_X, map_ofNat] using hgamma.2
  have htwo : (2 : L) ≠ 0 := by
    intro h
    have h' : (algebraMap ℚ L) (2 : ℚ) = (algebraMap ℚ L) 0 := by
      simpa using h
    exact (by norm_num : (2 : ℚ) ≠ 0) ((algebraMap ℚ L).injective h')
  have hbeta0 : beta ≠ 0 := by
    intro hb
    rw [hb, zero_pow (by decide : 3 ≠ 0)] at hbeta3
    exact htwo hbeta3.symm
  have hzeta3 : zeta ^ 3 = 1 := by
    dsimp [zeta]
    rw [div_pow, hgamma3, hbeta3, div_self htwo]
  have hzeta1 : zeta ≠ 1 := by
    intro hz
    exact hne ((div_eq_one_iff_eq hbeta0).mp hz)
  have hzeta : IsPrimitiveRoot zeta 3 := by
    apply IsPrimitiveRoot.mk_of_lt zeta (by decide) hzeta3
    intro l hl hlt
    interval_cases l
    · simpa only [pow_one] using hzeta1
    · intro hzeta2
      apply hzeta1
      calc
        zeta = zeta ^ 3 := by rw [pow_succ, hzeta2, one_mul]
        _ = 1 := hzeta3
  have hadjoin : IntermediateField.adjoin E ({zeta} : Set L) = ⊤ := by
    have htop : IntermediateField.adjoin ℚ ((X ^ 3 - 2 : ℚ[X]).rootSet L) = ⊤ :=
      (isSplittingField_iff_intermediateField.mp inferInstance).2
    have htopE : IntermediateField.adjoin E ((X ^ 3 - 2 : ℚ[X]).rootSet L) = ⊤ :=
      IntermediateField.adjoin_eq_top_of_adjoin_eq_top ℚ htop
    apply top_unique
    rw [← htopE]
    apply IntermediateField.adjoin_le_iff.mpr
    intro delta hdelta
    have hdelta3 : delta ^ 3 = 2 := by
      rw [Polynomial.mem_rootSet] at hdelta
      apply sub_eq_zero.mp
      simpa only [map_sub, map_pow, aeval_X, map_ofNat] using hdelta.2
    have hmu : (delta / beta) ^ 3 = 1 := by
      rw [div_pow, hdelta3, hbeta3, div_self htwo]
    have hmu_mem : delta / beta ∈ IntermediateField.adjoin E ({zeta} : Set L) :=
      hzeta.mem_adjoin_of_pow_eq_one hmu
    have hbeta_mem : beta ∈ IntermediateField.adjoin E ({zeta} : Set L) := by
      exact IntermediateField.algebraMap_mem _
        (⟨beta, mem_fixedField_stabilizer beta⟩ : E)
    have := (IntermediateField.adjoin E ({zeta} : Set L)).mul_mem hbeta_mem hmu_mem
    rwa [mul_div_cancel₀ delta hbeta0] at this
  refine (IsCyclotomicExtension.iff_adjoin_eq_top {3} E L).mpr ⟨?_, ?_⟩
  · intro n hn hn0
    simp only [Set.mem_singleton_iff] at hn
    subst n
    exact ⟨zeta, hzeta⟩
  · rw [← IntermediateField.top_toSubalgebra, ← hadjoin,
      IntermediateField.adjoin_toSubalgebra_of_isAlgebraic]
    · apply le_antisymm
      · apply Algebra.adjoin_le
        rintro x ⟨n, hn, -, hx⟩
        simp only [Set.mem_singleton_iff] at hn
        subst n
        exact hzeta.mem_algebraAdjoin_of_pow_eq_one hx
      · apply Algebra.adjoin_le
        intro x hx
        simp only [Set.mem_singleton_iff] at hx
        subst x
        apply Algebra.subset_adjoin
        exact ⟨3, Set.mem_singleton 3, by decide, hzeta.pow_eq_one⟩
    · intro x hx
      exact Algebra.IsAlgebraic.isAlgebraic x

open IsDedekindDomain (HeightOneSpectrum)

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
  have hsep : f.Separable := by
    dsimp [f]
    exact irreducible_X_pow_three_sub_two.separable
  let _ : IsGalois ℚ L := IsGalois.of_separable_splitting_field hsep
  have hcard : Fintype.card (f.rootSet L) = 3 := by
    rw [Polynomial.card_rootSet_eq_natDegree hsep (SplittingField.splits f)]
    dsimp [f]
    compute_degree
    norm_num
  let rootsEquiv : f.rootSet L ≃ Fin 3 := Fintype.equivFinOfCardEq hcard
  let betaRoot : f.rootSet L := rootsEquiv.symm 0
  let gammaRoot : f.rootSet L := rootsEquiv.symm 1
  let beta : L := betaRoot.1
  let gamma : L := gammaRoot.1
  have hbeta : beta ∈ f.rootSet L := betaRoot.2
  have hgamma : gamma ∈ f.rootSet L := gammaRoot.2
  have hgammaBeta : gamma ≠ beta := by
    intro h
    have hroots : gammaRoot = betaRoot := Subtype.ext h
    have : (1 : Fin 3) = 0 := rootsEquiv.symm.injective hroots
    simp at this
  refine ⟨beta, hbeta, ?_⟩
  let E := fixedField (stabilizer (L ≃ₐ[ℚ] L) beta)
  let _ : IsScalarTower ℚ E L := E.isScalarTower_mid'
  let _ : IsGalois E L := IsGalois.of_fixed_field L (stabilizer (L ≃ₐ[ℚ] L) beta)
  have hcyc : IsCyclotomicExtension {3} E L :=
    isCyclotomicExtension_fixedField_stabilizer_root
      (by simpa [f] using hbeta) (by simpa [f] using hgamma) hgammaBeta
  let _ : IsCyclotomicExtension {3} E L := hcyc
  obtain ⟨theta, htheta⟩ := rootElementMinpoly (by simpa [f] using hbeta)
  have hthetaC : minpoly ℤ theta.1 = X ^ 3 - C 2 := by
    simpa using htheta
  let p2 : Ideal ℤ := Ideal.span {(2 : ℤ)}
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : p2.IsMaximal := by
    dsimp [p2]
    exact Int.ideal_span_isMaximal_of_prime 2
  let _ : p2.IsPrime := by
    exact (inferInstance : p2.IsMaximal).isPrime
  let P0 : p2.primesOver (𝓞 E) := Classical.choice inferInstance
  let P : Ideal (𝓞 E) := P0.1
  let _ : P.IsPrime := P0.2.1
  let _ : P.LiesOver p2 := P0.2.2
  have hramP : P.ramificationIdx ℤ = 3 :=
    ramificationIdx_eq_three_of_minpoly_eq_X_pow_three_sub_two theta hthetaC P
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
      Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q hQne, hramQ]
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

end
end
end TauCeti
