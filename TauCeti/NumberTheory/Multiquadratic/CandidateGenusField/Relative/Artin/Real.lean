/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Artin.Basic
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Real

/-!
# Artin reciprocity for the real quadratic genus field

For positive squarefree nonsquare `d`, put `K = ℚ(√d)` and let `G` be the maximal totally real
subfield of the prime-discriminant compositum. The isomorphism
`autCandidateGenusFieldRealEquivElementaryTwoQuotient` carries the ideal Artin map of `G/K` to
the ordinary ideal class modulo squares. Thus its kernel consists exactly of ideals whose
ordinary classes are squares, and every automorphism is represented by an ideal.

The comparison holds on fractional ideals prime to `2 · disc K`. It follows by restricting the
Artin map of the full compositum and forgetting positivity on narrow ideal classes. In particular,
principal ideals need no sign condition for the real genus-field Artin map to vanish.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public section

open NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- The real genus-field isomorphism carries the Artin automorphism of an ideal to its ordinary
class modulo squares. The excluded set may be any finite set containing the primes above
`2 · disc K`. -/
theorem autCandidateGenusFieldRealEquivElementaryTwoQuotient_artinHomAway
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd))))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)),
      (TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d → v ∈ S)
    (I : NumberFieldArithmetic.idealsAway (K := candidateGenusFieldBase hd) S) :
    letI := candidateGenusFieldRealAlgebra hd hpos
    letI := candidateGenusFieldRealIsScalarTower hd hpos
    letI := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
    autCandidateGenusFieldRealEquivElementaryTwoQuotient hd hnsq hpos
        (NumberFieldArithmetic.artinHomAway (L := candidateGenusFieldReal hd)
          (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ)) S
          (isUnramifiedAway_of_intermediateField (candidateGenusFieldReal hd) S
            (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
              inferInstance inferInstance)) I) =
      Multiplicative.ofAdd (TauCeti.elementaryTwoQuotientMk
        (ClassGroup.mk (candidateGenusFieldBase hd)
          (I : (FractionalIdeal (𝓞 (candidateGenusFieldBase hd))⁰
            (candidateGenusFieldBase hd))ˣ))) := by
  let _ := candidateGenusFieldRealAlgebra hd hpos
  let _ := candidateGenusFieldRealIsScalarTower hd hpos
  let _ := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
  have hrestrict := DFunLike.congr_fun
    (NumberFieldArithmetic.artinHomAway_restrict
      (L := candidateGenusField hd)
      (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ)) S
      (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
        inferInstance inferInstance) (candidateGenusFieldReal hd)) I
  rw [MonoidHom.comp_apply] at hrestrict
  rw [← candidateGenusFieldRestrictionToReal_def hd hpos] at hrestrict
  rw [← hrestrict,
    autCandidateGenusFieldRealEquivElementaryTwoQuotient_apply_restrict,
    candidateGenusFieldOrdinaryClassGroupHom_apply,
    candidateGenusFieldOrdinaryClassGroupSignMap_apply]
  have hclass := congrArg (fun x => Multiplicative.ofAdd
    (NarrowClassGroup.toClassGroupElementaryTwoQuotient (candidateGenusFieldBase hd)
      (Multiplicative.toAdd x)))
    (autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_artinHomAway hd hnsq S hS I)
  simpa only [autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_apply,
    toAdd_ofAdd, NarrowClassGroup.toClassGroupElementaryTwoQuotient_mk,
    NarrowClassGroup.toClassGroup_mk] using hclass

/-- An ideal has trivial Artin automorphism in the real genus field exactly when its ordinary
ideal class is a square. In contrast to the full prime-discriminant compositum, no positivity
condition on principal generators is needed. -/
theorem artinHomAway_candidateGenusFieldReal_eq_one_iff
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd))))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)),
      (TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d → v ∈ S)
    (I : NumberFieldArithmetic.idealsAway (K := candidateGenusFieldBase hd) S) :
    letI := candidateGenusFieldRealAlgebra hd hpos
    letI := candidateGenusFieldRealIsScalarTower hd hpos
    letI := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
    NumberFieldArithmetic.artinHomAway (L := candidateGenusFieldReal hd)
        (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ)) S
        (isUnramifiedAway_of_intermediateField (candidateGenusFieldReal hd) S
          (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
            inferInstance inferInstance)) I = 1 ↔
      IsSquare (ClassGroup.mk (candidateGenusFieldBase hd)
        (I : (FractionalIdeal (𝓞 (candidateGenusFieldBase hd))⁰
          (candidateGenusFieldBase hd))ˣ)) := by
  let _ := candidateGenusFieldRealAlgebra hd hpos
  let _ := candidateGenusFieldRealIsScalarTower hd hpos
  let _ := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
  rw [← (autCandidateGenusFieldRealEquivElementaryTwoQuotient hd hnsq hpos).map_eq_one_iff,
    autCandidateGenusFieldRealEquivElementaryTwoQuotient_artinHomAway hd hnsq hpos S hS I,
    ofAdd_eq_one, TauCeti.elementaryTwoQuotientMk_eq_zero_iff]

/-- Every automorphism of the real genus field is the Artin automorphism of an integral ideal
prime to `2 · disc K`. -/
theorem artinHomAwayIntegral_candidateGenusFieldReal_surjective
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d) :
    letI := candidateGenusFieldRealAlgebra hd hpos
    letI := candidateGenusFieldRealIsScalarTower hd hpos
    letI := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
    Function.Surjective
      (NumberFieldArithmetic.artinHomAwayIntegral (L := candidateGenusFieldReal hd)
        (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ))
        (genusFieldArtinExcludedPrimes hd)
        (isUnramifiedAway_of_intermediateField (candidateGenusFieldReal hd)
          (genusFieldArtinExcludedPrimes hd)
          (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
            inferInstance inferInstance))) := by
  let _ := candidateGenusFieldRealAlgebra hd hpos
  let _ := candidateGenusFieldRealIsScalarTower hd hpos
  let _ := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
  intro σ
  obtain ⟨τ, rfl⟩ := candidateGenusFieldRestrictionToReal_surjective hd hpos σ
  obtain ⟨I, hI⟩ := artinHomAwayIntegral_candidateGenusField_surjective hd hnsq τ
  refine ⟨I, ?_⟩
  have hrestrict := DFunLike.congr_fun
    (NumberFieldArithmetic.artinHomAway_restrict
      (L := candidateGenusField hd)
      (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ))
      (genusFieldArtinExcludedPrimes hd)
      (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
        inferInstance inferInstance) (candidateGenusFieldReal hd))
    (NumberFieldArithmetic.integralIdealsAwayHom _ I)
  rw [NumberFieldArithmetic.artinHomAwayIntegral_apply] at hI ⊢
  rw [MonoidHom.comp_apply, ← candidateGenusFieldRestrictionToReal_def hd hpos] at hrestrict
  exact hrestrict.symm.trans (congrArg (candidateGenusFieldRestrictionToReal hd hpos) hI)

/-- Every automorphism of the real genus field is the Artin automorphism of a fractional ideal
prime to `2 · disc K`. -/
theorem artinHomAway_candidateGenusFieldReal_surjective
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) (hpos : 0 < d) :
    letI := candidateGenusFieldRealAlgebra hd hpos
    letI := candidateGenusFieldRealIsScalarTower hd hpos
    letI := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
    Function.Surjective
      (NumberFieldArithmetic.artinHomAway (L := candidateGenusFieldReal hd)
        (fun σ τ ↦ (commute_iff_eq σ τ).2 (IsMulCommutative.is_comm.comm σ τ))
        (genusFieldArtinExcludedPrimes hd)
        (isUnramifiedAway_of_intermediateField (candidateGenusFieldReal hd)
          (genusFieldArtinExcludedPrimes hd)
          (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd hnsq v.asIdeal Q
            inferInstance inferInstance))) := by
  let _ := candidateGenusFieldRealAlgebra hd hpos
  let _ := candidateGenusFieldRealIsScalarTower hd hpos
  let _ := isAbelianGalois_candidateGenusFieldReal_over_base hd hpos
  intro σ
  obtain ⟨I, hI⟩ := artinHomAwayIntegral_candidateGenusFieldReal_surjective hd hnsq hpos σ
  refine ⟨NumberFieldArithmetic.integralIdealsAwayHom _ I, ?_⟩
  simpa only [NumberFieldArithmetic.artinHomAwayIntegral_apply] using hI

end TauCeti.Multiquadratic
