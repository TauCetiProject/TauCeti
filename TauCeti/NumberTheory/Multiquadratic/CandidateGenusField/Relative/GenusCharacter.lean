/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.GaloisGroup
public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Quadratic
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.GenusCharacter.PrincipalGenus
import TauCeti.NumberTheory.NumberField.NarrowClassGroup.TotallyComplex
import TauCeti.NumberTheory.NumberField.Quadratic.InfinitePlace

/-!
# The genus field of a quadratic field has Galois group `Cl⁺(K)/Cl⁺(K)²`

For a squarefree integer `d` let `K = ℚ(√d)` be the embedded quadratic base of the candidate genus
field `K_gen = candidateGenusField hd`, the compositum of the quadratic fields of the prime
discriminants dividing `disc K`. It is the narrow genus field of `K`
(`isNarrowGenusField_candidateGenusField`), and the genus field of `K` when `d < 0`
(`isGenusField_candidateGenusField`). This file proves the genus-field isomorphism

`Gal(K_gen / K) ≅ Cl⁺(K) / Cl⁺(K)²`,

and, for imaginary `K`, its ordinary form `Gal(K_gen / K) ≅ Cl(K) / Cl(K)²`. Only the equality of
the two cardinalities was known before
(`card_aut_candidateGenusField_over_base_eq_card_narrowElementaryTwoQuotient`).

Both sides are described by the same space of sign patterns on the prime discriminants, and the
isomorphism is the identification of the two descriptions. On the Galois side, an automorphism is
recorded by the signs it puts on the chosen square roots, and fixing the base is exactly having an
even number of sign changes (`galoisGroupEquivCandidateGenusFieldRelative`). On the class-group
side, a narrow ideal class is recorded by its genus characters, which realize exactly the sign
patterns of product one and separate the classes modulo squares
(`mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff` and
`genusCharFunElementaryTwoQuotientFamilyLinearMap_injective`). The two sign spaces coincide, so
the two groups do.

The composite is the inverse of the Artin map of `K_gen / K`: the genus character `χ_P` of the
class of a degree-one prime `𝔮` above `q` is the Legendre symbol governing the Frobenius of `q` in
`ℚ(√P)` (`exists_forall_genusCharFunNarrowClassGroupHom_eq`). That identification with Frobenius
elements is not proved here; what is proved is the isomorphism itself.

See D. A. Cox, *Primes of the Form x² + ny²*, §6.A, and F. Lemmermeyer, *Reciprocity Laws: From
Euler to Eisenstein*, §2.2.

## Main definitions

* `TauCeti.Multiquadratic.narrowElementaryTwoQuotientEquivRelativeSign`: `Cl⁺(K)/Cl⁺(K)²` is the
  space of even-parity sign patterns on the prime discriminants of `disc K`.
* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivNarrowElementaryTwoQuotient`:
  `Gal(K_gen/K) ≅ Cl⁺(K)/Cl⁺(K)²`.
* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivElementaryTwoQuotient`: for `d < 0`,
  `Gal(K_gen/K) ≅ Cl(K)/Cl(K)²`.
-/

public section

open NumberField

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-! ### The genus characters of the embedded base, in sign coordinates -/

/-- The genus characters of the embedded quadratic base `ℚ(√d)`, assembled into a `ZMod 2`-linear
map into the sign patterns on the prime discriminants of its discriminant. This is
`genusCharFunElementaryTwoQuotientFamilyLinearMap` for the chosen factorization
`genusPrimeDiscriminants hd`, with the sign group `ℤˣ` written as `ZMod 2` so that the target is
the one carrying the relative Galois group. -/
@[expose] noncomputable def candidateGenusFieldBaseGenusCharLinearMap (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    NarrowClassGroup.ElementaryTwoQuotient (candidateGenusFieldBase hd) →ₗ[ZMod 2]
      ({P // P ∈ genusPrimeDiscriminants hd} → ZMod 2) :=
  (LinearEquiv.piCongrRight fun _ => TauCeti.additiveIntUnitsLinearEquiv).toLinearMap ∘ₗ
    genusCharFunElementaryTwoQuotientFamilyLinearMap (genusPrimeDiscriminants_spec hd).1
      (genusPrimeDiscriminants_spec hd).2.1 (genusPrimeDiscriminants_spec hd).2.2
      (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd

/-- The sign pattern recorded by the genus characters is the image of the sign vector of
`genusCharFunElementaryTwoQuotientFamilyLinearMap` under the identification of `ℤˣ` with
`ZMod 2`. -/
theorem candidateGenusFieldBaseGenusCharLinearMap_apply (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    (x : NarrowClassGroup.ElementaryTwoQuotient (candidateGenusFieldBase hd))
    (P : {P // P ∈ genusPrimeDiscriminants hd}) :
    candidateGenusFieldBaseGenusCharLinearMap hd hnsq x P =
      TauCeti.additiveIntUnitsLinearEquiv
        (genusCharFunElementaryTwoQuotientFamilyLinearMap (genusPrimeDiscriminants_spec hd).1
          (genusPrimeDiscriminants_spec hd).2.1 (genusPrimeDiscriminants_spec hd).2.2
          (minpoly_candidateGenusFieldBaseGen hd hnsq)
          (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd x P) :=
  rfl

/-- **The genus characters of the base realize exactly the even-parity sign patterns.** -/
theorem range_candidateGenusFieldBaseGenusCharLinearMap (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    LinearMap.range (candidateGenusFieldBaseGenusCharLinearMap hd hnsq) =
      candidateGenusFieldRelativeSignSubmodule hd := by
  refine Submodule.ext fun v => ?_
  rw [mem_candidateGenusFieldRelativeSignSubmodule_iff]
  constructor
  · rintro ⟨x, rfl⟩
    have hsum := (mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff
      (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
      (genusPrimeDiscriminants_spec hd).2.2 (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd _).mp ⟨x, rfl⟩
    simp only [candidateGenusFieldBaseGenusCharLinearMap_apply]
    rw [← map_sum, hsum, map_zero]
  · intro hv
    set e := TauCeti.additiveIntUnitsLinearEquiv
    have hsum : ∑ P : {P // P ∈ genusPrimeDiscriminants hd}, e.symm (v P) = 0 := by
      rw [← map_sum, hv, map_zero]
    obtain ⟨x, hx⟩ := (mem_range_genusCharFunElementaryTwoQuotientFamilyLinearMap_iff
      (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
      (genusPrimeDiscriminants_spec hd).2.2 (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd _).mpr hsum
    refine ⟨x, funext fun P => ?_⟩
    rw [candidateGenusFieldBaseGenusCharLinearMap_apply, congrFun hx P]
    exact e.apply_symm_apply (v P)

/-- **The genus characters of the base separate narrow classes modulo squares.** -/
theorem candidateGenusFieldBaseGenusCharLinearMap_injective (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    Function.Injective (candidateGenusFieldBaseGenusCharLinearMap hd hnsq) :=
  (LinearEquiv.piCongrRight fun _ => TauCeti.additiveIntUnitsLinearEquiv).injective.comp
    (genusCharFunElementaryTwoQuotientFamilyLinearMap_injective
      (genusPrimeDiscriminants_spec hd).1 (genusPrimeDiscriminants_spec hd).2.1
      (genusPrimeDiscriminants_spec hd).2.2 (minpoly_candidateGenusFieldBaseGen hd hnsq)
      (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd)

/-! ### The genus-field isomorphism -/

/-- **`Cl⁺(K)/Cl⁺(K)²` is the even-parity sign space.** For `K = ℚ(√d)` the embedded quadratic base
of the candidate genus field, the genus characters identify the maximal elementary-`2` quotient of
the narrow class group with the `𝔽₂`-space of sign patterns of product one on the prime
discriminants dividing `disc K`. -/
noncomputable def narrowElementaryTwoQuotientEquivRelativeSign (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    NarrowClassGroup.ElementaryTwoQuotient (candidateGenusFieldBase hd) ≃ₗ[ZMod 2]
      ↥(candidateGenusFieldRelativeSignSubmodule hd) :=
  (LinearEquiv.ofInjective _ (candidateGenusFieldBaseGenusCharLinearMap_injective hd hnsq)).trans
    (LinearEquiv.ofEq _ _ (range_candidateGenusFieldBaseGenusCharLinearMap hd hnsq))

/-- **The genus-field isomorphism `Gal(K_gen/K) ≅ Cl⁺(K)/Cl⁺(K)²`.** For a squarefree integer `d`
that is not a rational square, the Galois group of the candidate genus field over its embedded
quadratic base `K = ℚ(√d)` is isomorphic to the maximal elementary-`2` quotient of the narrow class
group of `K`. Both are the space of even-parity sign patterns on the prime discriminants dividing
`disc K`: the Galois group by its sign patterns, the class group by its genus characters. -/
noncomputable def autCandidateGenusFieldEquivNarrowElementaryTwoQuotient (hd : Squarefree d)
    (hnsq : ¬ IsSquare ((d : ℤ) : ℚ)) :
    (candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd) ≃*
      Multiplicative
        (NarrowClassGroup.ElementaryTwoQuotient (candidateGenusFieldBase hd)) :=
  (galoisGroupEquivCandidateGenusFieldRelative hd).trans
    (narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).symm.toAddEquiv.toMultiplicative

/-- **The genus-field isomorphism for an imaginary quadratic field,
`Gal(K_gen/K) ≅ Cl(K)/Cl(K)²`.** For `d < 0` squarefree, the narrow and ordinary class groups of
`K = ℚ(√d)` agree, so the genus-field isomorphism takes its classical ordinary form. Here
`K_gen` is the genus field of `K` in the full sense
(`isGenusField_candidateGenusField`): unramified over `K` at every place, including the infinite
ones, and abelian over `ℚ`. -/
noncomputable def autCandidateGenusFieldEquivElementaryTwoQuotient (hd : Squarefree d)
    (hneg : d < 0) :
    (candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd) ≃*
      Multiplicative
        (TauCeti.ClassGroup.ElementaryTwoQuotient (𝓞 (candidateGenusFieldBase hd))) :=
  have hnsq : ¬ IsSquare ((d : ℤ) : ℚ) := fun h =>
    absurd h.nonneg (not_le.mpr (by exact_mod_cast hneg))
  haveI : NumberField.IsTotallyComplex (candidateGenusFieldBase hd) :=
    NumberField.isTotallyComplex_of_minpoly_eq_X_sq_sub_C_of_neg
      (minpoly_candidateGenusFieldBaseGen hd hnsq) hneg
  (autCandidateGenusFieldEquivNarrowElementaryTwoQuotient hd hnsq).trans
    (NarrowClassGroup.toClassGroupElementaryTwoQuotientEquiv
      (candidateGenusFieldBase hd)).toAddEquiv.toMultiplicative

end TauCeti.Multiquadratic
