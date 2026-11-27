/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Decomposition
public import TauCeti.RingTheory.Valuation.LocalizationAtCenter
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Valuation.LocalSubring
import TauCeti.NumberTheory.NumberField.AbsoluteGaloisGroup.Transitivity
import TauCeti.RingTheory.DedekindDomain.Prufer

/-!
# Valuation subrings of `F^alg` and primes of the algebraic integers

Let `F` be a number field, `F^alg = AlgebraicClosure F`, `G_F = Field.absoluteGaloisGroup F` and
`O` the integral closure of `𝓞 F` in `F^alg`. There are two standard ways to describe a
non-archimedean valuation of `F^alg` up to equivalence: as a prime ideal `Q` of `O`, the language
of `TauCeti/NumberTheory/NumberField/AbsoluteGaloisGroup/Decomposition.lean` and of Mathlib's
`IsArithFrobAt`; or as a valuation subring `A` of `F^alg`, the language of Mathlib's
`ValuationSubring.decompositionSubgroup` and `ValuationSubring.inertiaSubgroup`. This file shows
that they agree, in both directions. The correspondence includes the trivial valuation, given by
the zero prime of `O` and by `F^alg` itself; the finite places of `F^alg` are the nonzero primes of
`O`, equivalently the proper valuation subrings of `F^alg`.

Every valuation subring of `F^alg` contains `O`, since it contains `ℤ` and is integrally closed;
its centre on `O` is a prime of `O`. Conversely, `O` is a Prüfer domain
(`IsIntegralClosure.preValuationRing_atPrime`), so the localization `O_Q` at a prime `Q` is a
valuation subring `A_Q = Q.valuationSubringAtPrime (AlgebraicClosure F)` of `F^alg`, and it is the
only valuation subring centred at `Q`. So valuation subrings of `F^alg` correspond to primes of
`O` (`TauCeti.GaloisRep.valuationSubringEquivPrimeSpectrum`), equivariantly for `G_F`. Under this
correspondence:

* the decomposition group `D_Q` is the decomposition subgroup of `A_Q`;
* the inertia group `I_Q` is the image of the inertia subgroup of `A_Q`;
* `σ` is an arithmetic Frobenius element at `Q` (`IsArithFrobAtIntegralPrime`) exactly when it
  lies in the decomposition subgroup of `A_Q` and acts on the residue field of `A_Q` by
  `x ↦ x ^ q`, `q = #(𝓞 F ⧸ Q ∩ 𝓞 F)`.

Every prime of `𝓞 F` has a valuation subring of `F^alg` above it, and `G_F` acts transitively on
the valuation subrings above it.

For any Galois extension `L` of a number field in place of `F^alg`, with `𝓞 L` in place of `O`,
`TauCeti/RingTheory/Valuation/LocalizationAtCenter.lean` and
`IsIntegralClosure.preValuationRing_atPrime` give the correspondence with primes, its
equivariance, and the decomposition, inertia and Frobenius comparisons. The existence and
transitivity statements are proved here only for `F^alg`; transitivity for an infinite `L` needs
a separate argument.

## Main results

* `TauCeti.GaloisRep.algebraMap_mem_valuationSubring`: every valuation subring of `F^alg` contains
  `O`.
* `TauCeti.GaloisRep.valuationSubringEquivPrimeSpectrum`: valuation subrings of `F^alg` are the
  primes of `O`, through their centres, `G_F`-equivariantly
  (`TauCeti.GaloisRep.valuationSubringEquivPrimeSpectrum_smul`).
* `TauCeti.GaloisRep.decompositionGroup_eq_decompositionSubgroup`: `D_Q` is the decomposition
  subgroup of `A_Q`.
* `TauCeti.GaloisRep.inertiaGroup_eq_map_inertiaSubgroup`: `I_Q` is the image of the inertia
  subgroup of `A_Q`.
* `TauCeti.GaloisRep.isArithFrobAtIntegralPrime_iff_residue`: arithmetic Frobenius elements at
  `Q` are the elements of the decomposition subgroup of `A_Q` acting on its residue field by the
  `q`-power map.
* `TauCeti.GaloisRep.exists_isCenteredAt_under_eq` and
  `TauCeti.GaloisRep.exists_smul_eq_of_isCenteredAt`: existence of, and transitivity on,
  valuation subrings above a prime of `𝓞 F`.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9 and Chapter II, §9.
* [The Stacks Project](https://stacks.math.columbia.edu/tag/0307), Tag 0307.

## Provenance

The direction from valuation subrings to primes of the Frobenius and inertia comparison was
first proved in the `riemann-hypothesis` formalisation
(https://github.com/leanprover-community/riemann-hypothesis, branch `tc-galois-5-frobenius`,
commit `c62bdab14fd`, `src/Lib/ClassField/Places/FrobeniusComparison.lean`, declarations
`New.IsFrob.isArithFrobAt` and `New.inertiaGroup_le_inertia`). **Adapted, not copied**: those
state the restriction from a valuation subring to its centre for that project's `New.IsFrob`;
here both directions are proved, the converse through the identification of a valuation subring
with the localization at its centre, and everything is stated with Mathlib's and Tau Ceti's
decomposition, inertia and Frobenius predicates.
-/

public section

noncomputable section

open NumberField Pointwise

namespace TauCeti.GaloisRep

variable (F : Type*) [Field F] [NumberField F]

/-- The integral closure `O` of `𝓞 F` in `F^alg` has fraction field `F^alg`. -/
instance instIsFractionRingIntegralClosure :
    IsFractionRing (integralClosure (𝓞 F) (AlgebraicClosure F)) (AlgebraicClosure F) :=
  have : Algebra.IsAlgebraic (𝓞 F) (AlgebraicClosure F) :=
    (IsFractionRing.comap_isAlgebraic_iff (K := F)).mpr inferInstance
  integralClosure.isFractionRing_of_algebraic fun _ hx ↦
    FaithfulSMul.algebraMap_injective (𝓞 F) (AlgebraicClosure F) (hx.trans (map_zero _).symm)

/-- **`O` is a Prüfer domain**: its localizations at primes are valuation rings. -/
instance instPreValuationRingAtPrime (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F)))
    [Q.IsPrime] : PreValuationRing (Localization.AtPrime Q) :=
  IsIntegralClosure.preValuationRing_atPrime (𝓞 F) F (AlgebraicClosure F) Q

omit [NumberField F] in
/-- **Every valuation subring of `F^alg` contains the algebraic integers `O`**: it contains `ℤ`
and is integrally closed. -/
theorem algebraMap_mem_valuationSubring (A : ValuationSubring (AlgebraicClosure F))
    (b : integralClosure (𝓞 F) (AlgebraicClosure F)) :
    algebraMap (integralClosure (𝓞 F) (AlgebraicClosure F)) (AlgebraicClosure F) b ∈ A := by
  have hb : IsIntegral ℤ (b : AlgebraicClosure F) := isIntegral_trans (R := ℤ) _ b.property
  exact Subring.isIntegrallyClosed_iff.mp inferInstance (hb.tower_top (A := A))

/-- **Valuation subrings of `F^alg` are primes of `O`**: sending a valuation subring to its centre
on `O` is a bijection onto the prime spectrum of `O`, with inverse `Q ↦ O_Q`. -/
def valuationSubringEquivPrimeSpectrum :
    ValuationSubring (AlgebraicClosure F) ≃
      PrimeSpectrum (integralClosure (𝓞 F) (AlgebraicClosure F)) :=
  (Equiv.subtypeUnivEquiv (algebraMap_mem_valuationSubring F)).symm.trans
    (ValuationSubring.equivPrimeSpectrum fun _ _ ↦ inferInstance)

/-- The prime of `O` corresponding to a valuation subring of `F^alg` is its centre on `O`. -/
@[simp]
theorem asIdeal_valuationSubringEquivPrimeSpectrum_apply
    (A : ValuationSubring (AlgebraicClosure F)) :
    (valuationSubringEquivPrimeSpectrum F A).asIdeal =
      A.valuation.centerIdeal (integralClosure (𝓞 F) (AlgebraicClosure F)) fun b ↦
        (A.valuation_le_one_iff _).mpr (algebraMap_mem_valuationSubring F A b) :=
  ValuationSubring.asIdeal_equivPrimeSpectrum_apply _ _

/-- The valuation subring of `F^alg` corresponding to a prime `Q` of `O` is the localization
`O_Q`. -/
@[simp]
theorem valuationSubringEquivPrimeSpectrum_symm_apply
    (Q : PrimeSpectrum (integralClosure (𝓞 F) (AlgebraicClosure F))) :
    (valuationSubringEquivPrimeSpectrum F).symm Q =
      Q.asIdeal.valuationSubringAtPrime (AlgebraicClosure F) :=
  ValuationSubring.coe_equivPrimeSpectrum_symm_apply _ _

/-- **The correspondence is `G_F`-equivariant**: the valuation subring of `F^alg` corresponding to
`σ • Q` is the image under `σ` of the one corresponding to `Q`. -/
theorem valuationSubringEquivPrimeSpectrum_symm_smul
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (Q : PrimeSpectrum (integralClosure (𝓞 F) (AlgebraicClosure F))) :
    (valuationSubringEquivPrimeSpectrum F).symm (σ • Q) =
      σ • (valuationSubringEquivPrimeSpectrum F).symm Q :=
  ValuationSubring.coe_equivPrimeSpectrum_symm_smul _ σ Q

/-- **The correspondence is `G_F`-equivariant**: the prime of `O` corresponding to `σ • A` is
`σ` applied to the prime corresponding to `A`. -/
@[simp]
theorem valuationSubringEquivPrimeSpectrum_smul
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (A : ValuationSubring (AlgebraicClosure F)) :
    valuationSubringEquivPrimeSpectrum F (σ • A) = σ • valuationSubringEquivPrimeSpectrum F A := by
  rw [← Equiv.eq_symm_apply, valuationSubringEquivPrimeSpectrum_symm_smul,
    Equiv.symm_apply_apply]

variable {F} (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))) [Q.IsPrime]

/-- **The decomposition group of a prime is that of its valuation subring**: `D_Q` is Mathlib's
decomposition subgroup of the localization `O_Q`, realized as a valuation subring of `F^alg`. -/
theorem decompositionGroup_eq_decompositionSubgroup :
    decompositionGroup F Q =
      (Q.valuationSubringAtPrime (AlgebraicClosure F)).decompositionSubgroup F :=
  Ideal.isCenteredAt_valuationSubringAtPrime.decompositionSubgroup_eq.symm

/-- **The inertia group of a prime is that of its valuation subring**: `I_Q` is the image in
`G_F` of Mathlib's inertia subgroup of `O_Q`, realized as a valuation subring of `F^alg`. -/
theorem inertiaGroup_eq_map_inertiaSubgroup :
    inertiaGroup F Q =
      ((Q.valuationSubringAtPrime (AlgebraicClosure F)).inertiaSubgroup F).map
        ((Q.valuationSubringAtPrime (AlgebraicClosure F)).decompositionSubgroup F).subtype :=
  Ideal.isCenteredAt_valuationSubringAtPrime.map_inertiaSubgroup_eq.symm

/-- **Arithmetic Frobenius elements at a prime and at its valuation subring**: `σ ∈ G_F` is an
arithmetic Frobenius element at `Q` exactly when it lies in the decomposition subgroup of `O_Q`
and acts on the residue field of `O_Q` as `y ↦ y ^ q`, where `q = #(𝓞 F ⧸ Q ∩ 𝓞 F)`. -/
theorem isArithFrobAtIntegralPrime_iff_residue {σ : Field.absoluteGaloisGroup F} :
    IsArithFrobAtIntegralPrime σ Q ↔
      ∃ hσ : σ ∈ (Q.valuationSubringAtPrime (AlgebraicClosure F)).decompositionSubgroup F,
        ∀ y : IsLocalRing.ResidueField (Q.valuationSubringAtPrime (AlgebraicClosure F)),
          (⟨σ, hσ⟩ : (Q.valuationSubringAtPrime (AlgebraicClosure F)).decompositionSubgroup F) •
            y = y ^ Nat.card (𝓞 F ⧸ Q.under (𝓞 F)) :=
  Ideal.isCenteredAt_valuationSubringAtPrime.isArithFrobAt_iff

variable (F) in
/-- **Every prime of `𝓞 F` lies below a valuation subring of `F^alg`**: some valuation subring
of `F^alg` is centred at a prime of `O` over the given prime. -/
theorem exists_isCenteredAt_under_eq (p : Ideal (𝓞 F)) [p.IsPrime] :
    ∃ (A : ValuationSubring (AlgebraicClosure F))
      (Q : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))), Q.IsPrime ∧
        A.IsCenteredAt Q ∧ Q.under (𝓞 F) = p := by
  obtain ⟨⟨Q, hQ, hQp⟩⟩ := p.nonempty_primesOver (S := integralClosure (𝓞 F) (AlgebraicClosure F))
  exact ⟨Q.valuationSubringAtPrime _, Q, hQ, Ideal.isCenteredAt_valuationSubringAtPrime,
    ((Ideal.liesOver_iff _ _).mp hQp).symm⟩

variable {Q} in
omit [Q.IsPrime] in
/-- **`G_F` acts transitively on the valuation subrings above a prime of `𝓞 F`**: two valuation
subrings of `F^alg` whose centres on `O` lie over the same prime of `𝓞 F` are `G_F`-conjugate. -/
theorem exists_smul_eq_of_isCenteredAt {A A' : ValuationSubring (AlgebraicClosure F)}
    {Q' : Ideal (integralClosure (𝓞 F) (AlgebraicClosure F))} (h : A.IsCenteredAt Q)
    (h' : A'.IsCenteredAt Q') (hQQ' : Q.under (𝓞 F) = Q'.under (𝓞 F)) :
    ∃ σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F, A' = σ • A := by
  have := h.isPrime
  have := h'.isPrime
  obtain ⟨σ, hσ⟩ := exists_smul_eq_of_under_eq Q Q' hQQ'
  refine ⟨σ, h'.eq ?_⟩
  rw [hσ]
  exact h.smul (G := AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) σ

end TauCeti.GaloisRep
