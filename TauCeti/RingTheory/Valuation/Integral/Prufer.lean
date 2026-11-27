/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import TauCeti.RingTheory.Valuation.LocalizationAtCenter
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Localization.Integral
import TauCeti.RingTheory.Valuation.AlgebraicExtension
import TauCeti.RingTheory.Valuation.ValuationRingCriterion
import TauCeti.RingTheory.Valuation.ValuationSubring

/-!
# The integral closure of a valuation ring in an algebraic extension

Let `O` be a valuation subring of a field `K` and `L / K` an algebraic extension. This file shows
that the integral closure `B` of `O` in `L` is a Prüfer domain, that is, its localization at every
prime is a valuation ring, and that its maximal ideals correspond to the extensions of `O` to `L`,
the extension at a maximal ideal `𝔪` being the localization `B_𝔪`. When `L / K` is finite there
are at most `[L : K]` such extensions, so `B` has finitely many maximal ideals. No finiteness of
`B` as an `O`-module is used or claimed: for a nondiscrete valuation it can fail.

The Prüfer property holds more generally for every `O`-algebra `A` that is an integrally closed
domain whose fraction field `L` is algebraic over `K`; `A` itself need not be local, nor equal to
the integral closure of `O` in `L`.

## Method

The engine is Kaplansky's criterion
(`ValuationRing.of_forall_exists_isUnit_coeff_aeval_eq_zero`): an integrally closed local domain
is a valuation ring if every element of its fraction field is a root of a polynomial over it with
a unit coefficient. An element of `L` is algebraic over `K`, so it is a root of a polynomial over
`O` with a coefficient equal to `1` (`ValuationSubring.exists_coeff_eq_one_and_aeval_eq_zero`).
Its image in a localization `A_𝔮` satisfies the criterion. Since `B` is Prüfer, a valuation
subring of `L` containing `B` is the localization of `B` at its centre
(`ValuationSubring.IsCenteredAt.eq_valuationSubringAtPrime`). Such a subring restricts to `O`
exactly when its centre lies over the maximal ideal of `O`, that is, since `B` is integral over
`O`, exactly when the centre is a maximal ideal.

The bound on the number of maximal ideals is the bound `[L : K]` on the number of extensions of
`O` to `L` (`ValuationSubring.ncard_setOf_comap_eq_le_finrank`).

## Main results

* `ValuationSubring.preValuationRing_atPrime`: the localizations at primes of an integrally closed
  `O`-algebra with fraction field algebraic over `K` are valuation rings.
* `ValuationSubring.extensionEquivMaximalSpectrum`: the extensions of `O` to `L` correspond to
  the maximal ideals of the integral closure of `O` in `L`.
* `ValuationSubring.finite_maximalSpectrum_integralClosure`,
  `ValuationSubring.card_maximalSpectrum_integralClosure_le_finrank`: for `L / K` finite, the
  integral closure has finitely many, indeed at most `[L : K]`, maximal ideals.

## References

* [I. Kaplansky, *Commutative Rings*], Theorem 67, for the valuation ring criterion.
* [R. Gilmer, *Multiplicative Ideal Theory*], Theorem 22.1 and §19, for Prüfer domains and the
  integral closure of a valuation ring.
* [A. J. Engler and A. Prestel, *Valued Fields*], §3.2, for the extensions of a valuation to an
  algebraic extension and the bound on their number.
* M. Temkin, *Tame distillation and desingularization by p-alterations*, Annals of Mathematics 186
  (2017), Lemma 2.3.4.
-/

public section

open Polynomial

namespace ValuationSubring

variable {K L : Type*} [Field K] [Field L] [Algebra K L] (O : ValuationSubring K)

/-- **Integrally closed algebras over a valuation ring are Prüfer domains.** Let `O` be a
valuation subring of `K`, and `A` an `O`-algebra that is an integrally closed domain with
fraction field `L` algebraic over `K`. Then the localization of `A` at every prime is a valuation
ring. -/
theorem preValuationRing_atPrime [Algebra.IsAlgebraic K L] {A : Type*} [CommRing A]
    [IsIntegrallyClosed A] [Algebra A L] [IsFractionRing A L] [Algebra O A] [IsScalarTower O A L]
    (P : Ideal A) [P.IsPrime] : PreValuationRing (Localization.AtPrime P) := by
  have : IsDomain A := (IsFractionRing.injective A L).isDomain
  set S := Localization.subalgebra.ofField L P.primeCompl
    (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)
  have : IsLocalization P.primeCompl S :=
    Localization.subalgebra.isLocalization_ofField L P.primeCompl
      (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)
  -- `A_P`, realized inside `L`, is an integrally closed local domain with fraction field `L`
  have : IsLocalRing S := IsLocalization.AtPrime.isLocalRing S P
  have : IsIntegrallyClosed S := isIntegrallyClosed_of_isLocalization S P.primeCompl
    (P.primeCompl_le_nonZeroDivisors_of_isFractionRing L)
  have : IsFractionRing S L :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.primeCompl S L
  have hφ : (algebraMap S L).comp ((algebraMap A S).comp (algebraMap O A)) = algebraMap O L := by
    rw [← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  -- the image in `S` of a normalized relation over `O` has the unit coefficient `1`
  have : ValuationRing S := ValuationRing.of_forall_exists_isUnit_coeff_aeval_eq_zero (K := L)
    fun x ↦ by
      obtain ⟨p, ⟨i, hi⟩, hp⟩ :=
        O.exists_coeff_eq_one_and_aeval_eq_zero (Algebra.IsAlgebraic.isAlgebraic (R := K) x)
      refine ⟨p.map ((algebraMap A S).comp (algebraMap O A)), ⟨i, ?_⟩, ?_⟩
      · rw [coeff_map, hi, map_one]
        exact isUnit_one
      · rw [aeval_def, eval₂_map, hφ, ← aeval_def, hp]
  exact Function.Surjective.preValuationRing
    (IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P) : S →ₙ* _)
    (IsLocalization.algEquiv P.primeCompl S (Localization.AtPrime P)).surjective

section IntegralClosure

variable [Algebra.IsAlgebraic K L]

/-- The integral closure of a valuation subring `O` of `K` in an algebraic extension `L` has
fraction field `L`. -/
instance isFractionRing_integralClosure : IsFractionRing (integralClosure O L) L :=
  have : Algebra.IsAlgebraic O L :=
    (IsFractionRing.comap_isAlgebraic_iff (K := K)).mpr inferInstance
  integralClosure.isFractionRing_of_algebraic fun _ hx ↦ Subtype.val_injective <|
    (map_eq_zero (algebraMap K L)).mp ((IsScalarTower.algebraMap_apply O K L _).symm.trans hx)

/-- **The integral closure of a valuation ring in an algebraic extension is a Prüfer domain**:
its localization at every prime is a valuation ring. -/
instance preValuationRing_atPrime_integralClosure (P : Ideal (integralClosure O L)) [P.IsPrime] :
    PreValuationRing (Localization.AtPrime P) :=
  have := IsIntegrallyClosed.of_isIntegrallyClosedIn (integralClosure O L) L
  O.preValuationRing_atPrime (L := L) P

end IntegralClosure

/-! ### Extensions of `O` and maximal ideals of its integral closure -/

section Extension

variable {O}

/-- An element of `O`, mapped into its integral closure in `L` and read in `L`, is its image under
`K → L`. -/
private theorem algebraMap_integralClosure_algebraMap (o : O) :
    algebraMap (integralClosure O L) L (algebraMap O (integralClosure O L) o) =
      algebraMap K L o := by
  rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply O K L, algebraMap_apply]

/-- The valuation of a valuation subring of `L` whose restriction to `K` is `O` is at most `1` on
the integral closure of `O` in `L`. -/
private theorem valuation_algebraMap_integralClosure_le_one
    (W : {W : ValuationSubring L // W.comap (algebraMap K L) = O}) (b : integralClosure O L) :
    W.val.valuation (algebraMap (integralClosure O L) L b) ≤ 1 :=
  (W.val.valuation_le_one_iff _).mpr
    ((integralClosure_toSubring_le_iff W.val).mpr W.property.ge b.property)

/-- **Extensions are centred at maximal ideals.** A valuation subring `W` of `L` centred at a prime
`P` of the integral closure of `O` in `L` restricts to `O` exactly when `P` is maximal. -/
theorem IsCenteredAt.comap_eq_iff_isMaximal {W : ValuationSubring L}
    {P : Ideal (integralClosure O L)} (h : W.IsCenteredAt P) :
    W.comap (algebraMap K L) = O ↔ P.IsMaximal := by
  have := h.isPrime
  -- an element of `O` lies under `P` exactly when it is a nonunit of the restriction of `W`
  have hmem (o : O) : o ∈ P.under O ↔ (o : K) ∈ (W.comap (algebraMap K L)).nonunits := by
    rw [Ideal.mem_under, ← h.algebraMap_mem_nonunits_iff, mem_nonunits_comap,
      algebraMap_integralClosure_algebraMap]
  have hle : O ≤ W.comap (algebraMap K L) := fun o ho ↦ by
    rw [mem_comap, ← algebraMap_integralClosure_algebraMap ⟨o, ho⟩]
    exact h.algebraMap_mem _
  refine ⟨fun hW ↦ Ideal.isMaximal_of_isIntegral_of_isMaximal_under (R := O) P ?_, fun hP ↦ ?_⟩
  · have : P.under O = IsLocalRing.maximalIdeal O := by
      ext o
      rw [hmem, hW, coe_mem_nonunits_iff]
    exact this ▸ IsLocalRing.maximalIdeal.isMaximal O
  · have hunder : P.under O = IsLocalRing.maximalIdeal O :=
      IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_under_of_isIntegral_of_isMaximal P)
    refine (eq_of_le_of_nonunits_le hle fun x hx ↦ ?_).symm
    obtain ⟨hxO, hxm⟩ := mem_nonunits_iff_exists_mem_maximalIdeal.mp hx
    exact (hmem ⟨x, hxO⟩).mp (hunder ▸ hxm)

variable (O) [Algebra.IsAlgebraic K L]

/-- **Extensions of a valuation subring are the maximal ideals of its integral closure.** For an
algebraic extension `L / K`, sending a valuation subring of `L` restricting to `O` to its centre
on the integral closure `B` of `O` in `L` is a bijection onto the maximal ideals of `B`, with
inverse `𝔪 ↦ B_𝔪`. -/
noncomputable def extensionEquivMaximalSpectrum :
    {W : ValuationSubring L // W.comap (algebraMap K L) = O} ≃
      MaximalSpectrum (integralClosure O L) where
  toFun W :=
    ⟨W.val.valuation.centerIdeal _ (valuation_algebraMap_integralClosure_le_one W),
      (W.val.isCenteredAt_centerIdeal _).comap_eq_iff_isMaximal.mp W.property⟩
  invFun 𝔪 :=
    have := 𝔪.isMaximal
    ⟨𝔪.asIdeal.valuationSubringAtPrime L,
      Ideal.isCenteredAt_valuationSubringAtPrime.comap_eq_iff_isMaximal.mpr 𝔪.isMaximal⟩
  left_inv W :=
    have := Valuation.isPrime_centerIdeal (valuation_algebraMap_integralClosure_le_one W)
    Subtype.ext (W.val.isCenteredAt_centerIdeal _).eq_valuationSubringAtPrime.symm
  right_inv 𝔪 :=
    have := 𝔪.isMaximal
    MaximalSpectrum.ext Ideal.isCenteredAt_valuationSubringAtPrime.eq_centerIdeal.symm

variable {O}

/-- An extension of `O` is centred at the maximal ideal it corresponds to. -/
theorem isCenteredAt_extensionEquivMaximalSpectrum
    (W : {W : ValuationSubring L // W.comap (algebraMap K L) = O}) :
    W.val.IsCenteredAt (extensionEquivMaximalSpectrum O W).asIdeal :=
  W.val.isCenteredAt_centerIdeal _

/-- The extension of `O` corresponding to a maximal ideal `𝔪` of the integral closure `B` is the
localization `B_𝔪`. -/
@[simp]
theorem coe_extensionEquivMaximalSpectrum_symm_apply (𝔪 : MaximalSpectrum (integralClosure O L)) :
    haveI := 𝔪.isMaximal
    ((extensionEquivMaximalSpectrum O).symm 𝔪 : ValuationSubring L) =
      𝔪.asIdeal.valuationSubringAtPrime L :=
  (rfl)

end Extension

/-! ### Finitely many extensions to a finite extension -/

section Finite

variable [FiniteDimensional K L]

/-- **The integral closure of a valuation ring in a finite extension is semilocal.** -/
instance finite_maximalSpectrum_integralClosure : Finite (MaximalSpectrum (integralClosure O L)) :=
  have := (finite_setOf_comap_eq O (L := L)).to_subtype
  .of_equiv _ (extensionEquivMaximalSpectrum O)

/-- The integral closure of a valuation ring in a finite extension `L / K` has at most `[L : K]`
maximal ideals. -/
theorem card_maximalSpectrum_integralClosure_le_finrank :
    Nat.card (MaximalSpectrum (integralClosure O L)) ≤ Module.finrank K L := by
  rw [← Nat.card_congr (extensionEquivMaximalSpectrum O)]
  exact ncard_setOf_comap_eq_le_finrank O

end Finite

end ValuationSubring
