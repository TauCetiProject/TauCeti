/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.RingTheory.Unramified.Locus

/-!
# Base change and flat descent of unramifiedness at a prime

Let `B` be the pushout `S ⊗[R] A` of commutative rings, and let `q` be a prime ideal of `B` lying
over `p = q ∩ A`. Because Kähler differentials commute with arbitrary base change
(`KaehlerDifferential.tensorKaehlerEquiv`) and with localization at primes, the module of relative
differentials `Ω[B_q ⁄ S]` is canonically isomorphic to `B_q ⊗[A_p] Ω[A_p ⁄ R]`.

From `Algebra.formallyUnramified_iff` (vanishing of relative Kähler differentials), this gives
base change and flat descent of Mathlib's `Algebra.IsUnramifiedAt` and `Algebra.unramifiedLocus`
with no finite-type or Noetherian assumptions:

* `Algebra.IsUnramifiedAt.of_isPushout`: if `A` is unramified over `R` at `q ∩ A`, then `B` is
  unramified over `S` at `q`.
* `Algebra.isUnramifiedAt_iff_of_isPushout_of_flat`: if `B_q` is flat over `A_{q ∩ A}`, then `B`
  is unramified over `S` at `q` if and only if `A` is unramified over `R` at `q ∩ A`, since a flat
  local homomorphism is faithfully flat.
* `Algebra.isUnramifiedAt_iff_of_isPushout`: the same equivalence when `S` is flat over `R`.
* `Algebra.preimage_unramifiedLocus_subset_of_isPushout` and
  `Algebra.unramifiedLocus_eq_preimage_of_isPushout`: the resulting inclusion and flat-base-change
  equality on `Algebra.unramifiedLocus`.
-/

public section

open TensorProduct

namespace Algebra

section Pushout

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

variable (R S A) in
/-- In a pushout `B = S ⊗[R] A`, the localized module of Kähler differentials `Ω[B_q ⁄ S]` at a
prime `q` of `B` is isomorphic to `B_q ⊗[A_{q ∩ A}] Ω[A_{q ∩ A} ⁄ R]`. -/
private noncomputable def kaehlerAtPrimePushoutEquiv (q : Ideal B) [q.IsPrime] :
    letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
    (Localization.AtPrime q ⊗[Localization.AtPrime (q.under A)]
      Ω[Localization.AtPrime (q.under A)⁄R]) ≃ₗ[Localization.AtPrime q]
      Ω[Localization.AtPrime q⁄S] := by
  let p := q.under A
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  let eAp : Ω[Ap⁄R] ≃ₗ[Ap] Ap ⊗[A] Ω[A⁄R] :=
    (IsLocalizedModule.iso p.primeCompl
      (KaehlerDifferential.map R R A Ap)).symm.extendScalarsOfIsLocalization
        p.primeCompl Ap ≪≫ₗ LocalizedModule.equivTensorProduct p.primeCompl Ω[A⁄R]
  let eBq : Bq ⊗[B] Ω[B⁄S] ≃ₗ[Bq] Ω[Bq⁄S] :=
    (LocalizedModule.equivTensorProduct q.primeCompl Ω[B⁄S]).symm ≪≫ₗ
      (IsLocalizedModule.iso q.primeCompl
        (KaehlerDifferential.map S S B Bq)).extendScalarsOfIsLocalization
          q.primeCompl Bq
  exact AlgebraTensorModule.congr (LinearEquiv.refl Bq Bq) eAp ≪≫ₗ
    AlgebraTensorModule.cancelBaseChange A Ap Bq Bq Ω[A⁄R] ≪≫ₗ
    (AlgebraTensorModule.cancelBaseChange A B Bq Bq Ω[A⁄R]).symm ≪≫ₗ
    AlgebraTensorModule.congr (LinearEquiv.refl Bq Bq)
      (KaehlerDifferential.tensorKaehlerEquiv R S A B) ≪≫ₗ
    eBq

variable (R A) in
/-- Unramifiedness at a prime is preserved under arbitrary pushout of commutative rings, with no
finiteness hypothesis: if `A` is unramified over `R` at `q ∩ A`, then `B = S ⊗[R] A` is unramified
over `S` at `q`. -/
theorem IsUnramifiedAt.of_isPushout (q : Ideal B) [q.IsPrime] [IsUnramifiedAt R (q.under A)] :
    IsUnramifiedAt S q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  have : Subsingleton Ω[Localization.AtPrime (q.under A)⁄R] :=
    (Algebra.formallyUnramified_iff R _).mp inferInstance
  exact (Algebra.formallyUnramified_iff S _).mpr
    (kaehlerAtPrimePushoutEquiv R S A q).symm.subsingleton

/-- In a pushout `B = S ⊗[R] A`, if `B_q` is flat over `A_{q ∩ A}` at a prime `q` of `B`, then `B`
is unramified over `S` at `q` if and only if `A` is unramified over `R` at `q ∩ A`. -/
theorem isUnramifiedAt_iff_of_isPushout_of_flat (q : Ideal B) [q.IsPrime]
    (hflat :
      letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
      Module.Flat (Localization.AtPrime (q.under A)) (Localization.AtPrime q)) :
    IsUnramifiedAt S q ↔ IsUnramifiedAt R (q.under A) := by
  let p := q.under A
  let Ap := Localization.AtPrime p
  let Bq := Localization.AtPrime q
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Module.Flat Ap Bq := hflat
  have : Module.FaithfullyFlat Ap Bq := .of_flat_of_isLocalHom
  rw [IsUnramifiedAt, IsUnramifiedAt, Algebra.formallyUnramified_iff,
    Algebra.formallyUnramified_iff,
    ← (kaehlerAtPrimePushoutEquiv R S A q).subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right Ap Bq]

/-- In a flat base change `B = S ⊗[R] A` (with `S` flat over `R`), `B` is unramified over `S` at a
prime `q` if and only if `A` is unramified over `R` at `q ∩ A`. -/
theorem isUnramifiedAt_iff_of_isPushout [Module.Flat R S] (q : Ideal B) [q.IsPrime] :
    IsUnramifiedAt S q ↔ IsUnramifiedAt R (q.under A) := by
  have : Module.Flat A B :=
    Module.Flat.isBaseChange R A S B (Algebra.IsPushout.symm ‹Algebra.IsPushout R S A B›).out
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  exact isUnramifiedAt_iff_of_isPushout_of_flat q inferInstance

variable (R S A B) in
/-- Under an arbitrary pushout `B = S ⊗[R] A`, the preimage of `Algebra.unramifiedLocus R A` lies
in `Algebra.unramifiedLocus S B`. -/
theorem preimage_unramifiedLocus_subset_of_isPushout :
    PrimeSpectrum.comap (algebraMap A B) ⁻¹' unramifiedLocus R A ⊆ unramifiedLocus S B :=
  fun q hq ↦ @IsUnramifiedAt.of_isPushout R S A B _ _ _ _ _ _ _ _ _ _ _ _ q.asIdeal q.isPrime hq

variable (R S A B) in
/-- Under a flat base change `B = S ⊗[R] A`, the unramified locus of `B` over `S` is the preimage
of the unramified locus of `A` over `R`. No finite-type assumption is required. -/
theorem unramifiedLocus_eq_preimage_of_isPushout [Module.Flat R S] :
    unramifiedLocus S B = PrimeSpectrum.comap (algebraMap A B) ⁻¹' unramifiedLocus R A := by
  ext q
  exact isUnramifiedAt_iff_of_isPushout q.asIdeal

end Pushout

end Algebra
