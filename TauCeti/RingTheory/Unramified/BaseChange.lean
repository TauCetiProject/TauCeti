/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.Unramified.Locus
import TauCeti.RingTheory.Kaehler.Localization

/-!
# Base change and flat descent of unramifiedness at a prime

For a pushout `B = S ⊗[R] A` of commutative rings and a prime `q` of `B` over `p = q ∩ A`, Kähler
differentials commute with base change and localization
(`TauCeti.KaehlerDifferential.atPrimePushoutEquiv`). With no finite-type or Noetherian hypotheses,
this yields:

* `Algebra.IsUnramifiedAt.of_isPushout`: base change of `Algebra.IsUnramifiedAt`.
* `Algebra.isUnramifiedAt_iff_of_isPushout_of_flat`, `Algebra.isUnramifiedAt_iff_of_isPushout`:
  equivalence when `B_q` is flat over `A_p` (in particular when `S` is flat over `R`).
* `Algebra.preimage_unramifiedLocus_subset_of_isPushout`,
  `Algebra.unramifiedLocus_eq_preimage_of_isPushout`: consequences on `Algebra.unramifiedLocus`.
-/

public section

open TensorProduct

namespace Algebra

section Pushout

variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
  [Algebra R S] [Algebra R A] [Algebra R B] [Algebra A B] [Algebra S B]
  [IsScalarTower R A B] [IsScalarTower R S B] [Algebra.IsPushout R S A B]

variable (R A) in
/-- Unramifiedness at a prime is preserved under arbitrary pushout of commutative rings, with no
finiteness hypothesis. -/
theorem IsUnramifiedAt.of_isPushout (q : Ideal B) [q.IsPrime] [IsUnramifiedAt R (q.under A)] :
    IsUnramifiedAt S q := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  have : Subsingleton Ω[Localization.AtPrime (q.under A)⁄R] :=
    (Algebra.formallyUnramified_iff R _).mp inferInstance
  exact (Algebra.formallyUnramified_iff S _).mpr
    (TauCeti.KaehlerDifferential.atPrimePushoutEquiv R S A q).symm.subsingleton

/-- In a pushout `B = S ⊗[R] A`, if `B_q` is flat over `A_{q ∩ A}` at a prime `q` of `B`, then `B`
is unramified over `S` at `q` iff `A` is unramified over `R` at `q ∩ A`. -/
theorem isUnramifiedAt_iff_of_isPushout_of_flat (q : Ideal B) [q.IsPrime]
    (hflat : letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
      Module.Flat (Localization.AtPrime (q.under A)) (Localization.AtPrime q)) :
    IsUnramifiedAt S q ↔ IsUnramifiedAt R (q.under A) := by
  let := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  have : Module.FaithfullyFlat (Localization.AtPrime (q.under A)) (Localization.AtPrime q) :=
    @Module.FaithfullyFlat.of_flat_of_isLocalHom _ _ _ _ _ _ _ hflat _
  rw [IsUnramifiedAt, IsUnramifiedAt, Algebra.formallyUnramified_iff,
    Algebra.formallyUnramified_iff,
    ← (TauCeti.KaehlerDifferential.atPrimePushoutEquiv R S A q).subsingleton_congr,
    Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (Localization.AtPrime (q.under A))
      (Localization.AtPrime q)]

/-- In a flat base change `B = S ⊗[R] A` (with `S` flat over `R`), `B` is unramified over `S` at a
prime `q` iff `A` is unramified over `R` at `q ∩ A`. -/
theorem isUnramifiedAt_iff_of_isPushout [Module.Flat R S] (q : Ideal B) [q.IsPrime] :
    IsUnramifiedAt S q ↔ IsUnramifiedAt R (q.under A) :=
  have : Module.Flat A B :=
    Module.Flat.isBaseChange R A S B (Algebra.IsPushout.symm ‹Algebra.IsPushout R S A B›).out
  letI := Localization.AtPrime.algebraOfLiesOver (q.under A) q
  isUnramifiedAt_iff_of_isPushout_of_flat q inferInstance

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
    unramifiedLocus S B = PrimeSpectrum.comap (algebraMap A B) ⁻¹' unramifiedLocus R A :=
  Set.ext fun q ↦ isUnramifiedAt_iff_of_isPushout q.asIdeal

end Pushout

end Algebra
