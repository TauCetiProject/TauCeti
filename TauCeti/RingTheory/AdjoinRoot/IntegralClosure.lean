/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdjoinRoot.StandardTameCover
public import TauCeti.RingTheory.IntegralClosure.IntegrallyClosed
public import TauCeti.RingTheory.RegularLocalRing.OfQuotient
import TauCeti.RingTheory.AdjoinRoot.Basic

/-!
# Integral closure of a root extraction

Let `C = A[x]/(x^e - f)`, where `e` is positive and `f` is a nonzerodivisor. If `A/(f)`
is reduced, then `C` is the integral closure of `A` in `C[1/f]`. If `A` is Noetherian and
`A/(f)` is regular, every localization of `C` at a prime containing `f` is regular local.
Neither assertion requires the exponent to be invertible.

These are the integral-closure and regularity properties of the local models in Stacks,
Lemma 58.31.6 (0EYH). The root is a nonzerodivisor and its quotient is `A/(f)`, by
`standardTameCover_root_mem_nonZeroDivisors_iff` and
`standardTameCoverQuotientSpanRootAlgEquiv`. Integral closedness in the localization follows
from `IsIntegrallyClosedIn.of_isLocalization_of_le_powers`; regularity along the root follows
from `IsRegularLocalRing.localization_of_isRegularRing_quotient` (Stacks 00NU).

## Main results

* `TauCeti.standardTameCover_isIntegralClosure`: the root algebra is the integral closure of
  the base in its localization away from `f`, even when `A/(f)` is only reduced.
* `TauCeti.standardTameCover_isRegularLocalRing_localization`: if `A/(f)` is regular, the root
  algebra is regular at every prime containing the image of `f`.

## References

* [Stacks Project, Lemma 58.31.6](https://stacks.math.columbia.edu/tag/0EYH).
* [Stacks Project, Lemma 10.106.7](https://stacks.math.columbia.edu/tag/00NU).
-/

public section

open Polynomial

namespace TauCeti

variable {A : Type*} [CommRing A] {f : A} {e : ℕ}

/-- If `f` is a nonzerodivisor and `A/(f)` is reduced, the root algebra `A[x]/(x^e - f)`
for `e > 0` is the integral closure of `A` in its localization away from `f`.
No invertibility assumption on `e` or Noetherianity assumption on `A` is needed. -/
theorem standardTameCover_isIntegralClosure (hf : f ∈ nonZeroDivisors A) (he : e ≠ 0)
    [IsReduced (A ⧸ Ideal.span {f})] (Cf : Type*) [CommRing Cf]
    [Algebra (standardTameCover A f e) Cf]
    [IsLocalization.Away (algebraMap A (standardTameCover A f e) f) Cf]
    [Algebra A Cf] [IsScalarTower A (standardTameCover A f e) Cf] :
    IsIntegralClosure (standardTameCover A f e) A Cf := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have : IsReduced
      (standardTameCover A f e ⧸ Ideal.span {AdjoinRoot.root (X ^ e - C f)}) :=
    isReduced_of_injective (standardTameCoverQuotientSpanRootAlgEquiv f he)
      (standardTameCoverQuotientSpanRootAlgEquiv f he).injective
  have : IsIntegrallyClosedIn (standardTameCover A f e) Cf :=
    .of_isLocalization_of_le_powers
      ((standardTameCover_root_mem_nonZeroDivisors_iff he).mpr hf)
      (Submonoid.powers (algebraMap A (standardTameCover A f e) f))
      (Submonoid.powers_le.mpr (by
        rw [AdjoinRoot.algebraMap_eq, ← AdjoinRoot.root_X_pow_sub_C_pow]
        exact Submonoid.pow_mem _ (Submonoid.mem_powers _) e))
  exact IsIntegralClosure.of_isIntegrallyClosedIn

/-- If `A` is Noetherian, `f` is a nonzerodivisor and `A/(f)` is regular, then
`A[x]/(x^e - f)` is regular at every prime over the divisor `(f)`, for every `e > 0`.
In particular, this applies even when the residue characteristic divides `e`. -/
theorem standardTameCover_isRegularLocalRing_localization [IsNoetherianRing A]
    (hf : f ∈ nonZeroDivisors A) (he : e ≠ 0) [IsRegularRing (A ⧸ Ideal.span {f})]
    (P : Ideal (standardTameCover A f e)) [P.IsPrime]
    (hfP : algebraMap A (standardTameCover A f e) f ∈ P) :
    IsRegularLocalRing (Localization.AtPrime P) := by
  have := (monic_X_pow_sub_C f he).finite_adjoinRoot
  have := IsNoetherianRing.of_finite A (standardTameCover A f e)
  have : IsRegularRing
      (standardTameCover A f e ⧸ Ideal.span {AdjoinRoot.root (X ^ e - C f)}) :=
    .of_ringEquiv (standardTameCoverQuotientSpanRootAlgEquiv f he).symm.toRingEquiv
  apply IsRegularLocalRing.localization_of_isRegularRing_quotient
    ((standardTameCover_root_mem_nonZeroDivisors_iff he).mpr hf) P
  apply Ideal.IsPrime.mem_of_pow_mem inferInstance e
  rwa [AdjoinRoot.root_X_pow_sub_C_pow, ← AdjoinRoot.algebraMap_eq]

end TauCeti
