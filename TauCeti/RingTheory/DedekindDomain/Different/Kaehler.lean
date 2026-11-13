/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Conductor
public import Mathlib.RingTheory.DedekindDomain.Different
public import TauCeti.RingTheory.FittingIdeal.BaseChange
import Mathlib.RingTheory.LocalProperties.Basic
import TauCeti.RingTheory.Adjoin.Conductor
import TauCeti.RingTheory.DedekindDomain.Conductor
import TauCeti.RingTheory.Kaehler.Hypersurface

/-!
# The Kähler different and the Dedekind different

Let `C` be the integral closure of an integrally closed domain `A` in a finite separable extension
`L / K` of its fraction field, and suppose `C` is a Dedekind domain, module-finite over `A`. The
**Kähler different** of `C / A` is the zeroth Fitting ideal of the module of differentials
`Ω[C⁄A]`; it is the ideal whose vanishing locus is the ramification locus, and on a finite map of
curves it is the ideal of the ramification divisor. The **Dedekind different** is Mathlib's
`differentIdeal A C`, the inverse of the trace dual of `C`.

This file proves that the two agree at every maximal ideal `Q` of `C` whose residue extension over
`A` is separable: they generate the same ideal of the local ring of `C` at `Q`
(`TauCeti.fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map`). If every residue extension
is separable, for instance when the residue fields of `A` are perfect, they are equal
(`TauCeti.fittingIdeal_kaehlerDifferential_eq_differentIdeal`).

The proof is local. At `Q` there is `x : C` whose conductor is not contained in `Q`
(`TauCeti.exists_not_conductor_le`), so the local ring of `C` at `Q` is a localization of the
monogenic ring `A[x] ≅ A[X] ⧸ (f)`, where `f` is the minimal polynomial of `x`. On the
differential side, `Fitt₀(Ω[A[x]⁄A]) = (f'(x))` (`TauCeti.fittingIdeal_kaehlerDifferential_adjoin`)
and Fitting ideals of differentials commute with localization. On the different side, Mathlib's
conductor formula `𝔣 𝔇 = (f'(x))` (`conductor_mul_differentIdeal`) gives `𝔇 = (f'(x))` at `Q`,
because the conductor `𝔣` becomes the unit ideal there. Residue separability enters only through
the existence of `x`.

## Main results

* `TauCeti.fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map_of_not_conductor_le`: the
  two differents agree at any prime not containing the conductor of some `A[x]`.
* `TauCeti.fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map`: they agree at every
  maximal ideal with separable residue extension.
* `TauCeti.fittingIdeal_kaehlerDifferential_eq_differentIdeal`: they are equal when every residue
  extension is separable.

## References

* [J.-P. Serre, *Corps locaux*][serre1968], Chapter III, §6 (the different of a monogenic
  extension) and §7 (the differential characterization of the different).
-/

public section

open Polynomial KaehlerDifferential

namespace TauCeti

variable {A C : Type*} [CommRing A] [CommRing C] [Algebra A C] [IsDomain A] [IsIntegrallyClosed A]
  [Module.IsTorsionFree A C]

variable (K L : Type*) [Field K] [Field L] [Algebra A K] [Algebra C L] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A C L] [IsFractionRing A K] [IsIntegralClosure C A L]
  [IsDedekindDomain C] [FiniteDimensional K L] [Algebra.IsSeparable K L] [Module.Finite A C]

include K L in
/-- **The two differents agree where `C` is locally monogenic.** If the conductor of `A[x]` in `C`
is not contained in the prime `Q`, then the zeroth Fitting ideal of `Ω[C⁄A]` and the different
ideal of `C / A` generate the same ideal of any localization `T` of `C` at `Q`. -/
theorem fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map_of_not_conductor_le {x : C}
    (Q : Ideal C) [Q.IsPrime] (hx : ¬ conductor A x ≤ Q) (T : Type*) [CommRing T] [Algebra C T]
    [IsLocalization.AtPrime T Q] :
    (fittingIdeal C Ω[C⁄A] 0).map (algebraMap C T) =
      (differentIdeal A C).map (algebraMap C T) := by
  -- It suffices to work in `Localization.AtPrime Q`, which is isomorphic to `T` over `C`.
  suffices h : (fittingIdeal C Ω[C⁄A] 0).map (algebraMap C (Localization.AtPrime Q)) =
      (differentIdeal A C).map (algebraMap C (Localization.AtPrime Q)) by
    let e := IsLocalization.algEquiv Q.primeCompl (Localization.AtPrime Q) T
    rw [← e.toAlgHom.comp_algebraMap, ← Ideal.map_map, ← Ideal.map_map, h]
  have := IsIntegralClosure.isFractionRing_of_finite_extension A K L C
  have := Q.isLocalization_adjoin_of_not_conductor_le hx (Localization.AtPrime Q)
  have : Algebra.FormallyEtale (Algebra.adjoin A {x}) (Localization.AtPrime Q) :=
    .of_isLocalization (Q.comap (algebraMap (Algebra.adjoin A {x}) C)).primeCompl
  -- Both Fitting ideals are read on the common localization `C_Q = A[x]_{Q ∩ A[x]}`.
  rw [← (isBaseChange_of_formallyEtale A C (Localization.AtPrime Q)).fittingIdeal_eq_map 0,
    (isBaseChange_of_formallyEtale A (Algebra.adjoin A {x}) _).fittingIdeal_eq_map 0,
    fittingIdeal_kaehlerDifferential_adjoin (IsIntegralClosure.isIntegral A L x), Ideal.map_span,
    Set.image_singleton, IsScalarTower.algebraMap_apply _ C]
  -- The conductor becomes the unit ideal at `Q`, so `𝔣 𝔇 = (f'(x))` gives `𝔇 = (f'(x))` there.
  have hK := algebra_adjoin_eq_top_of_conductor_ne_bot K L fun h ↦ hx (h ▸ bot_le)
  rw [← Ideal.top_mul (Ideal.map _ (differentIdeal A C)),
    ← IsLocalization.AtPrime.map_eq_top_of_not_le (Localization.AtPrime Q) hx, ← Ideal.map_mul,
    conductor_mul_differentIdeal A K L x hK, Ideal.map_span, Set.image_singleton]
  simp [aeval_subalgebra_coe]

include K L in
/-- **The Kähler different is the Dedekind different at a prime with separable residue
extension.** If `Q` is a maximal ideal of `C` over a maximal ideal `p` of `A`, and
`(C ⧸ Q) / (A ⧸ p)` is separable, then the zeroth Fitting ideal of `Ω[C⁄A]` and the different
ideal of `C / A` generate the same ideal of any localization `T` of `C` at `Q`. -/
theorem fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map {p : Ideal A} [p.IsMaximal]
    (Q : Ideal C) [Q.IsMaximal] [Q.LiesOver p] [Algebra.IsSeparable (A ⧸ p) (C ⧸ Q)]
    (T : Type*) [CommRing T] [Algebra C T] [IsLocalization.AtPrime T Q] :
    (fittingIdeal C Ω[C⁄A] 0).map (algebraMap C T) =
      (differentIdeal A C).map (algebraMap C T) :=
  have ⟨_, hx⟩ := exists_not_conductor_le (p := p) Q
  fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map_of_not_conductor_le K L Q hx T

include K L in
/-- **The Kähler different is the Dedekind different.** If every residue extension of `C / A` at a
maximal ideal is separable, then the zeroth Fitting ideal of `Ω[C⁄A]` is the different ideal of
`C / A`. -/
theorem fittingIdeal_kaehlerDifferential_eq_differentIdeal
    (hsep : ∀ (Q : Ideal C) [Q.IsMaximal], Algebra.IsSeparable (A ⧸ Q.under A) (C ⧸ Q)) :
    fittingIdeal C Ω[C⁄A] 0 = differentIdeal A C := by
  refine Ideal.eq_of_localization_maximal fun Q _ ↦ ?_
  have := hsep Q
  have := Ideal.IsMaximal.under A Q
  exact fittingIdeal_kaehlerDifferential_map_eq_differentIdeal_map K L (p := Q.under A) Q _

end TauCeti
