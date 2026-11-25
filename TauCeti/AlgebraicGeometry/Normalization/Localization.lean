/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.Defs
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Localization.Integral

/-!
# Localizing the spectrum of an integral closure

If `S` is integral over a localization `K` of `A`, then `Spec S` is the base change of the
spectrum of the integral closure of `A` in `S` to `Spec K`. This computes the generic fibre
when `A` is a domain and `K` is its fraction field, without requiring `S` to be a domain.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Base change of the spectrum of an integral closure to a localization recovers the spectrum
of the original algebra, when that algebra is integral over the localization. -/
noncomputable def integralClosureLocalizationIso (A K S : Type u) [CommRing A]
    (M : Submonoid A) [CommRing K] [Algebra A K] [IsLocalization M K]
    [CommRing S] [Algebra A S] [Algebra K S] [IsScalarTower A K S] [Algebra.IsIntegral K S] :
    Over.mk (pullback.snd (Spec.algebraMap A (integralClosure A S)) (Spec.algebraMap A K)) ≅
      Over.mk (Spec.algebraMap K S) := by
  have := TauCeti.IsIntegralClosure.isLocalization_of_isIntegral (S := integralClosure A S)
    (M := M) K (L := S)
  have h : Algebra.IsPushout A (integralClosure A S) K S :=
    Algebra.isPushout_of_isLocalization M K _ S
  have := (Algebra.IsPushout.comm A (integralClosure A S) K S).mp h
  exact pullbackSpecIsoOfAlgEquiv A (integralClosure A S) K S
    (Algebra.IsPushout.equiv A K (integralClosure A S) S)

end TauCeti.AlgebraicGeometry
