/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.Localization.FractionRing
import TauCeti.AlgebraicGeometry.Pullback.SpecMap
import TauCeti.RingTheory.Localization.Integral

/-!
# The generic fibre of the spectrum of an integral closure

If `S` is integral over the total ring of fractions of `A`, then `Spec S` is the base change of
the spectrum of the integral closure of `A` in `S` to that ring of fractions. In particular,
this computes the generic fibre when `A` is a domain, without requiring `S` to be a domain.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Base change of the spectrum of an integral closure to the total ring of fractions recovers
the spectrum of the original algebra, when that algebra is integral over the ring of fractions. -/
noncomputable def integralClosureGenericFiberIso (A K S : Type u) [CommRing A]
    [CommRing K] [Algebra A K] [IsFractionRing A K] [CommRing S] [Algebra A S] [Algebra K S]
    [IsScalarTower A K S] [Algebra.IsIntegral K S] :
    Over.mk (pullback.snd (Spec.algebraMap A (integralClosure A S)) (Spec.algebraMap A K)) ≅
      Over.mk (Spec.algebraMap K S) := by
  have := TauCeti.IsIntegralClosure.isLocalization_of_isIntegral (S := integralClosure A S)
    (M := nonZeroDivisors A) K (L := S)
  have h : Algebra.IsPushout A (integralClosure A S) K S :=
    Algebra.isPushout_of_isLocalization (nonZeroDivisors A) K _ S
  have := (Algebra.IsPushout.comm A (integralClosure A S) K S).mp h
  exact pullbackSpecIsoOfAlgEquiv A (integralClosure A S) K S
    (Algebra.IsPushout.equiv A K (integralClosure A S) S)

end TauCeti.AlgebraicGeometry
