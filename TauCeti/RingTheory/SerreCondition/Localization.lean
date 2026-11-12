/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.SerreCondition.Basic
import Mathlib.RingTheory.Localization.BaseChange
import TauCeti.RingTheory.KrullDimension.Module

/-!
# Localization of Serre's condition for modules

Serre's condition `(S_n)` is preserved by localization of a module over a commutative
ring. The local rings of a localization are local rings of the original ring, and localizing
the module twice gives its localization at the contracted prime.

`Module.SatisfiesSerreS.le_depth_of_isLocalizedModule` expresses the defining depth bound using
any presentation of the local ring and localized module. This also makes the bound available
for stalks of quasi-coherent sheaves without choosing the canonical algebraic localization.
`Module.SatisfiesSerreS.localization` applies it to an arbitrary localization map of modules.

## References

* [Stacks Project, Definition 10.157.1](https://stacks.math.columbia.edu/tag/031P)
-/

public section

universe u v w w'

open IsLocalRing

namespace Module

variable {R : Type u} [CommRing R]
  {M : Type v} [AddCommGroup M] [Module R M] {n : ℕ}

/-- The depth bound in `(S_n)` holds for any presentation of the localization of a
module at a prime, over any presentation of the local ring at that prime. -/
theorem SatisfiesSerreS.le_depth_of_isLocalizedModule (h : SatisfiesSerreS n R M)
    (p : Ideal R) [p.IsPrime] (B : Type w) [CommRing B] [IsLocalRing B] [Algebra R B]
    [IsLocalization.AtPrime B p] {N : Type w'} [AddCommGroup N] [Module R N] [Module B N]
    [IsScalarTower R B N] [Small.{w'} B] (f : M →ₗ[R] N) [IsLocalizedModule p.primeCompl f] :
    min (n : WithBot ℕ∞) (supportDim B N) ≤ (depth (ModuleCat.of B N) : WithBot ℕ∞) := by
  rw [depth_eq_of_isLocalizedModule p B f,
    supportDim_eq_of_isLocalizedModule p.primeCompl B f]
  exact (satisfiesSerreS_iff.mp h) p

/-- Serre's condition `(S_n)` for a module over a commutative ring passes to every
localization, with the localized module specified by its localization map. -/
theorem SatisfiesSerreS.localization (h : SatisfiesSerreS n R M) (T : Submonoid R)
    (S : Type w) [CommRing S] [Algebra R S] [IsLocalization T S]
    {N : Type w'} [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
    (f : M →ₗ[R] N) [IsLocalizedModule T f] : SatisfiesSerreS n S N := by
  rw [satisfiesSerreS_iff]
  intro Q _
  let P := Q.comap (algebraMap R S)
  let B := Localization.AtPrime Q
  let g := LocalizedModule.mkLinearMap Q.primeCompl N
  have : IsLocalization.AtPrime B P :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization T _ Q
  have : IsLocalizedModule P.primeCompl ((g.restrictScalars R).comp f) :=
    (isLocalizedModule_iff_isBaseChange P.primeCompl B _).2
      ((IsLocalizedModule.isBaseChange T S f).comp
        (IsLocalizedModule.isBaseChange Q.primeCompl B g))
  exact h.le_depth_of_isLocalizedModule P B ((g.restrictScalars R).comp f)

end Module
