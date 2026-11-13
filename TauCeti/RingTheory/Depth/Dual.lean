/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Depth of localized Hom modules

For finite modules over a Noetherian ring, localization commutes with taking linear maps.
Consequently a bound at most two on the depth of the localized target also bounds the depth
of the localized Hom module. In particular a depth bound on the local ring passes to duals.
This is useful for extending maps across subsets of codimension at least two.

## References

* Stacks Project, Lemma 15.24.10 (Tag 0AV5).
-/

public section

open Module IsLocalRing

namespace Ideal

universe u

/-- A depth bound at most two on a localized finite target passes to the localization
of the module of linear maps from any finite module. -/
theorem le_depth_localizedModule_hom {R M N : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] (p : Ideal R) [p.IsPrime]
    {N' : Type u} [AddCommGroup N'] [Module R N']
    [Module (Localization.AtPrime p) N'] [IsScalarTower R (Localization.AtPrime p) N']
    (g : N →ₗ[R] N') [IsLocalizedModule p.primeCompl g]
    {n : ℕ} (hn : n ≤ 2)
    (hdepth : (n : ℕ∞) ≤ IsLocalRing.depth
      (ModuleCat.of (Localization.AtPrime p) N')) :
    (n : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p)
      (LocalizedModule p.primeCompl (M →ₗ[R] N))) := by
  have := Module.finitePresentation_of_finite R M
  have : Module.Finite (Localization.AtPrime p) N' := .of_isLocalizedModule p.primeCompl g
  let d := IsLocalizedModule.mapExtendScalars p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M) g (Localization.AtPrime p)
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (M →ₗ[R] N)) d).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
  rw [IsLocalRing.depth_eq_of_linearEquiv e]
  exact depth_hom_ge hn hdepth

/-- A depth bound at most two on a local ring passes to the localization of the dual of
any finite module. -/
theorem le_depth_localizedModule_dual {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    {n : ℕ} (hn : n ≤ 2)
    (hdepth : (n : ℕ∞) ≤ IsLocalRing.depth
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    (n : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p)
      (LocalizedModule p.primeCompl (Dual R M))) :=
  le_depth_localizedModule_hom p (Algebra.linearMap R (Localization.AtPrime p)) hn hdepth

end Ideal
