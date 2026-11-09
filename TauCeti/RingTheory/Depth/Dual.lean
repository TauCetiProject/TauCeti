/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Depth.Basic
public import Mathlib.Algebra.Module.FinitePresentation

/-!
# Depth of localized dual modules

For a finite module over a Noetherian ring, localization commutes with taking its dual.
Consequently the depth bound for a module of homomorphisms applies to localized duals:
a bound at most two on the depth of the local ring also bounds the depth of the dual.
This is useful for extending maps across subsets of codimension at least two.

## References

* Stacks Project, Lemma 15.24.10 (Tag 0AV5).
-/

public section

open Module IsLocalRing

namespace Ideal

universe u

/-- A depth bound at most two on a local ring passes to the localization of the dual of
any finite module. -/
theorem le_depth_localizedModule_dual {R M : Type u} [CommRing R] [IsNoetherianRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] (p : Ideal R) [p.IsPrime]
    {n : ℕ} (hn : n ≤ 2)
    (hdepth : (n : ℕ∞) ≤ IsLocalRing.depth
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime p))) :
    (n : ℕ∞) ≤ IsLocalRing.depth (ModuleCat.of (Localization.AtPrime p)
      (LocalizedModule p.primeCompl (Dual R M))) := by
  have := Module.finitePresentation_of_finite R M
  let d := IsLocalizedModule.mapExtendScalars p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl M)
    (Algebra.linearMap R (Localization.AtPrime p)) (Localization.AtPrime p)
  let e := (IsLocalizedModule.linearEquiv p.primeCompl
    (LocalizedModule.mkLinearMap p.primeCompl (Dual R M)) d).extendScalarsOfIsLocalization
      p.primeCompl (Localization.AtPrime p)
  rw [IsLocalRing.depth_eq_of_linearEquiv e]
  exact depth_hom_ge hn hdepth

end Ideal
