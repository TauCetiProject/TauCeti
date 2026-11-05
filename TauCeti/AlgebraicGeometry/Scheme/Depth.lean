/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import TauCeti.RingTheory.Depth.Basic

/-!
# Depth of the local rings of a scheme on an affine chart

Let `f : Spec R ⟶ X` be an open immersion. It identifies the local ring `𝒪_{X,f(𝔭)}` with the
stalk of `Spec R` at `𝔭`, which is the localization `R_𝔭`. So depth conditions on the local rings
of `X` at points of the chart are depth conditions on localizations of `R`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.depth_stalk_eq_depth_localization`: for an open immersion
  `f : Spec R ⟶ X` with `R` Noetherian, `depth 𝒪_{X,f(𝔭)} = depth R_𝔭`.
-/

public section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- Let `f : Spec R ⟶ X` be an open immersion from the spectrum of a Noetherian ring. The local
ring of `X` at the image of a prime `𝔭` of `R` has the same depth as `R_𝔭`. -/
theorem depth_stalk_eq_depth_localization {R : CommRingCat.{u}} [IsNoetherianRing R]
    {X : Scheme.{u}} (f : Spec R ⟶ X) [IsOpenImmersion f] (p : PrimeSpectrum R) :
    depth (ModuleCat.of (X.presheaf.stalk (f p)) (X.presheaf.stalk (f p))) =
      depth (ModuleCat.of (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal)) :=
  have := (IsOpenImmersion.iff_isIso_stalkMap (f := f)).mp inferInstance |>.2 p
  (asIso (f.stalkMap p) ≪≫ Spec.stalkIso R p).commRingCatIsoToRingEquiv.symm.depth_self_eq.symm

end AlgebraicGeometry.Scheme.Hom
