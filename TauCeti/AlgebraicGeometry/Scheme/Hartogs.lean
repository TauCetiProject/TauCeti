/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Hartogs

/-!
# Reconstruction from sections across a subset of depth at least two

For an open subset `V` of a Noetherian affine scheme, if the local rings at the omitted
points have depth at least two, the canonical map from the coordinate ring to `Γ(V, 𝒪)`
is bijective. Thus the spectrum of these sections recovers the original affine scheme,
not necessarily the open subset `V`.

In particular, let `B` be a finite algebra over a Noetherian local ring `A`. Removing the
closed fibre of `Spec B → Spec A` does not change global functions provided the local
rings of `B` at maximal ideals have depth at least two. This is the affine form of the
reconstruction used for finite covers of a punctured local spectrum.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I).
* [Stacks Project, Lemma 58.20.1](https://stacks.math.columbia.edu/tag/0BM8).
-/

public section

open CategoryTheory IsLocalRing
open AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

universe u

/-- Functions on an open subset of a Noetherian affine scheme extend uniquely if the local
rings at all omitted points have depth at least two. -/
theorem algebraMap_sections_bijective_of_two_le_depth (R : CommRingCat.{u})
    [IsNoetherianRing R] (V : (Spec R).Opens)
    (hdepth : ∀ p : PrimeSpectrum R, p ∉ V →
      2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime p.asIdeal))) :
    Function.Bijective (algebraMap R Γ(Spec R, V)) := by
  have hlocal (p : PrimeSpectrum R) (hp : p ∉ V) :
      2 ≤ depth (ModuleCat.of (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl R)) := by
    let e := (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
    rw [IsLocalRing.depth_eq_of_linearEquiv e]
    exact hdepth p hp
  have h := tilde_toOpen_bijective_of_two_le_depth (ModuleCat.of R R) V hlocal
  -- `tilde.toOpen` is the constant-fraction map followed by the comparison of module
  -- structures; both comparison maps are the identity on the underlying sections.
  exact h

/-- A finite scheme over a Noetherian local base is recovered from the functions on any
open containing the complement of the closed fibre, provided its local rings at maximal
ideals have depth at least two. The isomorphism is induced by restriction of functions.
This is the affine form of Stacks, Lemma 58.20.1 (0BM8). -/
@[stacks 0BM8 "affine form"]
theorem spec_sections_of_depth (A B : CommRingCat.{u}) [IsNoetherianRing A]
    [IsLocalRing A] [Algebra A B] [Module.Finite A B] (V : (Spec B).Opens)
    (hV : ∀ p : PrimeSpectrum B, p ∉ V → p.asIdeal.under A = maximalIdeal A)
    (hdepth : ∀ (q : Ideal B) [q.IsMaximal],
      2 ≤ depth (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))) :
    IsIso (Spec.map (CommRingCat.ofHom (algebraMap B Γ(Spec B, V)))) := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  have hb := algebraMap_sections_bijective_of_two_le_depth B V fun p hp ↦ by
    have : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isIntegral_of_isMaximal_under p.asIdeal
      (hV p hp ▸ maximalIdeal.isMaximal A)
    exact hdepth p.asIdeal
  have : IsIso (CommRingCat.ofHom (algebraMap B Γ(Spec B, V))) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  infer_instance

end TauCeti.AlgebraicGeometry
