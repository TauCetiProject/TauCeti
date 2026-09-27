/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.RegularLocalRing.Defs

/-!
# Regular local rings of schemes

On an affine open with Noetherian ring of sections, regularity of that ring is equivalent to
regularity of the local rings at every point of the open. In particular, the local rings of the
spectrum of a regular ring are regular.

## Main declarations

* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_isRegularRing`
* `TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk`
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_Spec`
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If the sections over an affine open `U` form a regular ring, the local rings at the points of
`U` are regular. -/
theorem isRegularLocalRing_stalk_of_isRegularRing {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsRegularRing Γ(X, U)] {x : X} (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact .of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The sections over an affine open `U` with Noetherian ring of sections form a regular ring
exactly when the local rings at the points of `U` are regular. -/
theorem isRegularRing_iff_isRegularLocalRing_stalk {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsRegularRing Γ(X, U) ↔ ∀ x ∈ U, IsRegularLocalRing (X.presheaf.stalk x) := by
  refine ⟨fun _ _ hx ↦ isRegularLocalRing_stalk_of_isRegularRing hU hx, fun h ↦ ?_⟩
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  -- The prime `p` is the prime of the point `hU.fromSpec y` of `U`, whose stalk is `Γ(X, U)_p`.
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  have := h _ hy
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

/-- The local rings of the spectrum of a regular ring are regular. -/
instance isRegularLocalRing_stalk_Spec (R : CommRingCat.{u}) [IsRegularRing R] (x : Spec R) :
    IsRegularLocalRing ((Spec R).presheaf.stalk x) :=
  have : IsRegularRing Γ(Spec R, ⊤) :=
    .of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  isRegularLocalRing_stalk_of_isRegularRing (isAffineOpen_top _) (Set.mem_univ x)

end AlgebraicGeometry

end TauCeti
