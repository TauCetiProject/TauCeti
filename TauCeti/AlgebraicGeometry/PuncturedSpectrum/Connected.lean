/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.PuncturedSpectrum
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.Depth.Basic
import TauCeti.AlgebraicGeometry.PuncturedSpectrum.Sections
import TauCeti.AlgebraicGeometry.Scheme.Connected.Basic

/-!
# Connectedness of the punctured spectrum

If `R` is a Noetherian local ring of depth at least two, then its punctured spectrum
`U = Spec R ∖ {𝔪}` is connected (`TauCeti.IsLocalRing.connectedSpace_puncturedSpectrum`). It is
nonempty since `R` has positive Krull dimension
(`TauCeti.IsLocalRing.nonempty_puncturedSpectrum_iff`).

Connectedness comes from the algebraic Hartogs principle: in depth at least two, restriction
`R = Γ(Spec R, 𝒪) → Γ(U, 𝒪)` is bijective. A decomposition of `U` into two disjoint nonempty open
subsets `V` and `W` would make `Γ(U, 𝒪) ≅ Γ(V, 𝒪) × Γ(W, 𝒪)` a product of two nonzero rings, which
is not local (`AlgebraicGeometry.Scheme.connectedSpace_of_isLocalRing_Γ`).

Depth one does not suffice: two planes in affine four-space meeting in a single point have a
local ring of depth one at that point, and its punctured spectrum is the disjoint union of the two
punctured planes.

Connectedness of `U` is what makes finite étale covers of `U` behave like those of a connected
scheme, for instance when restricting them to the punctured spectrum of a hypersurface section,
as in Stacks, Lemma 58.19.7 (0BLJ).

## Main results

* `TauCeti.IsLocalRing.connectedSpace_puncturedSpectrum`: the punctured spectrum of a Noetherian
  local ring of depth at least two is connected.

## References

* [Stacks Project, Lemma 31.5.11](https://stacks.math.columbia.edu/tag/0E9I), extension of
  sections across a closed subset of depth at least two.
* R. Hartshorne, *Complete intersections and connectedness*, Amer. J. Math. 84 (1962),
  Proposition 2.1.
-/

public section

open CategoryTheory Limits Opposite AlgebraicGeometry

universe u

namespace TauCeti.IsLocalRing

variable (R : Type u) [CommRing R] [IsLocalRing R]

/-- **The punctured spectrum is connected in depth at least two.** For a Noetherian local ring
`R` of depth at least two, the complement of the closed point of `Spec R` is connected. -/
theorem connectedSpace_puncturedSpectrum [IsNoetherianRing R]
    (hdepth : 2 ≤ _root_.IsLocalRing.depth (ModuleCat.of R R)) :
    ConnectedSpace (puncturedSpectrum R).toScheme := by
  -- By the Hartogs principle, the global functions on the punctured spectrum are `R`.
  have := isIso_appTop_ι_puncturedSpectrum R hdepth
  have : _root_.IsLocalRing Γ((puncturedSpectrum R).toScheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of R)).symm ≪≫
      asIso (puncturedSpectrum R).ι.appTop).commRingCatIsoToRingEquiv.isLocalRing
  exact Scheme.connectedSpace_of_isLocalRing_Γ _

end TauCeti.IsLocalRing
