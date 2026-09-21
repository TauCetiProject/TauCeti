/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PrincipalParts.Basic
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Picard
public import TauCeti.Topology.KrullDimension

/-!
# Vanishing of the cohomology of line bundles on a curve above degree one

On a Noetherian integral scheme whose codimension-one points are closed and have discrete
valuation rings as local rings, the sheaf `𝒪_X(D)` of a Weil divisor has the flasque resolution
`0 ⟶ 𝒪_X(D) ⟶ 𝒦_X ⟶ 𝒦_X / 𝒪_X(D) ⟶ 0` of
`TauCeti/AlgebraicGeometry/WeilDivisor/Scheme/PrincipalParts/Basic.lean`. Flasque sheaves are
acyclic, so the long exact cohomology sequence gives `Hⁱ(X, 𝒪_X(D)) = 0` for `i ≥ 2`. Since every
line bundle on a curve is isomorphic to some `𝒪_X(D)`, the same holds for every line bundle.

## Main declarations

* `SchemeWeilDivisor.subsingleton_cohomology_sheaf_add_two`: `Hⁿ⁺²(X, 𝒪_X(D)) = 0` when the
  codimension-one points are closed;
* `SchemeWeilDivisor.subsingleton_cohomology_add_two_of_invertibleSheaf`: `Hⁿ⁺²(X, L) = 0` for
  every invertible sheaf `L` on a Noetherian integral scheme of dimension at most one whose
  codimension-one local rings are discrete valuation rings.

In degree one the same resolution identifies `H¹(X, 𝒪_X(D))` with the cokernel of
`H⁰(X, 𝒦_X) ⟶ H⁰(X, 𝒦_X / 𝒪_X(D))`, by `Scheme.Modules.cohomologyOneLinearEquivOfIsFlasque`
applied to `SchemeWeilDivisor.principalPartsShortComplex_shortExact`.

The acyclicity of flasque sheaves is
`Scheme.Modules.subsingleton_cohomology_succ_of_isFlasque`, the long exact sequence is
`TauCeti/AlgebraicGeometry/Cohomology/LongExactSequence.lean`, and the comparison of line bundles
with divisor sheaves is `SchemeWeilDivisor.exists_nonempty_iso_sheaf`.

## References

* R. Hartshorne, *Algebraic Geometry*, III, Proposition 2.5 (flasque sheaves are acyclic) and
  Theorem 2.7 (Grothendieck vanishing, of which the statements here are a special case).
* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II, §5.
-/

public section

open CategoryTheory Order TopologicalSpace AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

namespace SchemeWeilDivisor

variable {X : Scheme.{u}} [IsIntegral X] [IsNoetherian X]
  [∀ x : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (x : X))]

/-- **The sheaf of a Weil divisor has no cohomology above degree one** on a Noetherian integral
scheme whose codimension-one points are closed and have discrete valuation rings as local rings:
the flasque resolution `0 ⟶ 𝒪_X(D) ⟶ 𝒦_X ⟶ 𝒦_X / 𝒪_X(D) ⟶ 0` has length one. -/
theorem subsingleton_cohomology_sheaf_add_two
    (hclosed : ∀ x : CodimensionOnePoint X, IsClosed ({(x : X)} : Set X))
    (D : SchemeWeilDivisor X) (n : ℕ) :
    Subsingleton (Scheme.Modules.Cohomology (sheaf D) (n + 2)) :=
  have : (principalPartsShortComplex D).X₂.presheaf.IsFlasque :=
    principalPartsShortComplex_X₂ D ▸
      inferInstanceAs (Scheme.rationalFunctions X).presheaf.IsFlasque
  have : (principalPartsShortComplex D).X₃.presheaf.IsFlasque :=
    principalPartsShortComplex_X₃ D ▸
      inferInstanceAs (principalParts D).presheaf.IsFlasque
  principalPartsShortComplex_X₁ D ▸
    Scheme.Modules.subsingleton_cohomology_X₁ (principalPartsShortComplex_shortExact hclosed D)
      (n + 1) (n + 2) rfl inferInstance inferInstance

/-- **Line bundles on a curve have no cohomology above degree one.** On a Noetherian integral
scheme of dimension at most one whose codimension-one local rings are discrete valuation rings,
`Hⁱ(X, L) = 0` for every invertible sheaf `L` and every `i ≥ 2`. -/
theorem subsingleton_cohomology_add_two_of_invertibleSheaf (hX : ∀ y : X, coheight y ≤ 1)
    (L : InvertibleSheaf X) (n : ℕ) : Subsingleton (Scheme.Modules.Cohomology L.obj (n + 2)) := by
  obtain ⟨D, ⟨e⟩⟩ := exists_nonempty_iso_sheaf hX L
  have : Subsingleton ((Scheme.Modules.cohomologyFunctor X (n + 2)).obj (sheaf D)) :=
    subsingleton_cohomology_sheaf_add_two
      (fun x ↦ isClosed_singleton_of_forall_coheight_le_one_of_coheight_eq_one hX x.2) D n
  exact ((Scheme.Modules.cohomologyFunctor X (n + 2)).mapIso e).addCommGroupIsoToAddEquiv.injective
    |>.subsingleton

end SchemeWeilDivisor

end AlgebraicGeometry

end TauCeti
