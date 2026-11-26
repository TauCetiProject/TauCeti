/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.IntegralModel.Basic
public import TauCeti.Algebra.AlgebraicGroup.RootsOfUnity.Smooth

/-!
# `μ_p` over a ring of residue characteristic `p` is not a smooth model

Let `O` be a commutative ring with an algebra map to a field of characteristic `p`, for example
`ℤ_p`. The Hopf algebra `O[x]/(x^p - 1) = O[ℤ/p]` of `μ_{p,O}` is flat over `O`
(it is a group algebra, hence free), but it is not smooth
(`RootsOfUnityGroup.coordinateRing_not_smooth_of_charP`), so it is not the coordinate algebra of
any smooth model `SmoothModel`, whatever the generic fiber.

## Main declarations

* `TauCeti.IntegralModel.SmoothModel.isEmpty_coord_iso_rootsOfUnity`: no smooth model has
  coordinate Hopf algebra isomorphic to `O[ℤ/p]`.
-/

public section

open CategoryTheory

namespace TauCeti.IntegralModel.SmoothModel

universe u

variable {O : Type u} [CommRing O]

/-- **`μ_p` is not a smooth model over a ring of residue characteristic `p`**: when `O` has an
algebra map to a field `κ` of characteristic `p`, no smooth model over `O`, of any affine group
over any `K`, has coordinate Hopf algebra isomorphic to `O[x]/(x^p - 1)`. -/
theorem isEmpty_coord_iso_rootsOfUnity (κ : Type u) [Field κ] [Algebra O κ] (p : ℕ)
    [Fact p.Prime] [CharP κ p] {K : Type u} [CommRing K] [Algebra O K]
    {H : FiniteTypeCommHopfAlgCat.{u, u} K} (𝒢 : SmoothModel O K H) :
    IsEmpty (𝒢.coord ≅
      DiagonalizableGroup.coordinateRing O (RootsOfUnityGroup.characterGroup.{u} p)) :=
  ⟨fun e ↦ RootsOfUnityGroup.coordinateRing_not_smooth_of_charP κ p <|
    Algebra.Smooth.of_equiv (A := 𝒢.coord) (CommHopfAlgCat.ofIso
      ((forget₂ (FiniteTypeCommHopfAlgCat.{u, u} O) (CommHopfAlgCat.{u} O)).mapIso e)).toAlgEquiv⟩

end TauCeti.IntegralModel.SmoothModel
