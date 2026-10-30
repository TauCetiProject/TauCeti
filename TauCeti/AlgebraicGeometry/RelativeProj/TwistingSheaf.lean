/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Localization
public import TauCeti.AlgebraicGeometry.RelativeProj.Basic

/-!
# The twisting sheaves on the charts of a relative `Proj`

Let `A` be a graded algebra on a scheme `X` with quasi-coherent homogeneous components. The
relative `Proj` of `A` is glued from the charts `Proj (⨁ n, Γ(Aₙ, U))` over the affine opens `U`
of `X`, along the morphisms `Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))` induced by
restriction of sections to basic opens `D(f) ⊆ U`. Each chart carries its twisting sheaves `𝒪(n)`,
and these morphisms induce maps between them (`AlgebraicGeometry.Proj.twistingSheafMap`).

This file proves that these maps are isomorphisms over the overlap: the pullback of sections of
`𝒪(n)` from an open `W` of `Proj (⨁ n, Γ(Aₙ, U))` inside the locus where `f` is invertible is
bijective. This is the compatibility of twisting sheaves with restriction to basic opens through
which the twisting sheaves of the charts glue to the twisting sheaves of the relative `Proj`. It
holds because restriction of sections is the localization away from `f` in degree zero
(`CategoryTheory.CommMon.isLocalization_gradedSections_basicOpen`).

## Main results

* `CategoryTheory.CommMon.bijective_comap_twistingSheaf_restrictGradedSections`: the pullback of
  sections of twisting sheaves along a transition map of the charts of the relative `Proj` is
  bijective over the locus where `f` is invertible.

## References

* [The Stacks Project, Section 27.15, Relative Proj](https://stacks.math.columbia.edu/tag/01NS)
-/

public section

open CategoryTheory DirectSum

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {X : Scheme.{u}} (A : CommMon (GradedObject ℕ X.Modules)) [∀ n, (A.X n).IsQuasicoherent]

/-- **The twisting sheaves of the charts of the relative `Proj` agree on overlaps.** For an affine
open `U` of `X` and `f ∈ Γ(X, U)`, the pullback of sections of `𝒪(n)` along
`Proj (⨁ n, Γ(Aₙ, D(f))) ⟶ Proj (⨁ n, Γ(Aₙ, U))` is bijective over every open `W` of
`Proj (⨁ n, Γ(Aₙ, U))` on which the image of `f` in degree zero is invertible. -/
theorem _root_.CategoryTheory.CommMon.bijective_comap_twistingSheaf_restrictGradedSections
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U)) (n : ℤ)
    {W : (Proj (A.gradedSectionsGrading U)).Opens}
    (hW : W ≤ Proj.basicOpen _ (algebraMap Γ(X, U) (⨁ n, Γ(A.X n, U)) f)) :
    Function.Bijective (Proj.twistingSheaf.comap (n := n) (U := W)
      (V := Proj.map _ (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU _) ⁻¹ᵁ W)
      (A.restrictGradedSectionsGradedHom (homOfLE (X.basicOpen_le f)))
      (A.irrelevant_le_map_restrictGradedSectionsGradedHom f hU _) Set.Subset.rfl) :=
  Proj.twistingSheaf.bijective_comap_of_isLocalizationAway _ _
    (SetLike.algebraMap_mem_graded _ f) (by
      rw [CommMon.restrictGradedSectionsGradedHom_toRingHom]
      exact A.isLocalization_gradedSections_basicOpen hU f) hW

end TauCeti
