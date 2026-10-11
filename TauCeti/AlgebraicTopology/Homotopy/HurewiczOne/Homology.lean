/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Homotopy.HurewiczOne.Naturality

/-!
# Naturality of the degree-one Hurewicz isomorphism on singular homology

The identification of `1`-cycles modulo boundaries with the first homology group of the singular
chain complex (`TauCeti.HurewiczOne.H₁AddEquivHomology`) is natural in continuous maps. Combined
with `TauCeti.HurewiczOne.H₁Map_hurewiczAb`, the Hurewicz map `π₁(X, x)ᵃᵇ → H₁(X; ℤ)` is natural
with respect to the map induced on singular homology.

## Main results

* `TauCeti.HurewiczOne.homologyMap_H₁AddEquivHomology`: naturality of the identification of
  cycles modulo boundaries with homology.
* `TauCeti.HurewiczOne.homologyMap_hurewicz`: naturality of the Hurewicz map on homology.
* `TauCeti.HurewiczOne.homologyMap_hurewiczHomologyEquiv`: the same for the Hurewicz isomorphism
  of path-connected spaces.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti.HurewiczOne

variable {X Y : TopCat.{0}} (f : X ⟶ Y)

/-- The identification of `1`-cycles modulo boundaries with the first homology group of the
singular chain complex is natural. -/
theorem homologyMap_H₁AddEquivHomology (h : H₁ X) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom (H₁AddEquivHomology X h) =
      H₁AddEquivHomology Y (H₁Map f h) := by
  induction h using QuotientAddGroup.induction_on with | H c =>
  obtain ⟨z, hz⟩ := exists_iCycles_eq c
  have h₁ := congr($(HomologicalComplex.homologyπ_naturality ((singularChains ℤ).map f) 1).hom z)
  have h₂ := congr($(HomologicalComplex.cyclesMap_i ((singularChains ℤ).map f) 1).hom z)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  rw [H₁AddEquivHomology_mk c z hz, h₁, H₁Map_mk]
  refine (H₁AddEquivHomology_mk _ _ ?_).symm
  rw [h₂, hz]

/-- **Naturality of the degree-one Hurewicz map on singular homology**. -/
theorem homologyMap_hurewicz {x : X} (a : Additive (Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (H₁AddEquivHomology X (hurewiczAb x a)) =
      H₁AddEquivHomology Y (hurewiczAb (f x) (Additive.ofMul (Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul))) := by
  rw [homologyMap_H₁AddEquivHomology, H₁Map_hurewiczAb]

/-- **Naturality of the Hurewicz isomorphism** of path-connected spaces. -/
theorem homologyMap_hurewiczHomologyEquiv [PathConnectedSpace X] [PathConnectedSpace Y] {x : X}
    (a : Additive (Abelianization (FundamentalGroup X x))) :
    (HomologicalComplex.homologyMap ((singularChains ℤ).map f) 1).hom
        (hurewiczHomologyEquiv x a) =
      hurewiczHomologyEquiv (f x) (Additive.ofMul (Abelianization.map
        (FundamentalGroup.map f.hom x) a.toMul)) := by
  rw [hurewiczHomologyEquiv_apply, hurewiczHomologyEquiv_apply, homologyMap_hurewicz]

end TauCeti.HurewiczOne
