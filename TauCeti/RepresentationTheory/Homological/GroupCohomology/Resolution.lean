/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import TauCeti.Algebra.Homology.Ext.ProjectiveResolution

/-!
# Group cohomology from a projective resolution, through a comparison map

For a projective resolution `P` of the trivial representation `k` of `G`, Mathlib's
`groupCohomologyIso A n P : Hⁿ(G, A) ≅ Hⁿ(Hom(P, A))` is defined through `Ext`. This file makes its
inverse explicit: given a chain map `φ` from the bar resolution of `G` to `P` lying over the
identity of `k`, it is the map induced on cohomology by

`Hom(P, A) ⟶ Hom(bar, A) ≅ Fun(Gⁿ, A)`,

precomposition with `φ` followed by the identification of `Hom(bar, A)` with the inhomogeneous
cochains. This is how an explicit comparison map computes a cohomology isomorphism that Mathlib
constructs abstractly, such as Shapiro's isomorphism or the periodicity isomorphism of a finite
cyclic group.

## Main results

* `TauCeti.groupCohomologyIso_inv_eq_homologyMap`: the inverse of `groupCohomologyIso A n P` is
  the map on cohomology induced by a comparison map from the bar resolution to `P`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §7 (comparison of projective resolutions).
-/

public section

open CategoryTheory

namespace TauCeti

universe u

variable {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G)

/-- **Group cohomology from a projective resolution, through a comparison map.** For a projective
resolution `P` of the trivial representation `k` and a chain map `φ` from the bar resolution to `P`
lying over the identity of `k`, the inverse of `groupCohomologyIso A n P` is the map on cohomology
induced by precomposition with `φ`, followed by the identification of `Hom(bar, A)` with the
inhomogeneous cochains. -/
theorem groupCohomologyIso_inv_eq_homologyMap (P : ProjectiveResolution (Rep.trivial k G k))
    (φ : (Rep.barResolution k G).complex ⟶ P.complex)
    (comm : φ.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0) (n : ℕ) :
    (groupCohomologyIso A n P).inv = HomologicalComplex.homologyMap
      ((HomologicalComplex.unopFunctor _ _).map
        ((((linearYoneda k (Rep k G)).obj A).rightOp.mapHomologicalComplex _).map φ).op ≫
        (groupCohomology.inhomogeneousCochainsIso A).inv) n := by
  have hext := ProjectiveResolution.isoExt_hom_comp_homologyMap (R := k)
    (Rep.barResolution k G) P φ comm n A
  have hinhom : (isoOfQuasiIsoAt
      (HomotopyEquiv.ofIso (groupCohomology.inhomogeneousCochainsIso A)).hom n).inv =
      HomologicalComplex.homologyMap (groupCohomology.inhomogeneousCochainsIso A).inv n :=
    Iso.inv_ext ((HomologicalComplex.homologyMap_comp _ _ n).symm.trans
      ((congrArg (HomologicalComplex.homologyMap · n)
        (groupCohomology.inhomogeneousCochainsIso A).hom_inv_id).trans
        (HomologicalComplex.homologyMap_id _ n)))
  -- `groupCohomologyIso` is `groupCohomologyIsoExt` followed by the `Ext` computation from `P`,
  -- and `groupCohomologyIsoExt` is the `Ext` computation from the bar resolution followed by the
  -- inhomogeneous cochain isomorphism. The unfolding is taken from the `Iso.trans` lemmas, not
  -- restated and proved by `rfl`: restated, its `Ext` objects carry fresh instance terms and the
  -- kernel unfolds `Ext` to match.
  have h₁ : (groupCohomologyIso A n P).inv = _ := Iso.trans_inv _ _
  have h₂ : (groupCohomologyIsoExt A n).inv = _ := Iso.trans_inv _ _
  rw [h₁, h₂, Iso.symm_inv, hinhom]
  exact ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) ((Iso.inv_comp_eq _).2 hext.symm))).trans
      (HomologicalComplex.homologyMap_comp _ _ n).symm

end TauCeti
