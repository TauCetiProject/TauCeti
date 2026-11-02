/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Homological.GroupHomology.Basic

/-!
# Group homology from a projective resolution, through a comparison map

For a projective resolution `P` of the trivial representation `k` of `G`, Mathlib's
`groupHomologyIso A n P : Hₙ(G, A) ≅ Hₙ((A ⊗ P)_G)` is defined through `Tor`. This file makes it
explicit: given a chain map `φ` from the bar resolution of `G` to `P` lying over the identity of
`k`, it is the map induced on homology by

`Cₙ(G, A) ≅ (A ⊗ bar)_G ⟶ (A ⊗ P)_G`,

the identification of the inhomogeneous chains with the bar coinvariants followed by `A ⊗ φ`.
This is the homological counterpart of `TauCeti.Rep.groupCohomologyIso_inv_eq_homologyMap`.

## Main results

* `Rep.groupHomologyIso_hom_eq_homologyMap`: `groupHomologyIso A n P` is the map on
  homology induced by a comparison map from the bar resolution to `P`.

## References

* K. S. Brown, *Cohomology of Groups*, Graduate Texts in Mathematics 87, Springer (1982),
  Chapter I, §7 (comparison of projective resolutions) and Chapter III, §1.

The comparisons `groupHomologyIso` and `groupHomology.inhomogeneousChainsIso` are Mathlib's
constructions by Amelia Livingston; the proof uses Mathlib's computation of left derived functors
by projective resolutions, `ProjectiveResolution.isoLeftDerivedObj_hom_naturality`.
-/

public section

open CategoryTheory

namespace Rep

universe u

variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G] (A : Rep.{u} k G)

/-- **Group homology from a projective resolution, through a comparison map.** For a projective
resolution `P` of the trivial representation `k` and a chain map `φ` from the bar resolution to `P`
lying over the identity of `k`, `groupHomologyIso A n P` is the map on homology induced by the
identification of the inhomogeneous chains with `(A ⊗ bar)_G` followed by `A ⊗ φ`. -/
theorem groupHomologyIso_hom_eq_homologyMap (P : ProjectiveResolution (Rep.trivial k G k))
    (φ : Rep.barComplex k G ⟶ P.complex)
    (comm : φ.f 0 ≫ P.π.f 0 = (Rep.barResolution k G).π.f 0) (n : ℕ) :
    (groupHomologyIso A n P).hom = HomologicalComplex.homologyMap
      ((groupHomology.inhomogeneousChainsIso A).hom ≫
        (((Rep.coinvariantsTensor k G).obj A).mapHomologicalComplex _).map φ) n := by
  have h := ProjectiveResolution.isoLeftDerivedObj_hom_naturality (𝟙 _)
    (Rep.barResolution k G) P φ (comm.trans (Category.comp_id _).symm)
    ((Rep.coinvariantsTensor k G).obj A) n
  rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
  -- `groupHomologyIso` is `groupHomologyIsoTor` followed by the `Tor` computation from `P`,
  -- and `groupHomologyIsoTor` is the inhomogeneous chain isomorphism followed by the inverse
  -- `Tor` computation from the bar resolution.
  have h₁ : (groupHomologyIso A n P).hom = _ := Iso.trans_hom _ _
  have h₂ : (groupHomologyIsoTor A n).hom = _ := Iso.trans_hom _ _
  rw [h₁, h₂, Iso.symm_hom, isoOfQuasiIsoAt_hom, HomologicalComplex.homologyMap_comp]
  -- The homotopy equivalence `HomotopyEquiv.ofIso e` has forward map `e.hom` by definition, and
  -- `groupHomology A n` is the homology of the inhomogeneous chains by definition; `exact`
  -- compares these presentations up to unfolding.
  exact (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Iso.inv_comp_eq _).2 h))

end Rep
