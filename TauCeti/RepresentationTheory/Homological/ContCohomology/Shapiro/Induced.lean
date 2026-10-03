/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Induced.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Algebraic

/-!
# Continuous Shapiro on induced coefficients

For an open subgroup of a profinite group, continuous cohomology with algebraically
induced smooth discrete coefficients is isomorphic to the subgroup's cohomology in every
degree. The isomorphism first uses Mathlib's finite-index induction–coinduction comparison
and then the canonical continuous Shapiro map. The forward map therefore has the same
restriction/evaluation normalization as Shapiro on locally constant coinduction.

Induction uses the tensor-coinvariant carrier, with the discrete topology supplied by
`TauCeti.algebraicIndAsSmooth`. The scalar ring may live in its own universe; the coefficient
universe contains both the group and the ring, since the induced tensor product contains
the group algebra. The groups retain their original profinite topologies.

## References

* Mathlib's `Rep.indCoindIso`, by Amelia Livingston.
* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, Thm. 6.10.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.6.4), with the footnote on p. 61 distinguishing coinduction from induction.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type v} [CommRing R] [TopologicalSpace R]
  {G : Type (max u v)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  (U : OpenSubgroup G) (A : SmoothDiscreteTopRep.{v, max u v, max u v} R U.toSubgroup)

/-- Continuous Shapiro for the algebraically induced representation of an open subgroup,
with the discrete topology, in every degree. -/
noncomputable def inducedShapiroIso (n : ℕ) :
    continuousCohomology n (algebraicIndAsSmooth.{max u v, v, 0} R G U A).obj ≅
      continuousCohomology n A.obj :=
  (continuousCohomologyFunctor (R := R) G n).mapIso
    ((smoothDiscreteι R G).mapIso (algebraicIndIsoCoind.{max u v, v, 0} R G U A)) ≪≫
      algebraicShapiroIso U A n

/-- The induced Shapiro map is coefficient transport by the algebraic finite-index
comparison followed by restriction and evaluation at `1`. -/
@[simp]
theorem inducedShapiroIso_hom (n : ℕ) :
    (inducedShapiroIso.{u, v} (R := R) (G := G) U A n).hom =
      coeffMap (R := R) (G := G) (algebraicIndIsoCoind.{max u v, v, 0} R G U A).hom.hom n
        ≫ algebraicShapiroMap U A n := by
  -- The inclusion forgets the smoothness property, and cohomology maps coefficients by
  -- `coeffMap`; reduce those categorical wrappers, then use the existing Shapiro computation.
  dsimp only [inducedShapiroIso, continuousCohomologyFunctor, Functor.mapIso,
    Iso.trans_hom, smoothDiscreteι]
  rw [algebraicShapiroIso_hom]
  rfl

/-- The induced Shapiro isomorphism agrees with locally constant Shapiro under the
induction–coinduction coefficient comparison. -/
@[reassoc]
theorem coeffMap_topologicalIndIsoCoind_comp_shapiroIso (n : ℕ) :
    coeffMap (R := R) (G := G) (topologicalIndIsoCoind.{max u v, v, 0} R G U A).hom.hom n ≫
      (shapiroIsoTopRep U.toSubgroup U.isClosed A n).hom =
        (inducedShapiroIso.{u, v} (R := R) (G := G) U A n).hom := by
  rw [topologicalIndIsoCoind_def, Iso.trans_hom, ObjectProperty.FullSubcategory.comp_hom,
    coeffMap_comp, Category.assoc, shapiroIsoTopRep_hom, inducedShapiroIso_hom]
  rw [← coeffMap_topologicalCoindIsoAlgebraic_comp_algebraicShapiroMap U A n]
  simp only [← Category.assoc, ← coeffMap_comp]
  simp only [Category.assoc, Iso.symm_hom, ObjectProperty.isoInv_hom_id_hom,
    Category.comp_id]

end TauCeti.ContinuousCohomology
