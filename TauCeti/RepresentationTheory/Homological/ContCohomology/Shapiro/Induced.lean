/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Coinduced.Induced
public import TauCeti.RepresentationTheory.Homological.ContCohomology.Shapiro.Algebraic

/-!
# Continuous Shapiro on induced coefficients

For an open subgroup of a profinite group, continuous cohomology with genuine algebraically
induced smooth discrete coefficients is isomorphic to the cohomology of the subgroup. The
forward map is the compatible-pair map of subgroup inclusion and the transported evaluation
counit. The finite-index comparison carries it to the algebraic coinduced Shapiro map in
every degree, and it is natural in the coefficient representation.

The coefficient carrier and finite-index comparison come from Amelia Livingston's
`Representation.ind` and `Rep.indCoindIso` in Mathlib. These cohomology groups retain the
original topology on the group. The common group/coefficient universe contains the ring
universe, combining the pinned induction comparison with the canonical continuous Shapiro API.

## References

* L. Ribes, P. Zalesskii, *Profinite Groups*, second edition, Thm. 6.10.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, second edition,
  (1.6.4), with the footnote on p. 61 that uses `Ind` for coinduction.
-/

public section

open CategoryTheory

namespace TauCeti.ContinuousCohomology

universe u v

variable {R : Type v} [CommRing R] [TopologicalSpace R]
  {G : Type (max u v)} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] (U : OpenSubgroup G)
  (A : SmoothDiscreteTopRep.{v, max u v, max u v} R U.toSubgroup)

/-- Restriction followed by the evaluation counit on genuine induced coefficients, equipped
with their smooth discrete topology. -/
noncomputable def inducedShapiroMap (n : ℕ) :
    continuousCohomology n (algebraicIndAsSmooth.{max u v, v, 0} R G U A).obj ⟶
      continuousCohomology n A.obj :=
  _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    (algebraicIndCounit.{max u v, v, 0} R G U A) n

/-- The compatible pair defining induced Shapiro consists of subgroup inclusion and the
induced evaluation counit. -/
theorem inducedShapiroMap_def (n : ℕ) :
    inducedShapiroMap.{u, v} U A n =
      _root_.ContinuousCohomology.map (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
        (algebraicIndCounit.{max u v, v, 0} R G U A) n := (rfl)

/-- The finite-index induction/coinduction comparison intertwines their canonical continuous
Shapiro maps in every degree. -/
@[reassoc]
theorem coeffMap_algebraicIndCoindIso_comp_algebraicShapiroMap (n : ℕ) :
    coeffMap (algebraicIndCoindIso.{max u v, v, 0} R G U A).hom.hom n ≫ algebraicShapiroMap U A n =
      inducedShapiroMap.{u, v} U A n := by
  have h := map_comp_coeffMap (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    (algebraicIndCounit.{max u v, v, 0} R G U A) (TopRep.ofHom (algebraicCoindCounit R G U A))
    (algebraicIndCoindIso.{max u v, v, 0} R G U A).hom.hom (𝟙 A.obj)
    ((algebraicIndCounit_def R G U A).symm.trans (Category.comp_id _).symm) n
  simpa only [coeffMap_id, Category.comp_id, algebraicShapiroMap_def,
    inducedShapiroMap_def] using h.symm

/-- Induced Shapiro is an isomorphism for an open subgroup of a profinite group. -/
theorem isIso_inducedShapiroMap [TotallyDisconnectedSpace G] (n : ℕ) :
    IsIso (inducedShapiroMap.{u, v} U A n) := by
  let e := (smoothDiscreteι R G).mapIso (algebraicIndCoindIso.{max u v, v, 0} R G U A)
  let eH := (continuousCohomologyFunctor (R := R) G n).mapIso e
  have : IsIso (coeffMap (algebraicIndCoindIso.{max u v, v, 0} R G U A).hom.hom n) :=
    inferInstanceAs (IsIso eH.hom)
  have := isIso_algebraicShapiroMap U A n
  rw [← coeffMap_algebraicIndCoindIso_comp_algebraicShapiroMap.{u, v}]
  infer_instance

/-- Continuous Shapiro's isomorphism with genuine induced smooth discrete coefficients. Its
forward map is subgroup restriction followed by the transported evaluation counit. -/
noncomputable def inducedShapiroIso [TotallyDisconnectedSpace G] (n : ℕ) :
    continuousCohomology n (algebraicIndAsSmooth.{max u v, v, 0} R G U A).obj ≅
      continuousCohomology n A.obj :=
  have := isIso_inducedShapiroMap.{u, v} U A n
  asIso (inducedShapiroMap.{u, v} U A n)

/-- The induced Shapiro isomorphism has the restriction/evaluation forward map. -/
@[simp]
theorem inducedShapiroIso_hom [TotallyDisconnectedSpace G] (n : ℕ) :
    (inducedShapiroIso.{u, v} U A n).hom = inducedShapiroMap.{u, v} U A n := by
  rw [inducedShapiroIso, asIso_hom]

/-- The topological induction/coinduction comparison carries induced continuous Shapiro to
the canonical coinduced Shapiro map. -/
@[reassoc]
theorem coeffMap_topologicalIndCoindIso_comp_shapiroMapTopRep (n : ℕ) :
    coeffMap (topologicalIndCoindIso.{max u v, v, 0} R G U A).hom.hom n ≫
        shapiroMapTopRep U.toSubgroup A n = inducedShapiroMap.{u, v} U A n := by
  rw [← coeffMap_topologicalCoindIsoAlgebraic_comp_algebraicShapiroMap,
    ← Category.assoc, ← coeffMap_comp]
  rw [topologicalIndCoindIso_hom_comp_topologicalCoindIsoAlgebraic,
    coeffMap_algebraicIndCoindIso_comp_algebraicShapiroMap.{u, v}]

/-- The induced Shapiro isomorphism agrees with locally constant Shapiro under the
induction–coinduction coefficient comparison. -/
@[reassoc]
theorem coeffMap_topologicalIndCoindIso_comp_shapiroIso [TotallyDisconnectedSpace G]
    (n : ℕ) :
    coeffMap (topologicalIndCoindIso.{max u v, v, 0} R G U A).hom.hom n ≫
      (shapiroIsoTopRep U.toSubgroup U.isClosed A n).hom =
        (inducedShapiroIso.{u, v} U A n).hom := by
  rw [shapiroIsoTopRep_hom]
  exact (coeffMap_topologicalIndCoindIso_comp_shapiroMapTopRep.{u, v} U A n).trans
    (inducedShapiroIso_hom.{u, v} U A n).symm

variable {A}
  {B : SmoothDiscreteTopRep.{v, max u v, max u v} R U.toSubgroup}

/-- Induced continuous Shapiro is natural in the smooth discrete coefficient representation. -/
@[reassoc]
theorem inducedShapiroMap_naturality (f : A ⟶ B) (n : ℕ) :
    coeffMap (algebraicIndMap.{max u v, v, 0} R G U f).hom n ≫ inducedShapiroMap.{u, v} U B n =
      inducedShapiroMap.{u, v} U A n ≫ coeffMap f.hom n := by
  exact (map_comp_coeffMap (ContinuousMonoidHom.subgroupSubtype U.toSubgroup)
    (algebraicIndCounit.{max u v, v, 0} R G U A) (algebraicIndCounit.{max u v, v, 0} R G U B)
    (algebraicIndMap.{max u v, v, 0} R G U f).hom f.hom
    (algebraicIndCounit_naturality R G U f) n).symm

end TauCeti.ContinuousCohomology
