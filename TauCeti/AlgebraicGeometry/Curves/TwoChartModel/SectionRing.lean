/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.FieldTheory.FunctionField.RiemannRoch.SectionRing

/-!
# The section-ring charts of the two-chart model

Let `F / k` be an algebraic function field and let `z ∈ Fˣ`. The degree-one sections `1` and
`z` of the pole divisor `(z)_∞` define two standard opens in `Proj` of its section ring. This
file identifies their homogeneous coordinate rings with the holomorphy rings used to construct
the two-chart model:

* localization at `X` gives the finite chart, where `z` is regular;
* localization at `z X` gives the infinity chart, where `z⁻¹` is regular.

Thus each standard open is canonically isomorphic to the corresponding affine chart of
`TauCeti.AlgebraicGeometry.twoChartModel`. These are the local identifications needed to compare
the gluing construction with `Proj` of the pole-divisor section ring.

The ring identifications are `TauCeti.Divisor.sectionRingAwayOneEquiv` and
`TauCeti.Divisor.sectionRingAwayGeneratorEquiv`; this file composes them with Mathlib's
`AlgebraicGeometry.Proj.basicOpenIsoSpec`.

## Main definitions

* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`: the resulting
  isomorphism from the standard open `D₊(X)` to the finite chart.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso`: the resulting
  isomorphism from the standard open `D₊(z X)` to the infinity chart.

## Main results

* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso_hom` and
  `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso_hom`: the chart
  isomorphisms are the canonical maps `D₊(f) ⟶ Spec A₍f₎` followed by the ring identifications.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjChart_cover`: the two standard opens
  cover `Proj`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
-/

public section

open CategoryTheory Polynomial HomogeneousLocalization

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

namespace AlgebraicGeometry.twoChartModel

open Divisor

/-- The standard open `D₊(X)` of `Proj` of the section ring of `(z)_∞` is the finite affine
chart of the two-chart model. -/
noncomputable def sectionRingProjFiniteChartIso (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z))
      (polesSectionOne hF z)).toScheme ≅
      Spec (.of (holomorphyRing {P : Place k F | (z : F) ∈ P.integers})) :=
  Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z))
      (polesSectionOne hF z) (monomialDegreeOne_mem_sectionRingGrade _) (by simp) ≪≫
    Scheme.Spec.mapIso (sectionRingAwayOneEquiv hF z).toRingEquiv.toCommRingCatIso.symm.op

/-- The chart isomorphism `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`
is Mathlib's isomorphism `D₊(X) ≅ Spec A₍X₎` followed by the map induced by
`TauCeti.Divisor.sectionRingAwayOneEquiv`. -/
theorem sectionRingProjFiniteChartIso_hom (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjFiniteChartIso hF z).hom =
      (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionOne hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (sectionRingAwayOneEquiv hF z).symm.toRingHom) := by
  rfl

/-- The standard open `D₊(z X)` of `Proj` of the section ring of `(z)_∞` is the affine chart
at infinity of the two-chart model. -/
noncomputable def sectionRingProjInfinityChartIso (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z)).toScheme ≅
      Spec (.of (holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers})) :=
  Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _) (by simp) ≪≫
    Scheme.Spec.mapIso (sectionRingAwayGeneratorEquiv hF z).toRingEquiv.toCommRingCatIso.symm.op

/-- The chart isomorphism
`TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso` is Mathlib's isomorphism
`D₊(z X) ≅ Spec A₍z X₎` followed by the map induced by
`TauCeti.Divisor.sectionRingAwayGeneratorEquiv`. -/
theorem sectionRingProjInfinityChartIso_hom (hF : IsFunctionField k F) (z : Fˣ) :
    (sectionRingProjInfinityChartIso hF z).hom =
      (Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z)
          (monomialDegreeOne_mem_sectionRingGrade _) Nat.one_pos).hom ≫
        Spec.map (CommRingCat.ofHom (sectionRingAwayGeneratorEquiv hF z).symm.toRingHom) := by
  rfl

/-- The standard opens `D₊(X)` and `D₊(z X)` cover `Proj` of the section ring of `(z)_∞`. -/
theorem sectionRingProjChart_cover (hF : IsFunctionField k F) (z : Fˣ) :
    Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionOne hF z) ⊔
      Proj.basicOpen (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z) = ⊤ := by
  apply top_unique
  intro x _
  rw [TopologicalSpace.Opens.mem_sup, Proj.mem_basicOpen, Proj.mem_basicOpen]
  by_contra h
  push Not at h
  apply x.not_irrelevant_le
  refine (irrelevant_le_radical_span_monomialDegreeOne_poles hF z).trans ?_
  apply x.isPrime.radical_le_iff.mpr
  rw [Ideal.span_le]
  rintro y (rfl | rfl)
  · exact h.1
  · exact h.2

end AlgebraicGeometry.twoChartModel

end TauCeti
