/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Basic
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

## Main definitions

* `TauCeti.Divisor.sectionRingAwayOneEquiv`: the localization at `X` is the finite-chart ring.
* `TauCeti.Divisor.sectionRingAwayGeneratorEquiv`: the localization at `z X` is the
  infinity-chart ring.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjFiniteChartIso`: the resulting
  isomorphism from the standard open `D₊(X)` to the finite chart.
* `TauCeti.AlgebraicGeometry.twoChartModel.sectionRingProjInfinityChartIso`: the resulting
  isomorphism from the standard open `D₊(z X)` to the infinity chart.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.2.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section III.2 and Appendix B.
-/

public section

open Polynomial HomogeneousLocalization

namespace TauCeti

open _root_.AlgebraicGeometry

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F]

namespace Divisor

/-- The degree-one section `X` in the section ring of the pole divisor of `z`. -/
noncomputable abbrev polesSectionOne (hF : IsFunctionField k F) (z : Fˣ) :
    sectionRing (poles hF z) :=
  monomialDegreeOne (one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le)

/-- The degree-one section `z X` in the section ring of the pole divisor of `z`. -/
noncomputable abbrev polesSectionGenerator (hF : IsFunctionField k F) (z : Fˣ) :
    sectionRing (poles hF z) :=
  monomialDegreeOne (mem_riemannRochSpace_poles hF z)

/-- Localizing the section ring of `(z)_∞` at `X` gives the holomorphy ring of the places at
which `z` is regular. -/
noncomputable def sectionRingAwayOneEquiv (hF : IsFunctionField k F) (z : Fˣ) :
    Away (sectionRingGrade (poles hF z)) (polesSectionOne hF z) ≃ₐ[k]
      holomorphyRing {P : Place k F | (z : F) ∈ P.integers} := by
  let hOne : (1 : F) ∈ riemannRochSpace (poles hF z) :=
    one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le
  let e := sectionRingAwayEquiv hF (monomialDegreeOne_mem_sectionRingGrade hOne)
    (by
      intro h
      apply_fun fun s : sectionRing (poles hF z) ↦ (s : F[X]) at h
      simp [coe_monomialDegreeOne] at h)
  refine e.trans (Subalgebra.equivOfEq _ _ ?_)
  congr 1
  ext P
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, coe_monomialDegreeOne,
    Polynomial.coeff_monomial_same]
  rw [Nat.cast_one, one_mul, map_one, ← WithZero.exp_zero, WithZero.exp_inj, eq_comm]
  exact coeff_poles_eq_zero_iff hF z P

/-- Under `TauCeti.Divisor.sectionRingAwayOneEquiv`, the fraction `g Xʳ / Xʳ` is sent to
the degree-`r` coefficient of `g`. -/
@[simp]
theorem sectionRingAwayOneEquiv_mk (hF : IsFunctionField k F) (z : Fˣ) (r : ℕ)
    (g : sectionRing (poles hF z)) (hg : g ∈ sectionRingGrade (poles hF z) r) :
    (sectionRingAwayOneEquiv hF z
      (Away.mk _ (monomialDegreeOne_mem_sectionRingGrade
        (one_mem_riemannRochSpace_iff.mpr (isEffective_poles hF z).zero_le)) r g
        (by simpa using hg)) : F) =
      (g : F[X]).coeff r := by
  simp [sectionRingAwayOneEquiv, sectionRingAwayEquiv_mk]

/-- Localizing the section ring of `(z)_∞` at `z X` gives the holomorphy ring of the places at
which `z⁻¹` is regular. -/
noncomputable def sectionRingAwayGeneratorEquiv (hF : IsFunctionField k F) (z : Fˣ) :
    Away (sectionRingGrade (poles hF z)) (polesSectionGenerator hF z) ≃ₐ[k]
      holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers} := by
  let hz : (z : F) ∈ riemannRochSpace (poles hF z) := mem_riemannRochSpace_poles hF z
  let e := sectionRingAwayEquiv hF (monomialDegreeOne_mem_sectionRingGrade hz)
    (by
      intro h
      apply_fun fun s : sectionRing (poles hF z) ↦ (s : F[X]) at h
      simp [coe_monomialDegreeOne] at h)
  refine e.trans (Subalgebra.equivOfEq _ _ ?_)
  congr 1
  ext P
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, coe_monomialDegreeOne,
    Polynomial.coeff_monomial_same]
  simpa only [Nat.cast_one, one_mul] using valuation_eq_exp_coeff_poles_iff hF z P

/-- Under `TauCeti.Divisor.sectionRingAwayGeneratorEquiv`, the fraction
`g Xʳ / (z X)ʳ` is sent to `g / zʳ`. -/
@[simp]
theorem sectionRingAwayGeneratorEquiv_mk (hF : IsFunctionField k F) (z : Fˣ) (r : ℕ)
    (g : sectionRing (poles hF z)) (hg : g ∈ sectionRingGrade (poles hF z) r) :
    (sectionRingAwayGeneratorEquiv hF z
      (Away.mk _ (monomialDegreeOne_mem_sectionRingGrade
        (mem_riemannRochSpace_poles hF z)) r g (by simpa using hg)) : F) =
      (g : F[X]).coeff r * ((z : F) ^ r)⁻¹ := by
  simp [sectionRingAwayGeneratorEquiv, sectionRingAwayEquiv_mk]

end Divisor

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

/-- The standard open `D₊(z X)` of `Proj` of the section ring of `(z)_∞` is the affine chart
at infinity of the two-chart model. -/
noncomputable def sectionRingProjInfinityChartIso (hF : IsFunctionField k F) (z : Fˣ) :
    (Proj.basicOpen (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z)).toScheme ≅
      Spec (.of (holomorphyRing {P : Place k F | (z : F)⁻¹ ∈ P.integers})) :=
  Proj.basicOpenIsoSpec (sectionRingGrade (poles hF z))
      (polesSectionGenerator hF z) (monomialDegreeOne_mem_sectionRingGrade _) (by simp) ≪≫
    Scheme.Spec.mapIso (sectionRingAwayGeneratorEquiv hF z).toRingEquiv.toCommRingCatIso.symm.op

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
