/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.LaurentExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Affine
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Chart
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.FormalPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval

/-!
# The tautological point of the projective Weierstrass model

Let `W` be a Weierstrass curve over a commutative ring `R`. This file defines the
**tautological point** `[x : y : 1]` of the projective Weierstrass model `projModel W`, with values
in the affine coordinate ring `R[W] = R[x, y] ⧸ (W(x, y))` (`WeierstrassCurve.tautologicalPoint`).
The chart `D₊(Z)` of the projective model factors through it, and through the Laurent expansion
`R[W] → R⸨z⸩` at the point at infinity (`WeierstrassCurve.laurentExpansion`) it becomes the formal
point `[z : -1 : w(z)]` along the zero section, with values in the power series ring `R⟦z⟧`.

## Main definitions

* `WeierstrassCurve.tautologicalPoint W`: the point `[x : y : 1]` of `projModel W` with values in
  the affine coordinate ring `R[W]`.

## Main results

* `WeierstrassCurve.tautologicalPoint_eq_SpecMap_chartι`: the tautological point is the chart
  `D₊(Z)` after the canonical affine coordinate-ring comparison.
* `WeierstrassCurve.opensRange_tautologicalPoint`: its image is exactly `D₊(Z)`.
* `WeierstrassCurve.SpecMap_laurentExpansion_tautologicalPoint`: expanded at the point at
  infinity, the tautological point is the formal point.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1.
-/

public section

open CategoryTheory AlgebraicGeometry PowerSeries LaurentSeries

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] {W : WeierstrassCurve R}

/-- The coordinate functions `(x, y, 1)` over the affine coordinate ring `R[W]` solve the
homogeneous Weierstrass equation of `W`. -/
theorem equation_tautologicalPoint :
    (W.toProjective.map (algebraMap R W.toAffine.CoordinateRing)).Equation
      ![AdjoinRoot.of W.toAffine.polynomial Polynomial.X, AdjoinRoot.root W.toAffine.polynomial,
        1] :=
  (Projective.equation_some _ _).mpr (Affine.CoordinateRing.equation_X_root W.toAffine)

variable (W)

/-- The **tautological point** `[x : y : 1]` of the projective Weierstrass model, with values in
the affine coordinate ring `R[W] = R[x, y] ⧸ (W(x, y))`. Rewrite with `tautologicalPoint_def`
rather than unfolding this definition. -/
noncomputable def tautologicalPoint : Spec (.of W.toAffine.CoordinateRing) ⟶ W.projModel :=
  W.projModelPoint (algebraMap R _) equation_tautologicalPoint (i := 2) (by simp)

/-- The tautological point is the point of the projective model with homogeneous coordinates
`(x, y, 1)`, along `algebraMap R R[W]`. -/
theorem tautologicalPoint_def : W.tautologicalPoint =
    W.projModelPoint (algebraMap R _) equation_tautologicalPoint (i := 2) (by simp) := (rfl)

/-- The tautological point lies over the morphism `Spec R[W] ⟶ Spec R` induced by
`algebraMap R R[W]`. -/
@[reassoc (attr := simp)]
theorem tautologicalPoint_projModelOver : W.tautologicalPoint ≫ W.projModelOver =
    Spec.map (CommRingCat.ofHom (algebraMap R W.toAffine.CoordinateRing)) := by
  rw [tautologicalPoint_def, projModelPoint_projModelOver]

/-- The canonical inverse coordinate-ring comparison sends the tautological point to the
universal point of the third projective chart. -/
theorem SpecMap_chartRingTwoEquivCoordinateRing_symm_tautologicalPoint :
    Spec.map W.toProjective.chartRingTwoEquivCoordinateRing.toRingEquiv.toCommRingCatIso.inv ≫
        W.tautologicalPoint =
      W.chartι 2 := by
  rw [RingEquiv.toCommRingCatIso_inv, tautologicalPoint_def, SpecMap_projModelPoint,
    chartι_eq_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨RingHom.ext W.toProjective.chartRingTwoEquivCoordinateRing.symm.commutes,
    1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp [Projective.chartRingTwoEquivCoordinateRing_symm_of_X,
    Projective.chartRingTwoEquivCoordinateRing_symm_root]

/-- The tautological point is the standard affine chart `D₊(Z)` transported along the canonical
comparison of the chart ring with the affine Weierstrass coordinate ring. -/
theorem tautologicalPoint_eq_SpecMap_chartι : W.tautologicalPoint =
    Spec.map W.toProjective.chartRingTwoEquivCoordinateRing.toRingEquiv.toCommRingCatIso.hom ≫
      W.chartι 2 := by
  apply (cancel_epi (Spec.map
    W.toProjective.chartRingTwoEquivCoordinateRing.toRingEquiv.toCommRingCatIso.inv)).mp
  rw [SpecMap_chartRingTwoEquivCoordinateRing_symm_tautologicalPoint,
    ← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]

/-- The tautological point identifies the affine Weierstrass scheme with an open subscheme of
the projective model. -/
instance isOpenImmersion_tautologicalPoint : IsOpenImmersion W.tautologicalPoint := by
  rw [W.tautologicalPoint_eq_SpecMap_chartι]
  infer_instance

/-- The image of the tautological point is the standard affine open `D₊(Z)`. -/
@[simp]
theorem opensRange_tautologicalPoint : W.tautologicalPoint.opensRange =
    Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) := by
  simpa only [← W.tautologicalPoint_eq_SpecMap_chartι] using
    (Scheme.Hom.opensRange_comp_of_isIso
      (Spec.map W.toProjective.chartRingTwoEquivCoordinateRing.toRingEquiv.toCommRingCatIso.hom)
      (W.chartι 2)).trans (W.opensRange_chartι 2)

/-- **The tautological point at infinity.** Expanded in Laurent series at the point at infinity,
the tautological point `[x : y : 1]` is the formal point `[z : -1 : w(z)]`: its coordinates are
`-y` times those of the formal point. -/
theorem SpecMap_laurentExpansion_tautologicalPoint :
    Spec.map (CommRingCat.ofHom (W.laurentExpansion : W.toAffine.CoordinateRing →+* R⸨X⸩)) ≫
        W.tautologicalPoint =
      Spec.map (CommRingCat.ofHom (HahnSeries.ofPowerSeries ℤ R)) ≫ W.projModelFormalPoint := by
  have hy := W.laurentExpansion_root_mul_formalW
  have hx := W.laurentExpansion_of_X_eq_neg_X_mul_laurentExpansion_root
  rw [tautologicalPoint_def, projModelFormalPoint_def, SpecMap_projModelPoint,
    SpecMap_projModelPoint, projModelPoint_eq_projModelPoint_iff]
  refine ⟨(W.laurentExpansion.comp_algebraMap).trans rfl,
    (IsUnit.of_mul_eq_one (HahnSeries.ofPowerSeries ℤ R (formalW W))
      (by rw [neg_mul, hy, neg_neg])).unit, funext fun k ↦ ?_⟩
  fin_cases k
  · simp [-laurentExpansion_of_X, -laurentExpansion_root, Units.smul_def, hx]
    ring
  · simp [Units.smul_def]
  · simp [-laurentExpansion_root, Units.smul_def, hy]

end WeierstrassCurve
