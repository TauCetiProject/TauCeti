/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.CoordinateRing.LaurentExpansion
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

* `WeierstrassCurve.exists_SpecMap_comp_tautologicalPoint_eq_chartι`: the chart `D₊(Z)` factors
  through the tautological point.
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

/-- The chart `D₊(Z)` of the projective model factors through the tautological point: the
universal point of the chart is `[X / Z : Y / Z : 1]`, the image of `[x : y : 1]` under an
`R`-algebra map `R[W] → ChartRing 2`. -/
theorem exists_SpecMap_comp_tautologicalPoint_eq_chartι :
    ∃ k : W.toAffine.CoordinateRing →ₐ[R] W.toProjective.ChartRing 2,
      Spec.map (CommRingCat.ofHom k.toRingHom) ≫ W.tautologicalPoint = W.chartι 2 := by
  -- the universal point of the chart is `(X / Z, Y / Z, 1)`
  have hP : W.toProjective.chartPoint 2 = ![W.toProjective.chartPoint 2 0,
      W.toProjective.chartPoint 2 1, 1] := funext fun k ↦ by
    fin_cases k <;> simp
  have hE := W.toProjective.equation_chartPoint 2
  rw [hP] at hE
  refine ⟨Affine.CoordinateRing.evalAlgHom ((Projective.equation_some _ _).mp hE), ?_⟩
  rw [tautologicalPoint_def, SpecMap_projModelPoint, chartι_eq_projModelPoint,
    projModelPoint_eq_projModelPoint_iff]
  refine ⟨RingHom.ext (Affine.CoordinateRing.evalAlgHom _).commutes, 1, funext fun k ↦ ?_⟩
  fin_cases k <;> simp

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
