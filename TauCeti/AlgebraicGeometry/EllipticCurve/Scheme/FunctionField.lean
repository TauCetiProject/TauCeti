/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.AlgebraicGeometry.FunctionField
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GenericPoint.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Integral
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Points
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Eval
import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic

/-!
# The function field of the projective Weierstrass model

For a Weierstrass curve `W` over an integral domain `R`, the projective Weierstrass model
`W.projModel` is an integral scheme. This file identifies its function field with the function
field `W.toAffine.FunctionField` of the affine Weierstrass equation, the fraction field of the
affine coordinate ring `R[x, y] ⧸ (W(x, y))`. No ellipticity hypothesis is needed.

## Main definitions

* `WeierstrassCurve.projModelFunctionFieldEquiv`: the isomorphism
  `W.projModel.functionField ≃+* W.toAffine.FunctionField`.

## Main results

* `WeierstrassCurve.nonempty_basicOpen_coord_two`: over a nontrivial ring, the standard affine
  chart `D₊(Z)` of the projective model is nonempty.
* `WeierstrassCurve.projModelFunctionFieldEquiv_germToFunctionField_awayToSection_mk`: the
  isomorphism sends the rational function `p(X, Y, Z) / Zⁿ` on the chart `D₊(Z)` to `p(x, y, 1)`.
* `WeierstrassCurve.SpecMap_projModelFunctionFieldEquiv_fromSpecStalk`: through the isomorphism,
  the generic point `Spec K(E) ⟶ E` of the projective model is the point with homogeneous
  coordinates `[x : y : 1]`, where `x` and `y` are the affine coordinates in
  `W.toAffine.FunctionField`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], I.1 and I.2.

## Provenance

Adapted from AINTLIB (`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit
`c3415f32a313e19ace43e05479aeaa0d56ca287a`, file
`projects/ModularCurves/ModularCurves/EllipticCurve/MulByHomDegree.lean`, declaration
`ModularCurves.EllipticCurve.projModelFunctionFieldEquiv`, which treats elliptic curves over a
field and takes its `Z`-chart identification `coordRingToZSection` from `ModelVariableChange.lean`
in the same directory; here the base is any integral domain, no ellipticity is assumed, and the
chart identification is built on `WeierstrassCurve.Projective.awayEquivChartRing`.
-/

public section

open CategoryTheory AlgebraicGeometry HomogeneousLocalization MvPolynomial

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

private theorem aeval_toProjective_polynomial_eq_zero :
    aeval ![Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X),
      Affine.CoordinateRing.mk W.toAffine Polynomial.X, 1] W.toProjective.polynomial = 0 := by
  -- `x` and `y`, the classes of the affine coordinates, solve the affine Weierstrass equation of
  -- `W` base changed to the coordinate ring, so `(x, y, 1)` solves its homogeneous equation
  rw [aeval_def, ← eval_map, ← Projective.map_polynomial]
  exact (Projective.equation_some _ _).mpr (Affine.CoordinateRing.equation_of_algHom (.id R _))

private noncomputable def chartRingToCoordinateRing :
    W.toProjective.ChartRing 2 →ₐ[R] W.toAffine.CoordinateRing :=
  -- dehomogenization on the chart `D₊(Z)`: the map from the chart ring
  -- `R[X, Y, Z] ⧸ (W(X, Y, Z), Z - 1)` to the affine coordinate ring sending `X, Y, Z` to `x, y, 1`
  Ideal.Quotient.liftₐ _ (aeval ![Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X),
      Affine.CoordinateRing.mk W.toAffine Polynomial.X, 1]) fun _ hp ↦
    RingHom.mem_ker.mp <| Ideal.span_le.mpr (Set.range_subset_iff.mpr <| Fin.forall_fin_two.mpr
      ⟨by rw [Projective.chartRelation_zero]; exact W.aeval_toProjective_polynomial_eq_zero,
        by simp⟩) hp

private theorem chartRingToCoordinateRing_mk (p : MvPolynomial (Fin 3) R) :
    W.chartRingToCoordinateRing (Ideal.Quotient.mk _ p) =
      aeval ![Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X),
        Affine.CoordinateRing.mk W.toAffine Polynomial.X, 1] p :=
  rfl

private noncomputable def coordinateRingToChartRing :
    W.toAffine.CoordinateRing →ₐ[R] W.toProjective.ChartRing 2 :=
  -- homogenization on the chart `D₊(Z)`: the map from the affine coordinate ring to the chart
  -- ring sending `x` and `y` to the classes of `X` and `Y`
  Affine.CoordinateRing.evalAlgHom <|
    (Projective.equation_some (Ideal.Quotient.mk _ (X 0)) (Ideal.Quotient.mk _ (X 1))).mp <| by
      -- the homogeneous Weierstrass equation, with `Z = 1`
      rw [Projective.Equation, Affine.baseChange, WeierstrassCurve.baseChange,
        Projective.map_polynomial, eval_map, ← aeval_def, ← W.toProjective.chartRing_mk_X_self 2,
        ← Projective.chartRelation_zero _ 2, ← Ideal.Quotient.mk_span_range _ 0]
      -- evaluation at the classes of `X`, `Y`, `Z` is the quotient map
      exact DFunLike.congr_fun (algHom_ext fun i ↦ by fin_cases i <;> simp :
        aeval _ = Ideal.Quotient.mkₐ R _) _

private noncomputable def awayEquivCoordinateRing :
    Away W.toProjective.grading (W.toProjective.coord 2) ≃+* W.toAffine.CoordinateRing :=
  -- the degree-zero part `A_(Z)` is the chart ring `R[X, Y, Z] ⧸ (W(X, Y, Z), Z - 1)` of `D₊(Z)`,
  -- which is the affine coordinate ring
  (W.toProjective.awayEquivChartRing 2).trans <|
    AlgEquiv.ofAlgHom W.chartRingToCoordinateRing W.coordinateRingToChartRing
      (by ext <;> simp [coordinateRingToChartRing, chartRingToCoordinateRing_mk])
      (Ideal.Quotient.algHom_ext R <| algHom_ext fun j ↦ by
        fin_cases j <;> simp [chartRingToCoordinateRing_mk, coordinateRingToChartRing])

private noncomputable def chartSectionsEquivCoordinateRing :
    Γ(W.projModel, Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)) ≃+*
      W.toAffine.CoordinateRing :=
  -- the sections of the projective model over the chart `D₊(Z)` are the degree-zero part `A_(Z)`
  (Proj.basicOpenIsoAway _ _ (W.toProjective.coord_mem_grading 2) one_pos).commRingCatIsoToRingEquiv
    |>.symm.trans W.awayEquivCoordinateRing

private theorem chartSectionsEquivCoordinateRing_awayToSection
    (z : Away W.toProjective.grading (W.toProjective.coord 2)) :
    W.chartSectionsEquivCoordinateRing (Proj.awayToSection _ _ z) = W.awayEquivCoordinateRing z :=
  -- `Proj.awayToSection` is the forward map of `Proj.basicOpenIsoAway`, whose inverse cancels it
  congrArg W.awayEquivCoordinateRing ((Proj.basicOpenIsoAway _ _
    (W.toProjective.coord_mem_grading 2) one_pos).commRingCatIsoToRingEquiv.symm_apply_apply z)

/-- Over a nontrivial ring, the standard affine chart `D₊(Z)` of the projective Weierstrass model
is nonempty. -/
instance nonempty_basicOpen_coord_two [Nontrivial R] :
    Nonempty (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)) :=
  -- the chart is the spectrum of `A_(Z)`, which is the nonzero affine coordinate ring
  .map (Proj.basicOpenIsoSpec _ _ (W.toProjective.coord_mem_grading 2) one_pos).inv.base <|
    PrimeSpectrum.nonempty_iff_nontrivial.mpr W.awayEquivCoordinateRing.toEquiv.nontrivial

private instance [IsDomain R] :
    IsFractionRing Γ(W.projModel, Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2))
      W.projModel.functionField :=
  -- the function field of the projective model is the fraction field of the sections over the
  -- affine chart `D₊(Z)`, a nonempty affine open of the integral scheme `W.projModel`
  functionField_isFractionRing_of_isAffineOpen _ _ <|
    Proj.isAffineOpen_basicOpen _ _ (W.toProjective.coord_mem_grading 2) one_pos

/-- Over an integral domain, the isomorphism between the function field of the projective
Weierstrass model and the function field `W.toAffine.FunctionField` of the affine Weierstrass
equation. On the chart `D₊(Z)` it sends `p(X, Y, Z) / Zⁿ` to `p(x, y, 1)`, where `x` and `y` are
the affine coordinates (`projModelFunctionFieldEquiv_germToFunctionField_awayToSection_mk`). -/
noncomputable def projModelFunctionFieldEquiv [IsDomain R] :
    W.projModel.functionField ≃+* W.toAffine.FunctionField :=
  -- the sections over the affine chart `D₊(Z)` form the degree-zero part `A_(Z)`, which is the
  -- chart ring `R[X, Y, Z] ⧸ (W, Z - 1)` and, setting `Z = 1`, the affine coordinate ring; the
  -- function field of an integral scheme is the fraction field of the sections over any nonempty
  -- affine open, so both sides are fraction fields of the same ring
  IsFractionRing.ringEquivOfRingEquiv W.chartSectionsEquivCoordinateRing

/-- On the standard affine chart `D₊(Z)`, `projModelFunctionFieldEquiv` sends the rational
function `p(X, Y, Z) / Zⁿ`, for `p` whose class in the homogeneous coordinate ring has degree `n`,
to `p(x, y, 1)`, where `x` and `y` are the classes of the affine coordinates in
`W.toAffine.CoordinateRing`. -/
@[simp]
theorem projModelFunctionFieldEquiv_germToFunctionField_awayToSection_mk [IsDomain R] {n : ℕ}
    {p : MvPolynomial (Fin 3) R} (hp : Ideal.Quotient.mk _ p ∈ W.toProjective.grading (n • 1)) :
    -- the section is not indexed: the type arguments of its coercion mention
    -- `↑(CommRingCat.of (Away _ _))`, which `simp` reduces to `Away _ _` before rewriting
    W.projModelFunctionFieldEquiv (W.projModel.germToFunctionField _ (no_index
      (Proj.awayToSection _ _ (Away.mk _ (W.toProjective.coord_mem_grading 2) n _ hp)))) =
    algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
      (aeval ![Affine.CoordinateRing.mk W.toAffine (Polynomial.C Polynomial.X),
        Affine.CoordinateRing.mk W.toAffine Polynomial.X, 1] p) :=
  -- the germ map is the algebra map of the fraction field structure
  (IsFractionRing.ringEquivOfRingEquiv_algebraMap _ _).trans <| congrArg _ <|
    (W.chartSectionsEquivCoordinateRing_awayToSection _).trans <| congrArg _ <|
      W.toProjective.awayEquivChartRing_mk 2 hp

-- The inclusion `Spec Γ(E, D₊(Z)) ⟶ E` of the affine chart `D₊(Z)` is `Spec` of the identification
-- `A_(Z) ≅ Γ(E, D₊(Z))` followed by the chart `Spec A_(Z) ⟶ E`.
private theorem fromSpec_basicOpen_coord_two
    (hU : IsAffineOpen (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2))) :
    hU.fromSpec = Spec.map (Proj.awayToSection _ _) ≫ Proj.awayι W.toProjective.grading
      (W.toProjective.coord 2) (W.toProjective.coord_mem_grading 2) one_pos := by
  have : IsIso (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)).toSpecΓ := by
    rw [← hU.isoSpec_hom]
    infer_instance
  -- both sides precomposed with the isomorphism `D₊(Z) ⟶ Spec Γ(E, D₊(Z))` are the inclusion
  rw [← cancel_epi (Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2)).toSpecΓ,
    hU.toSpecΓ_fromSpec,
    ← Proj.basicOpenIsoSpec_inv_ι _ _ (W.toProjective.coord_mem_grading 2) one_pos,
    ← Category.assoc, ← Category.assoc, ← Proj.basicOpenToSpec,
    ← Proj.basicOpenIsoSpec_hom _ _ (W.toProjective.coord_mem_grading 2) one_pos, Iso.hom_inv_id,
    Category.id_comp]

/-- **The generic point of the projective Weierstrass model.** Over an integral domain `R`, the
canonical morphism `Spec K(E) ⟶ E` from the spectrum of the function field of `E = projModel W`,
read through `projModelFunctionFieldEquiv` as a morphism out of `Spec` of the function field of
the affine equation, is the point with homogeneous coordinates `[x : y : 1]`, where `x` and `y` are
the affine coordinates `genericX` and `genericY`. -/
theorem SpecMap_projModelFunctionFieldEquiv_fromSpecStalk [IsDomain R] :
    Spec.map (CommRingCat.ofHom (W.projModelFunctionFieldEquiv : W.projModel.functionField →+*
        W.toAffine.FunctionField)) ≫ W.projModel.fromSpecStalk (genericPoint W.projModel) =
      W.projModelPoint (algebraMap R W.toAffine.FunctionField)
        (P := ![Affine.genericX W.toAffine, Affine.genericY W.toAffine, 1])
        ((Projective.equation_some _ _).mpr (Affine.equation_genericX_genericY W.toAffine)) (i := 2)
        (by simpa only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] using
          isUnit_one) := by
  have hU := Proj.isAffineOpen_basicOpen W.toProjective.grading _
    (W.toProjective.coord_mem_grading 2) one_pos
  have hη : genericPoint W.projModel ∈
      Proj.basicOpen W.toProjective.grading (W.toProjective.coord 2) :=
    ((genericPoint_spec W.projModel).mem_open_set_iff (Proj.basicOpen _ _).isOpen).mpr
      (by simpa using W.nonempty_basicOpen_coord_two)
  have hι : Proj.awayι W.toProjective.grading (W.toProjective.coord 2)
      (W.toProjective.coord_mem_grading 2) one_pos =
        Spec.map (CommRingCat.ofHom ((W.toProjective.awayEquivChartRing 2).symm : _ →+* _)) ≫
          W.chartι 2 := by
    rw [chartι_def, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
    simp
  -- the generic point lies on the chart `D₊(Z)`, so the morphism is `Spec` of a homomorphism out of
  -- the chart ring followed by the chart, which is the point whose homogeneous coordinates are the
  -- images of the classes of `X`, `Y` and `Z`
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hη, IsAffineOpen.fromSpecStalk,
    fromSpec_basicOpen_coord_two, hι, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, SpecMap_chartι]
  refine projModelPoint_eq_projModelPoint_iff.mpr ⟨?_, 1, ?_⟩
  · -- on constants, read as fractions `r / Z⁰`
    ext r
    have hp : Ideal.Quotient.mk _ (C r) ∈ W.toProjective.grading (0 • 1) :=
      W.toProjective.mem_grading_iff.mpr ⟨C r, by simpa using isHomogeneous_C _ r, rfl⟩
    have hr : (W.toProjective.awayEquivChartRing 2).symm (algebraMap R _ r) =
        Away.mk _ (W.toProjective.coord_mem_grading 2) 0 _ hp := by
      rw [RingEquiv.symm_apply_eq, Projective.awayEquivChartRing_mk]
      rfl
    simp [hr, ← IsScalarTower.algebraMap_apply]
  · -- on the fractions `X / Z`, `Y / Z` and `Z / Z`
    ext k
    fin_cases k <;> simp [Affine.genericX_def, Affine.genericY_def, Affine.CoordinateRing.mk]

end WeierstrassCurve
