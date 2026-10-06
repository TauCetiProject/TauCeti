/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Chart.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.Nonsingular
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.ProjModel
public import TauCeti.RingTheory.Smooth.Jacobian

/-!
# Smoothness of the projective Weierstrass model

If the discriminant of a Weierstrass curve `W` over a commutative ring `R` is a unit, the
projective Weierstrass model `W.projModel` is smooth of relative dimension one over `Spec R`.

The proof is chart by chart. On the standard affine chart `Xᵢ ≠ 0`, presented as
`R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`, the Jacobian minor of the two relations with respect to the
variables `Xⱼ` and `Xᵢ` (for `j ≠ i`) is the partial derivative `∂W/∂Xⱼ`; inverting it gives a
standard smooth algebra of relative dimension `3 - 2 = 1`. The two partial derivatives `∂W/∂Xⱼ`,
`j ≠ i`, generate the unit ideal of the chart ring: at a point with residue field `k`, the image
of the point is a nonzero solution of the projective equation over `k`, hence nonsingular since
the discriminant is a unit in `k`, and Euler's relation `3W = Σ Xⱼ ∂W/∂Xⱼ` with `Xᵢ = 1` shows that
some `∂W/∂Xⱼ` with `j ≠ i` is nonzero there.

## Main results

* `WeierstrassCurve.Projective.isStandardSmoothOfRelativeDimension_localizationAway_pderiv`: the
  chart `Xᵢ ≠ 0` is standard smooth of relative dimension one where `∂W/∂Xⱼ` is invertible,
  `j ≠ i`; no ellipticity is needed.
* `WeierstrassCurve.Projective.span_range_mk_pderiv_eq_top`: for an elliptic curve, these partial
  derivatives generate the unit ideal of the chart.
* `WeierstrassCurve.smoothOfRelativeDimension_one_projModelOver`: the projective model of an
  elliptic Weierstrass curve is smooth of relative dimension one over the base.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, 2.2.
* P. Deligne and M. Rapoport, *Les schémas de modules de courbes elliptiques*, II.1.
* Stacks Project, Tag 00T7.
-/

public section

open CategoryTheory AlgebraicGeometry MvPolynomial

universe u

namespace WeierstrassCurve.Projective

variable {R : Type u} [CommRing R] (W' : Projective R) {i j : Fin 3}

/-- The presentation of the chart `Xᵢ ≠ 0` by the relations `W` and `Xᵢ - 1`, with the square
Jacobian minor taken with respect to `Xⱼ` and `Xᵢ`. -/
private noncomputable def chartPresentation (hji : j ≠ i) :
    Algebra.PreSubmersivePresentation R (W'.ChartRing i) (Fin 3) (Fin 2) :=
  .naive ![j, i] (Matrix.injective_pair_iff_ne.mpr hji)

/-- The Jacobian minor `det [[∂W/∂Xⱼ, ∂(Xᵢ - 1)/∂Xⱼ], [∂W/∂Xᵢ, ∂(Xᵢ - 1)/∂Xᵢ]]` is `∂W/∂Xⱼ`. -/
private theorem chartPresentation_jacobian (hji : j ≠ i) :
    (W'.chartPresentation hji).jacobian = Ideal.Quotient.mk _ (pderiv j W'.polynomial) := by
  rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_fin_two,
    chartPresentation]
  simp only [Algebra.PreSubmersivePresentation.jacobiMatrix_naive]
  simp only [chartRelation_zero, chartRelation_one, Matrix.cons_val_zero, Matrix.cons_val_one,
    map_sub, pderiv_X, pderiv_one, sub_zero, Pi.single_eq_same, Pi.single_eq_of_ne hji.symm,
    mul_one, zero_mul]
  -- the naive presentation maps polynomials to the chart ring by the quotient map
  rfl

/-- The standard affine chart `Xᵢ ≠ 0` of the projective Weierstrass cubic becomes standard smooth
of relative dimension one after inverting the partial derivative `∂W/∂Xⱼ`, for `j ≠ i`. -/
theorem isStandardSmoothOfRelativeDimension_localizationAway_pderiv (hji : j ≠ i) :
    Algebra.IsStandardSmoothOfRelativeDimension 1 R
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range (W'.chartRelation i)))
        (pderiv j W'.polynomial))) := by
  have : IsLocalization.Away (W'.chartPresentation hji).jacobian
      (Localization.Away (Ideal.Quotient.mk (Ideal.span (Set.range (W'.chartRelation i)))
        (pderiv j W'.polynomial))) := by
    rw [chartPresentation_jacobian]
    infer_instance
  simpa [Algebra.Presentation.dimension] using
    (W'.chartPresentation hji).isStandardSmoothOfRelativeDimension_localizationAway _

variable (i)

/-- On the standard affine chart `Xᵢ ≠ 0` of an elliptic Weierstrass cubic, the partial derivatives
`∂W/∂Xⱼ` with `j ≠ i` generate the unit ideal. -/
theorem span_range_mk_pderiv_eq_top [W'.IsElliptic] :
    Ideal.span (Set.range fun j : {j : Fin 3 // j ≠ i} ↦
      Ideal.Quotient.mk (Ideal.span (Set.range (W'.chartRelation i)))
        (pderiv j.1 W'.polynomial)) = ⊤ := by
  by_contra h
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
  have := hm.isPrime
  -- the point of the chart at `m`, with coordinates `P` in the residue field
  let π : MvPolynomial (Fin 3) R →+* m.ResidueField :=
    (algebraMap _ m.ResidueField).comp
      (Ideal.Quotient.mk (Ideal.span (Set.range (W'.chartRelation i))))
  let P : Fin 3 → m.ResidueField := fun k ↦ π (X k)
  have hπ (p : MvPolynomial (Fin 3) R) : π p = eval P (p.map (π.comp C)) := by
    conv_lhs => rw [← eval₂_eta p, eval₂_comp_left]
    rw [eval_map]
    rfl
  have hrel (k : Fin 2) : π (W'.chartRelation i k) = 0 := by
    have hk : W'.chartRelation i k ∈ Ideal.span (Set.range (W'.chartRelation i)) :=
      Ideal.subset_span ⟨k, rfl⟩
    simp [π, Ideal.Quotient.eq_zero_iff_mem.mpr hk]
  have hPi : P i = 1 := by
    have h1 := hrel 1
    rwa [chartRelation_one, map_sub, map_one, sub_eq_zero] at h1
  have hpd (j : Fin 3) (hj : j ≠ i) : π (pderiv j W'.polynomial) = 0 :=
    Ideal.algebraMap_residueField_eq_zero.mpr (hle (Ideal.subset_span ⟨⟨j, hj⟩, rfl⟩))
  -- the point lies on the base change of `W'` to the residue field, so it is nonsingular there
  let Wk : Projective m.ResidueField := W'.map (π.comp C)
  have heq : Wk.Equation P := by
    rw [Equation, map_polynomial, ← hπ]
    simpa using hrel 0
  obtain ⟨-, hns⟩ := (equation_iff_nonsingular_of_ne_zero (W := Wk)
    (fun h ↦ one_ne_zero (hPi.symm.trans (congrFun h i)))).mp heq
  have hX : eval P Wk.polynomialX = π (pderiv 0 W'.polynomial) := by
    rw [map_polynomialX, ← hπ, polynomialX]
  have hY : eval P Wk.polynomialY = π (pderiv 1 W'.polynomial) := by
    rw [map_polynomialY, ← hπ, polynomialY]
  have hZ : eval P Wk.polynomialZ = π (pderiv 2 W'.polynomial) := by
    rw [map_polynomialZ, ← hπ, polynomialZ]
  -- Euler's relation at the point, where `Xᵢ = 1`, forces `∂W/∂Xᵢ` to vanish as well
  have heuler := Wk.polynomial_relation P
  rw [heq, hX, hY, hZ] at heuler
  rw [hX, hY, hZ] at hns
  have hi : π (pderiv i W'.polynomial) = 0 := by
    fin_cases i
    all_goals
      simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] at hPi hpd ⊢
      simpa [hpd, hPi] using heuler.symm
  have hall (k : Fin 3) : π (pderiv k W'.polynomial) = 0 := by
    obtain rfl | hk := eq_or_ne k i
    exacts [hi, hpd k hk]
  rcases hns with h | h | h <;> exact h (hall _)

/-- The standard affine chart `Xᵢ ≠ 0` of an elliptic Weierstrass cubic is, locally on the chart,
standard smooth of relative dimension one over the base. -/
theorem locally_isStandardSmoothOfRelativeDimension_algebraMap [W'.IsElliptic] :
    RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension 1)
      (algebraMap R (W'.ChartRing i)) := by
  refine RingHom.locally_of_exists RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ _
    (W'.span_range_mk_pderiv_eq_top i)
    (fun j ↦ Localization.Away (Ideal.Quotient.mk
      (Ideal.span (Set.range (W'.chartRelation i))) (pderiv j.1 W'.polynomial))) fun j ↦ ?_
  rw [← IsScalarTower.algebraMap_eq, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact W'.isStandardSmoothOfRelativeDimension_localizationAway_pderiv j.2

end WeierstrassCurve.Projective

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The chart `Spec A_(Xᵢ) ⟶ projModel W` followed by the structure morphism is smooth of relative
dimension one: it is `Spec` of the structure map of the chart ring, up to the isomorphism
`awayEquivChartRing`. -/
private theorem smoothOfRelativeDimension_awayι_projModelOver [W.IsElliptic] (i : Fin 3) :
    SmoothOfRelativeDimension 1
      (Proj.awayι _ _ (W.toProjective.coord_mem_grading i) one_pos ≫ W.projModelOver) := by
  rw [awayι_projModelOver, HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1),
    CommRingCat.hom_ofHom, ← Projective.awayEquivChartRing_symm_comp_algebraMap]
  exact (RingHom.locally_respectsIso RingHom.isStandardSmoothOfRelativeDimension_respectsIso).left
    _ _ (W.toProjective.locally_isStandardSmoothOfRelativeDimension_algebraMap i)

/-- If the discriminant is a unit, the projective Weierstrass model is smooth of relative
dimension one over the base. -/
instance smoothOfRelativeDimension_one_projModelOver [W.IsElliptic] :
    SmoothOfRelativeDimension 1 W.projModelOver := by
  -- the standard charts `D₊(Xᵢ)` form an affine open cover of `projModel W`
  let 𝒰 := (Proj.affineOpenCoverOfIrrelevantLESpan W.toProjective.grading W.toProjective.coord
    W.toProjective.coord_mem_grading (fun _ ↦ one_pos)
    W.toProjective.irrelevant_le_span_range_coord).openCover
  have (i : 𝒰.I₀) : IsAffine (𝒰.X i) := inferInstanceAs (IsAffine (Spec _))
  exact HasRingHomProperty.of_source_openCover (P := @SmoothOfRelativeDimension 1) 𝒰
    fun i ↦ (HasRingHomProperty.iff_of_isAffine (P := @SmoothOfRelativeDimension 1)).mp
      (W.smoothOfRelativeDimension_awayι_projModelOver i)

end WeierstrassCurve
