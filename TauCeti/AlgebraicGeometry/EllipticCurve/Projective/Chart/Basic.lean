/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization.Basic
public import TauCeti.RingTheory.MvPolynomial.Homogeneous

/-!
# The standard affine charts of the projective Weierstrass cubic

For a Weierstrass curve `W'` over `R` and a homogeneous coordinate `Xᵢ`, the standard affine chart
`D₊(Xᵢ)` of the projective cubic is the spectrum of the degree-zero part `A_(Xᵢ)` of the
localization of the homogeneous coordinate ring `A = R[X₀, X₁, X₂] ⧸ (W(X₀, X₁, X₂))` away from
`Xᵢ`. This file identifies `A_(Xᵢ)` with the dehomogenized ring

`R[X₀, X₁, X₂] ⧸ (W(X₀, X₁, X₂), Xᵢ - 1)`,

the fraction `a / Xᵢⁿ` corresponding to the class of `a` with `Xᵢ` set to `1`. Keeping all three
variables and adding the relation `Xᵢ - 1` treats the three charts uniformly, and presents each
chart by three generators and two relations; this is the form in which the smoothness of the
projective model is checked. The isomorphism is the chart isomorphism
`HomogeneousIdeal.awayEquivDehomogenize` of a general quotient by a homogeneous ideal, onto
`R[Y₀, Y₁] ⧸ (W|_{Xᵢ = 1})`, followed by the identification of that ring with the chart ring.

## Main definitions

* `WeierstrassCurve.Projective.chartRelation W' i`: the two relations `W(X₀, X₁, X₂)` and
  `Xᵢ - 1`.
* `WeierstrassCurve.Projective.ChartRing W' i`: the quotient of `R[X₀, X₁, X₂]` by them.
* `WeierstrassCurve.Projective.awayEquivChartRing W' i`: the isomorphism `A_(Xᵢ) ≃+* ChartRing`.
* `WeierstrassCurve.Projective.chartPoint W' i`: the universal point of the chart, whose
  coordinates are the classes of `X₀, X₁, X₂` in `ChartRing W' i`.
* `WeierstrassCurve.Projective.awayEvalHom W' g hP hi`: the homomorphism `A_(Xᵢ) →+* S`,
  `a / Xᵢⁿ ↦ a(P) / Pᵢⁿ`, at a solution `P` of the equation of `W'.map g` with `Pᵢ` a unit.

## Main results

* `WeierstrassCurve.Projective.awayEquivChartRing_mk`: the isomorphism sends `a / Xᵢⁿ` to the
  class of `a`.
* `WeierstrassCurve.Projective.awayEquivChartRing_symm_comp_algebraMap`: the isomorphism is
  compatible with the structure maps from `R`.
* `WeierstrassCurve.Projective.equation_chartPoint`: the universal point of the chart is a solution
  of the Weierstrass equation over `ChartRing W' i`.

## References

* [R. Hartshorne, *Algebraic Geometry*, II.2.5][hartshorne1977]

## Provenance

`chartPoint` and `equation_chartPoint` are adapted from AINTLIB
(`github.com/CBirkbeck/AINTLIB`, Apache-2.0) at commit `c3415f32a313e19ace43e05479aeaa0d56ca287a`,
file `projects/ModularCurves/ModularCurves/EllipticCurve/AdditionChartRing.lean`
(`affineChartPoint` and `equation_affineChartPoint`), stated for TauCeti's `ChartRing`.
-/

public section

open MvPolynomial HomogeneousLocalization

attribute [local instance] MvPolynomial.gradedAlgebra

namespace WeierstrassCurve.Projective

variable {R : Type*} [CommRing R] (W' : Projective R) (i : Fin 3)

/-- The two relations `W(X₀, X₁, X₂)` and `Xᵢ - 1` cutting out the standard affine chart
`Xᵢ ≠ 0` of the projective Weierstrass cubic, as a closed subscheme of affine `3`-space. -/
noncomputable def chartRelation : Fin 2 → MvPolynomial (Fin 3) R :=
  ![W'.polynomial, X i - 1]

@[simp]
theorem chartRelation_zero : W'.chartRelation i 0 = W'.polynomial :=
  (rfl)

@[simp]
theorem chartRelation_one : W'.chartRelation i 1 = X i - 1 :=
  (rfl)

/-- The coordinate ring `R[X₀, X₁, X₂] ⧸ (W(X₀, X₁, X₂), Xᵢ - 1)` of the standard affine chart
`Xᵢ ≠ 0` of the projective Weierstrass cubic. -/
abbrev ChartRing : Type _ :=
  MvPolynomial (Fin 3) R ⧸ Ideal.span (Set.range (W'.chartRelation i))

/-- In the chart ring `ChartRing W' i`, the class of the coordinate `Xᵢ` is `1`. -/
@[simp]
theorem chartRing_mk_X_self : (Ideal.Quotient.mk _ (X i) : W'.ChartRing i) = 1 :=
  (Ideal.Quotient.mk_eq_one_iff_sub_mem _).mpr (Ideal.subset_span ⟨1, by simp⟩)

/-- Evaluation at the classes of the remaining coordinates: `R[Y₀, Y₁] → ChartRing W' i`,
`Yⱼ ↦ X_{i.succAbove j}`. -/
private noncomputable def aevalChartRing : MvPolynomial (Fin 2) R →ₐ[R] W'.ChartRing i :=
  aeval fun j ↦ Ideal.Quotient.mk _ (X (i.succAbove j))

/-- Evaluating the dehomogenization of `p` at the classes of the remaining coordinates gives the
class of `p`, since the class of `Xᵢ` is `1`. -/
private theorem aevalChartRing_dehomogenize (p : MvPolynomial (Fin 3) R) :
    W'.aevalChartRing i (TauCeti.dehomogenize i p) = Ideal.Quotient.mk _ p := by
  have h : i.insertNth 1 (fun j ↦ Ideal.Quotient.mk _ (X (i.succAbove j))) =
      fun k ↦ (Ideal.Quotient.mk _ (X k) : W'.ChartRing i) :=
    Fin.insertNth_eq_iff.mpr ⟨(W'.chartRing_mk_X_self i).symm, rfl⟩
  rw [aevalChartRing, TauCeti.aeval_dehomogenize, h]
  -- `Ideal.Quotient.mkₐ` is determined by the classes of the variables
  exact (DFunLike.congr_fun (aeval_unique (Ideal.Quotient.mkₐ R _)) p).symm

/-- The dehomogenized ring `R[Y₀, Y₁] ⧸ (W|_{Xᵢ = 1})` maps to the chart ring by
`Yⱼ ↦ X_{i.succAbove j}`. -/
private noncomputable def dehomogenizeToChartRing :
    (MvPolynomial (Fin 2) R ⧸ W'.homogeneousIdeal.toIdeal.map (TauCeti.dehomogenize i)) →ₐ[R]
      W'.ChartRing i :=
  Ideal.Quotient.liftₐ _ (W'.aevalChartRing i) fun p hp ↦ by
    refine RingHom.mem_ker.mp (Ideal.map_le_iff_le_comap.mpr (fun q hq ↦ ?_) hp)
    rw [Ideal.mem_comap, RingHom.mem_ker, aevalChartRing_dehomogenize,
      Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨0, rfl⟩ :
      {W'.polynomial} ⊆ Set.range (W'.chartRelation i)) hq

private theorem dehomogenizeToChartRing_mk (p : MvPolynomial (Fin 2) R) :
    W'.dehomogenizeToChartRing i (Ideal.Quotient.mk _ p) = W'.aevalChartRing i p :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- Setting `Xᵢ = 1`: the chart ring maps to the dehomogenized ring `R[Y₀, Y₁] ⧸ (W|_{Xᵢ = 1})`. -/
private noncomputable def chartRingToDehomogenize :
    W'.ChartRing i →ₐ[R]
      MvPolynomial (Fin 2) R ⧸ W'.homogeneousIdeal.toIdeal.map (TauCeti.dehomogenize i) :=
  Ideal.Quotient.liftₐ _ ((Ideal.Quotient.mkₐ R _).comp (TauCeti.dehomogenize i)) fun p hp ↦ by
    refine RingHom.mem_ker.mp (Ideal.span_le.mpr ?_ hp)
    rintro _ ⟨k, rfl⟩
    fin_cases k
    · -- `W|_{Xᵢ = 1}` generates the ideal of the dehomogenized ring
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _))
    · simp

private theorem chartRingToDehomogenize_mk (p : MvPolynomial (Fin 3) R) :
    W'.chartRingToDehomogenize i (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk _ (TauCeti.dehomogenize i p) :=
  Ideal.Quotient.liftₐ_apply _ _ _ _

/-- Setting `Xᵢ = 1` identifies the dehomogenized ring `R[Y₀, Y₁] ⧸ (W|_{Xᵢ = 1})` with the chart
ring `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)`. -/
private noncomputable def dehomogenizeEquivChartRing :
    (MvPolynomial (Fin 2) R ⧸ W'.homogeneousIdeal.toIdeal.map (TauCeti.dehomogenize i)) ≃ₐ[R]
      W'.ChartRing i :=
  AlgEquiv.ofAlgHom (W'.dehomogenizeToChartRing i) (W'.chartRingToDehomogenize i)
    (Ideal.Quotient.algHom_ext R <| AlgHom.ext fun p ↦ by
      simp only [AlgHom.comp_apply, AlgHom.id_comp, Ideal.Quotient.mkₐ_eq_mk,
        chartRingToDehomogenize_mk, dehomogenizeToChartRing_mk, aevalChartRing_dehomogenize])
    (Ideal.Quotient.algHom_ext R <| MvPolynomial.algHom_ext fun j ↦ by
      simp only [AlgHom.comp_apply, AlgHom.id_comp, Ideal.Quotient.mkₐ_eq_mk,
        dehomogenizeToChartRing_mk, aevalChartRing, aeval_X, chartRingToDehomogenize_mk,
        TauCeti.dehomogenize_X, Fin.insertNth_apply_succAbove])

private theorem dehomogenizeEquivChartRing_mk_dehomogenize (p : MvPolynomial (Fin 3) R) :
    W'.dehomogenizeEquivChartRing i (Ideal.Quotient.mk _ (TauCeti.dehomogenize i p)) =
      Ideal.Quotient.mk _ p :=
  (W'.dehomogenizeToChartRing_mk i _).trans (W'.aevalChartRing_dehomogenize i p)

/-- The degree-zero part `A_(Xᵢ)` of the localization of the homogeneous coordinate ring away from
`Xᵢ` is the coordinate ring `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)` of the standard affine chart: the chart
isomorphism `HomogeneousIdeal.awayEquivDehomogenize` of the general quotient, followed by setting
`Xᵢ = 1`. -/
noncomputable def awayEquivChartRing : Away W'.grading (W'.coord i) ≃+* W'.ChartRing i :=
  ((W'.homogeneousIdeal.awayEquivDehomogenize i).trans
    (W'.dehomogenizeEquivChartRing i)).toRingEquiv

/-- `awayEquivChartRing` sends `a / Xᵢⁿ` to the class of `a` with `Xᵢ` set to `1`. -/
@[simp]
theorem awayEquivChartRing_mk {n : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : Ideal.Quotient.mk _ p ∈ W'.grading (n • 1)) :
    W'.awayEquivChartRing i (Away.mk W'.grading (W'.coord_mem_grading i) n _ hp) =
      Ideal.Quotient.mk _ p :=
  (congrArg (W'.dehomogenizeEquivChartRing i)
    (W'.homogeneousIdeal.awayEquivDehomogenize_mk i hp)).trans
      (W'.dehomogenizeEquivChartRing_mk_dehomogenize i p)

/-- The inverse of `awayEquivChartRing` sends the class of `Xⱼ` to the fraction `Xⱼ / Xᵢ`. -/
@[simp]
theorem awayEquivChartRing_symm_mk_X (j : Fin 3) :
    (W'.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X j)) =
      Away.mk W'.grading (W'.coord_mem_grading i) 1 (W'.coord j)
        (by simpa using W'.coord_mem_grading j) :=
  (RingEquiv.symm_apply_eq _).mpr (W'.awayEquivChartRing_mk i _).symm

/-- `awayEquivChartRing` is compatible with the structure maps from `R`: on the chart ring it is
the quotient map, on `A_(Xᵢ)` it factors through the degree-zero part of the coordinate ring. -/
theorem awayEquivChartRing_symm_comp_algebraMap :
    (W'.awayEquivChartRing i).symm.toRingHom.comp (algebraMap R (W'.ChartRing i)) =
      (fromZeroRingHom W'.grading _).comp (algebraMap R (W'.grading 0)) :=
  RingHom.ext ((W'.homogeneousIdeal.awayEquivDehomogenize i).trans
    (W'.dehomogenizeEquivChartRing i)).symm.commutes

/-- The universal point of the standard affine chart `D₊(Xᵢ)` of the projective Weierstrass cubic:
the classes of the three homogeneous coordinates in `ChartRing W' i`. -/
noncomputable def chartPoint : Fin 3 → W'.ChartRing i :=
  fun k ↦ Ideal.Quotient.mk _ (X k)

/-- The coordinates of the universal point of the chart `D₊(Xᵢ)` are the classes of `X₀, X₁, X₂`. -/
@[simp]
theorem chartPoint_apply (k : Fin 3) : W'.chartPoint i k = Ideal.Quotient.mk _ (X k) :=
  (rfl)

/-- The `i`-th coordinate of the universal point of the chart `D₊(Xᵢ)` is `1`. -/
theorem chartPoint_self : W'.chartPoint i i = 1 :=
  W'.chartRing_mk_X_self i

/-- The universal point of the chart `D₊(Xᵢ)` is a solution of the Weierstrass equation over
`ChartRing W' i`. -/
theorem equation_chartPoint : (W'.baseChange (W'.ChartRing i)).Equation (W'.chartPoint i) := by
  -- by definition, `W'.baseChange B` is `W'.map (algebraMap R B)` and `chartPoint i` is `mkₐ ∘ X`
  change (W'.map _).Equation (Ideal.Quotient.mkₐ R _ ∘ X)
  -- evaluation at the classes of the variables is the quotient map, which kills `W'.polynomial`
  rw [Equation, map_polynomial, eval_map, ← aeval_def, ← aeval_unique, Ideal.Quotient.mkₐ_eq_mk,
    ← chartRelation_zero W' i, Ideal.Quotient.mk_span_range]

section AwayEval

variable {S : Type*} [CommRing S] (g : R →+* S) {P : Fin 3 → S} (hP : (W'.map g).Equation P) {i}

/-- The ring homomorphism `A_(Xᵢ) →+* S`, `a / Xᵢⁿ ↦ a(P) / Pᵢⁿ` (`awayEvalHom_mk`), on the
degree-zero part `A_(Xᵢ)` of the localization of the homogeneous coordinate ring away from `Xᵢ`, at
a solution `P` of the projective Weierstrass equation of `W'.map g` whose coordinate `Pᵢ` is a unit.
It restricts to `g` on `R` (`awayEvalHom_comp_algebraMap`). -/
noncomputable def awayEvalHom (hi : IsUnit (P i)) : Away W'.grading (W'.coord i) →+* S :=
  Away.lift _ (W'.evalHom g hP) <| by rwa [evalHom_mk, eval₂_X]

/-- `awayEvalHom` is the homomorphism `HomogeneousLocalization.Away.lift` induced by the evaluation
`evalHom` of the homogeneous coordinate ring at `P`. -/
theorem awayEvalHom_def (hi : IsUnit (P i)) :
    W'.awayEvalHom g hP hi = Away.lift _ (W'.evalHom g hP) (by rwa [evalHom_mk, eval₂_X]) :=
  (rfl)

/-- `awayEvalHom` sends the fraction `a / Xᵢⁿ` to `a(P) / Pᵢⁿ`. -/
@[simp]
theorem awayEvalHom_mk (hi : IsUnit (P i)) (n : ℕ) (a : W'.CoordinateRing)
    (ha : a ∈ W'.grading (n • 1)) :
    W'.awayEvalHom g hP hi (Away.mk W'.grading (W'.coord_mem_grading i) n a ha) =
      W'.evalHom g hP a * ↑(hi.unit ^ n)⁻¹ := by
  simp [awayEvalHom]

/-- `awayEvalHom` restricts to `g` on the base ring `R`, which maps to `A_(Xᵢ)` through the
degree-zero part of the homogeneous coordinate ring. -/
theorem awayEvalHom_comp_algebraMap (hi : IsUnit (P i)) :
    (W'.awayEvalHom g hP hi).comp ((fromZeroRingHom _ _).comp (algebraMap R (W'.grading 0))) = g :=
  RingHom.ext fun r ↦ (Away.lift_algebraMap _ _ _).trans <|
    RingHom.congr_fun (W'.evalHom_comp_algebraMap g hP) r

end AwayEval

end WeierstrassCurve.Projective
