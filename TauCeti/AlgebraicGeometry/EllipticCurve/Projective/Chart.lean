/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.CoordinateRing
public import TauCeti.RingTheory.GradedAlgebra.HomogeneousLocalization
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
projective model is checked.

## Main definitions

* `WeierstrassCurve.Projective.chartRelation W' i`: the two relations `W(X₀, X₁, X₂)` and
  `Xᵢ - 1`.
* `WeierstrassCurve.Projective.ChartRing W' i`: the quotient of `R[X₀, X₁, X₂]` by them.
* `WeierstrassCurve.Projective.awayEquivChartRing W' i`: the isomorphism `A_(Xᵢ) ≃+* ChartRing`.

## Main results

* `WeierstrassCurve.Projective.awayEquivChartRing_mk`: the isomorphism sends `a / Xᵢⁿ` to the
  class of `a`.
* `WeierstrassCurve.Projective.awayEquivChartRing_symm_comp_algebraMap`: the isomorphism is
  compatible with the structure maps from `R`.

## References

* [R. Hartshorne, *Algebraic Geometry*, II.2.5][hartshorne1977]
-/

public section

open MvPolynomial HomogeneousLocalization

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

/-- Dehomogenization: the quotient map from the homogeneous coordinate ring to the chart ring,
setting `Xᵢ = 1`. -/
private noncomputable def toChartRing : W'.CoordinateRing →ₐ[R] W'.ChartRing i :=
  Ideal.Quotient.factorₐ R (Ideal.span_mono (Set.singleton_subset_iff.mpr ⟨0, rfl⟩))

private theorem toChartRing_mk (p : MvPolynomial (Fin 3) R) :
    W'.toChartRing i (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ p := by
  rw [toChartRing, Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]

private theorem toChartRing_coord_self : W'.toChartRing i (W'.coord i) = 1 := by
  rw [toChartRing_mk, ← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span ⟨1, rfl⟩

/-- Dehomogenization on the chart: `a / Xᵢⁿ ↦ a(X₀, X₁, X₂)|_{Xᵢ = 1}`. -/
private noncomputable def awayToChartRing : Away W'.grading (W'.coord i) →+* W'.ChartRing i :=
  Away.lift W'.grading (W'.toChartRing i).toRingHom
    (by rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, toChartRing_coord_self]; exact isUnit_one)

private theorem awayToChartRing_mk {n : ℕ} {a : W'.CoordinateRing}
    (ha : a ∈ W'.grading (n • 1)) :
    W'.awayToChartRing i (Away.mk W'.grading (W'.coord_mem_grading i) n a ha) =
      W'.toChartRing i a := by
  rw [awayToChartRing, Away.lift_mk]
  generalize_proofs hu
  have hu1 : hu.unit = 1 := Units.ext (W'.toChartRing_coord_self i)
  rw [hu1, one_pow, inv_one, Units.val_one, mul_one, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- The structure map `R → A_(Xᵢ)`, through the degree-zero part of the coordinate ring. -/
private noncomputable def awayBase : R →+* Away W'.grading (W'.coord i) :=
  (fromZeroRingHom W'.grading _).comp (algebraMap R (W'.grading 0))

/-- The fraction `Xⱼ / Xᵢ` in `A_(Xᵢ)`. -/
private noncomputable def awayCoord (j : Fin 3) : Away W'.grading (W'.coord i) :=
  Away.mk W'.grading (W'.coord_mem_grading i) 1 (W'.coord j)
    (by simpa using W'.coord_mem_grading j)

private theorem awayCoord_self : W'.awayCoord i i = 1 := by
  apply val_injective
  rw [awayCoord, Away.val_mk, val_one, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
  simp

/-- Evaluating a homogeneous polynomial `p` of degree `n` at the fractions `Xⱼ / Xᵢ` gives the
fraction `p / Xᵢⁿ`. -/
private theorem eval₂_awayCoord {n : ℕ} {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    eval₂ (W'.awayBase i) (W'.awayCoord i) p =
      Away.mk W'.grading (W'.coord_mem_grading i) n (Ideal.Quotient.mk _ p)
        (by simpa using W'.mk_mem_grading hp) := by
  apply val_injective
  let L := Localization.Away (W'.coord i)
  -- the inverse of `Xᵢ` in the full localization
  let a : L := Localization.mk 1 ⟨W'.coord i, 1, pow_one _⟩
  have hcoord : (algebraMap (Away W'.grading (W'.coord i)) L) ∘ W'.awayCoord i =
      fun j ↦ a * ((algebraMap W'.CoordinateRing L) ∘ W'.coord) j := by
    ext j
    rw [Function.comp_apply, HomogeneousLocalization.algebraMap_apply, awayCoord, Away.val_mk,
      Function.comp_apply, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
    congr 1 <;> simp
  have hbase : (algebraMap (Away W'.grading (W'.coord i)) L).comp (W'.awayBase i) =
      (algebraMap W'.CoordinateRing L).comp (algebraMap R _) := by
    ext r
    rw [RingHom.comp_apply, awayBase, RingHom.comp_apply, ← HomogeneousLocalization.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply _ W'.CoordinateRing L]
    simp
  have hmk : eval₂ (algebraMap R W'.CoordinateRing) W'.coord p = Ideal.Quotient.mk _ p := by
    rw [← aeval_def, ← Ideal.Quotient.mkₐ_eq_mk R, aeval_unique (Ideal.Quotient.mkₐ R _)]
    -- `coord j` is by definition the class of `X j`
    rfl
  rw [← HomogeneousLocalization.algebraMap_apply, eval₂_comp_left, hbase, hcoord,
    hp.eval₂_const_mul, ← eval₂_comp_left, hmk, Away.val_mk, ← Localization.mk_one_eq_algebraMap,
    Localization.mk_pow, Localization.mk_mul]
  congr 1
  · simp
  · exact Subtype.ext (by simp)

/-- Homogenization: `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1) → A_(Xᵢ)`, `Xⱼ ↦ Xⱼ / Xᵢ`. -/
private noncomputable def chartRingToAway : W'.ChartRing i →+* Away W'.grading (W'.coord i) :=
  Ideal.Quotient.lift _ (eval₂Hom (W'.awayBase i) (W'.awayCoord i)) fun p hp ↦ by
    refine Submodule.span_induction ?_ (map_zero _) (fun x y _ _ hx hy ↦ ?_)
      (fun c x _ hx ↦ ?_) hp
    · rintro _ ⟨k, rfl⟩
      fin_cases k
      · -- `W / Xᵢ³` vanishes in `A_(Xᵢ)`
        refine (W'.eval₂_awayCoord i W'.isHomogeneous_polynomial).trans (val_injective _ ?_)
        simp [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _),
          Localization.mk_zero]
      · simp [awayCoord_self]
    · rw [map_add, hx, hy, add_zero]
    · rw [smul_eq_mul, map_mul, hx, mul_zero]

private theorem chartRingToAway_mk (p : MvPolynomial (Fin 3) R) :
    W'.chartRingToAway i (Ideal.Quotient.mk _ p) = eval₂ (W'.awayBase i) (W'.awayCoord i) p :=
  Ideal.Quotient.lift_mk _ _ _

private theorem awayToChartRing_comp_chartRingToAway :
    (W'.awayToChartRing i).comp (W'.chartRingToAway i) = RingHom.id _ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun r ↦ ?_) fun j ↦ ?_)
  · simp only [RingHom.comp_apply, RingHom.id_apply, chartRingToAway_mk, eval₂_C, awayBase,
      ← HomogeneousLocalization.algebraMap_eq, awayToChartRing, Away.lift_algebraMap]
    rw [SetLike.GradeZero.coe_algebraMap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      AlgHom.commutes, ← MvPolynomial.algebraMap_eq, Ideal.Quotient.mk_algebraMap]
  · simp [chartRingToAway_mk, awayCoord, awayToChartRing_mk, toChartRing_mk]

private theorem chartRingToAway_comp_awayToChartRing :
    (W'.chartRingToAway i).comp (W'.awayToChartRing i) = RingHom.id _ := by
  ext z
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective W'.grading (W'.coord_mem_grading i) z
  obtain ⟨p, hp, rfl⟩ := W'.mem_grading_iff.mp ha
  simp [awayToChartRing_mk, toChartRing_mk, chartRingToAway_mk, W'.eval₂_awayCoord i hp]

/-- The degree-zero part `A_(Xᵢ)` of the localization of the homogeneous coordinate ring away from
`Xᵢ` is the coordinate ring `R[X₀, X₁, X₂] ⧸ (W, Xᵢ - 1)` of the standard affine chart. -/
noncomputable def awayEquivChartRing : Away W'.grading (W'.coord i) ≃+* W'.ChartRing i :=
  RingEquiv.ofRingHom (W'.awayToChartRing i) (W'.chartRingToAway i)
    (W'.awayToChartRing_comp_chartRingToAway i) (W'.chartRingToAway_comp_awayToChartRing i)

/-- `awayEquivChartRing` sends `a / Xᵢⁿ` to the class of `a` with `Xᵢ` set to `1`. -/
@[simp]
theorem awayEquivChartRing_mk {n : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : Ideal.Quotient.mk _ p ∈ W'.grading (n • 1)) :
    W'.awayEquivChartRing i (Away.mk W'.grading (W'.coord_mem_grading i) n _ hp) =
      Ideal.Quotient.mk _ p :=
  (W'.awayToChartRing_mk i hp).trans (W'.toChartRing_mk i p)

/-- The inverse of `awayEquivChartRing` sends the class of `Xⱼ` to the fraction `Xⱼ / Xᵢ`. -/
@[simp]
theorem awayEquivChartRing_symm_mk_X (j : Fin 3) :
    (W'.awayEquivChartRing i).symm (Ideal.Quotient.mk _ (X j)) =
      Away.mk W'.grading (W'.coord_mem_grading i) 1 (W'.coord j)
        (by simpa using W'.coord_mem_grading j) :=
  (W'.chartRingToAway_mk i (X j)).trans (eval₂_X _ _ _)

/-- `awayEquivChartRing` is compatible with the structure maps from `R`: on the chart ring it is
the quotient map, on `A_(Xᵢ)` it factors through the degree-zero part of the coordinate ring. -/
theorem awayEquivChartRing_symm_comp_algebraMap :
    (W'.awayEquivChartRing i).symm.toRingHom.comp (algebraMap R (W'.ChartRing i)) =
      (fromZeroRingHom W'.grading _).comp (algebraMap R (W'.grading 0)) :=
  RingHom.ext fun r ↦ (W'.chartRingToAway_mk i (C r)).trans (eval₂_C _ _ _)

end WeierstrassCurve.Projective
