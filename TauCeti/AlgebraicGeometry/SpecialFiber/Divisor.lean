/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.SpecialFiber.Components
public import TauCeti.AlgebraicGeometry.WeilDivisor.FiniteSum

/-!
# The divisor of a special fibre

For an integral Noetherian scheme over a one-dimensional local ring, whose generic point maps
away from the closed point, the divisor of the pullback of a nonzero element of the maximal
ideal is a positive sum of the codimension-one components of the special fibre. Its coefficient
at a component is the order of vanishing of the pulled-back element there. For a DVR
uniformizer, these coefficients are the component multiplicities of the scheme-theoretic
special fibre.

The support and positivity facts come from `SpecialFiber.Components`; the sum uses the existing
finite-sum API for Weil divisors. Associated elements and generators of the same principal ideal
define the same multiplicities (`specialFiberMultiplicity_congr_of_associated`,
`specialFiberMultiplicity_eq_of_span_eq`). This is the divisor calculation in the
[Stacks Project, Section 55.9](https://stacks.math.columbia.edu/tag/0C5Y).
-/

public section

noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing TauCeti.AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Hom

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [Ring.DimensionLEOne R]
variable {X : Scheme.{u}} (toBase : X ⟶ Spec (.of R)) [IsIntegral X] [IsNoetherian X]

/-- The nonnegative order of vanishing of the pullback of `π` at a codimension-one point. When
the generic point maps away from the closed point and `π` is nonzero in the maximal ideal, this
is the multiplicity of a special-fibre component, and it is zero away from the special fibre. -/
noncomputable def specialFiberMultiplicity
    (π : R) (x : CodimensionOnePoint X) : ℕ :=
  (X.ord (X.germToFunctionField ⊤
    (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π))) x).toNat

omit [IsLocalRing R] [Ring.DimensionLEOne R] in
/-- The integer coercion of the special-fibre multiplicity is the order of vanishing of the
pulled-back section. -/
theorem specialFiberMultiplicity_coe
    (π : R) (x : CodimensionOnePoint X) :
    (toBase.specialFiberMultiplicity π x : ℤ) = X.ord
      (X.germToFunctionField ⊤
        (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π))) x := by
  rw [Scheme.Hom.specialFiberMultiplicity]
  exact Int.toNat_of_nonneg (Scheme.ord_germToFunctionField_nonneg _ trivial)

omit [IsLocalRing R] [Ring.DimensionLEOne R] in
/-- Two generators of the same principal ideal of `R` define the same special-fibre
multiplicities. -/
theorem specialFiberMultiplicity_eq_of_span_eq {π π' : R}
    (hspan : Ideal.span {π} = Ideal.span {π'}) (x : CodimensionOnePoint X) :
    toBase.specialFiberMultiplicity π x = toBase.specialFiberMultiplicity π' x := by
  let φ : R →+* Γ(X, ⊤) := toBase.appTop.hom.comp (Scheme.ΓSpecIso (.of R)).inv.hom
  have hφ (r : R) : toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv r) = φ r := rfl
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  have hφ_span : Ideal.span {φ π} = Ideal.span {φ π'} := by
    simpa only [Ideal.map_span, Set.image_singleton] using congrArg (Ideal.map φ) hspan
  obtain ⟨u, hu⟩ := Ideal.span_singleton_eq_span_singleton.mp hφ_span
  apply Nat.cast_injective (R := ℤ)
  rw [toBase.specialFiberMultiplicity_coe, toBase.specialFiberMultiplicity_coe, hφ, hφ]
  rcases eq_or_ne (φ π) 0 with hπ0 | hπ0
  · rw [← hu, hπ0, zero_mul]
  · rw [← hu, map_mul,
      X.ord_mul ((map_ne_zero_iff _ (X.germToFunctionField_injective ⊤)).mpr hπ0)
        (u.isUnit.map (X.germToFunctionField ⊤).hom).ne_zero,
      X.ord_of_isUnit u.isUnit trivial, add_zero]

omit [IsLocalRing R] [Ring.DimensionLEOne R] in
/-- Associated elements of the base ring define the same special-fibre multiplicities: multiplying
`π` by a unit leaves the generated principal ideal unchanged. -/
theorem specialFiberMultiplicity_congr_of_associated {π π' : R} (h : Associated π π')
    (x : CodimensionOnePoint X) :
    toBase.specialFiberMultiplicity π x = toBase.specialFiberMultiplicity π' x := by
  obtain ⟨u, rfl⟩ := h
  exact toBase.specialFiberMultiplicity_eq_of_span_eq
    (Ideal.span_singleton_mul_right_unit u.isUnit π).symm x

/-- At a codimension-one point of the special fibre, the pullback of a nonzero element of the
maximal ideal has positive multiplicity. -/
theorem specialFiberMultiplicity_pos
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) (x : CodimensionOnePoint X)
    (hx : toBase x = closedPoint R) : 0 < toBase.specialFiberMultiplicity π x := by
  rw [Scheme.Hom.specialFiberMultiplicity]
  have := (toBase.ord_germToFunctionField_appTop_pos_iff hη hπ hπ0 x.property).mpr hx
  omega

/-- The multiplicity is zero away from the special fibre. -/
theorem specialFiberMultiplicity_eq_zero_of_ne
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : ¬ IsUnit π) (hπ0 : π ≠ 0) (x : CodimensionOnePoint X)
    (hx : toBase x ≠ closedPoint R) : toBase.specialFiberMultiplicity π x = 0 := by
  rw [Scheme.Hom.specialFiberMultiplicity]
  have hπ' : π ∈ maximalIdeal R := by simpa using hπ
  have hnonneg := Scheme.ord_germToFunctionField_nonneg
    (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π)) (x := x) trivial
  have hnotpos := (toBase.ord_germToFunctionField_appTop_pos_iff hη hπ' hπ0 x.property).not.mpr hx
  exact Int.toNat_eq_zero.mpr (by omega)

/-- The divisor of the pullback of `π` is the sum of its component multiplicities over the
finite set of codimension-one points of the special fibre. -/
theorem principalDivisor_eq_sum_specialFiber
    (hη : toBase (genericPoint X) ≠ closedPoint R) {π : R}
    (hπ : π ∈ maximalIdeal R) (hπ0 : π ≠ 0) :
    (WeilDivisor.OrderSystem.ofScheme X).principalDivisor
      (Additive.ofMul (Units.mk0 _ (toBase.germToFunctionField_appTop_ne_zero hη hπ hπ0))) =
      ∑ x ∈ (toBase.finite_setOf_base_eq_closedPoint
        (by intro h; rw [h] at hπ; exact hπ0 (by simpa using hπ)) hη).toFinset,
        (toBase.specialFiberMultiplicity π x : ℤ) • WeilDivisor.ofPoint x := by
  classical
  have hR : maximalIdeal R ≠ ⊥ := by
    intro h
    rw [h] at hπ
    exact hπ0 (by simpa using hπ)
  let D : WeilDivisor (CodimensionOnePoint X) :=
    (WeilDivisor.OrderSystem.ofScheme X).principalDivisor
      (Additive.ofMul (Units.mk0 _ (toBase.germToFunctionField_appTop_ne_zero hη hπ hπ0)))
  have hsupport : D.support = (toBase.finite_setOf_base_eq_closedPoint hR hη).toFinset := by
    ext x
    simpa [D] using toBase.mem_support_principalDivisor_appTop hη hπ hπ0 x
  have heq : D = ∑ x ∈ (toBase.finite_setOf_base_eq_closedPoint hR hη).toFinset,
      (toBase.specialFiberMultiplicity π x : ℤ) • WeilDivisor.ofPoint x := by
    rw [WeilDivisor.eq_sum_coeff_smul_ofPoint D, hsupport]
    refine Finset.sum_congr rfl fun x _ ↦ ?_
    have hord : WeilDivisor.coeff D x = X.ord
        (X.germToFunctionField ⊤
          (toBase.appTop ((Scheme.ΓSpecIso (.of R)).inv π))) x := by
      simp [D, WeilDivisor.OrderSystem.coeff_principalDivisor,
        WeilDivisor.OrderSystem.ofScheme_ord]
    rw [Scheme.Hom.specialFiberMultiplicity_coe, hord]
  exact heq

end AlgebraicGeometry.Scheme.Hom
