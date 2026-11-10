/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Proper
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.PicZero
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.RiemannRoch.Finiteness
public import TauCeti.FieldTheory.FunctionField.Divisor.Equiv

/-!
# Weil divisors, the Picard group, and `Pic⁰` of the two-chart model

Let `F / k` be an algebraic function field over an arbitrary field `k`, and let
`X_F = TauCeti.AlgebraicGeometry.twoChartModel hF hx` be its regular proper curve over `k` built
from an element `x ∈ F` transcendental over `k`. Because the codimension-one points of `X_F` are in
canonical bijection with the normalized places of `F / k` (`twoChartModel.equivPlace`), reindexing
identifies scheme-theoretic Weil divisors on `X_F` with function-field divisors on `F`.

This file establishes the complete divisor- and class-group dictionary between `X_F` and `F / k`,
with no assumption on the constant field `k`:

* `twoChartModel.equivDivisor`: the order-preserving additive equivalence
  `SchemeWeilDivisor X_F ≃+ Divisor k F`, compatible with coefficients, prime divisors, and
  effectivity;
* `twoChartModel.degree_equivDivisor` and `twoChartModel.relativeDegree_equivDivisor_symm`: the
  residue-degree-weighted degree on `X_F` agrees with the place-degree-weighted degree on `F`;
* `twoChartModel.equivDivisor_principal`, `twoChartModel.equivDivisor_symm_principal`, and
  `twoChartModel.linearlyEquivalent_equivDivisor_iff`: principal divisors on `X_F` correspond to
  principal divisors of `F` under `k(X_F) ≃ₐ[k] F`, so linear equivalence is preserved;
* `twoChartModel.classGroupEquiv` and `twoChartModel.picardEquivClassGroup`: the induced
  isomorphisms `Cl(X_F) ≃+ Cl(F)` and `Pic(X_F) ≃+ Cl(F)`, intertwining the Euler-characteristic
  degree on `Pic(X_F)` with `Divisor.degreeClass`
  (`twoChartModel.degreeClass_picardEquivClassGroup`);
* `twoChartModel.picZeroEquivDegreeZeroClassGroup`: the restricted isomorphism
  `Pic⁰(X_F) ≃+ Cl⁰(F)` between the degree-zero Picard group of `X_F` and the degree-zero divisor
  class group of `F`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Section II.6 and Section IV.1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.4 and Appendix B.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry Order

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-! ### Reindexing Weil divisors along `equivPlace` -/

/-- **Weil divisors on the two-chart model are divisors of `F / k`**: reindexing along
`twoChartModel.equivPlace` identifies `SchemeWeilDivisor (twoChartModel hF hx)` with
`Divisor k F`. -/
noncomputable def equivDivisor (hxt : Transcendental k x) :
    SchemeWeilDivisor (twoChartModel hF hx) ≃+ Divisor k F :=
  Finsupp.domCongr (equivPlace hxt)

/-- `equivDivisor` is reindexing along `equivPlace`. -/
theorem equivDivisor_eq_domCongr (hxt : Transcendental k x) :
    equivDivisor (hF := hF) (hx := hx) hxt = Finsupp.domCongr (equivPlace hxt) :=
  (rfl)

/-- `equivDivisor` factors as `SchemeWeilDivisor.equivFunctionFieldDivisor` followed by divisor
transport along `functionFieldEquiv`. -/
theorem equivDivisor_eq_trans (hxt : Transcendental k x) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    equivDivisor hxt =
      (SchemeWeilDivisor.equivFunctionFieldDivisor (valuativeCriterion_existence hF hx)
        (coheight_le_one hxt)).trans
        (Finsupp.domCongr (Place.mapEquiv (functionFieldEquiv hxt))) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  have heq : equivPlace (hF := hF) (hx := hx) hxt =
      (CodimensionOnePoint.equivPlace (k := k) (valuativeCriterion_existence hF hx)
        (coheight_le_one hxt)).trans (Place.mapEquiv (functionFieldEquiv hxt)) :=
    Equiv.ext fun p ↦ by
      rw [equivPlace_apply, Equiv.trans_apply, CodimensionOnePoint.equivPlace_apply,
        Place.mapEquiv_apply]
  rw [equivDivisor_eq_domCongr, heq, ← Finsupp.domCongr_trans,
    ← SchemeWeilDivisor.equivFunctionFieldDivisor_eq_domCongr]

/-- Transporting `SchemeWeilDivisor.equivFunctionFieldDivisor` along `functionFieldEquiv` gives
`equivDivisor`. -/
theorem domCongr_equivOfRingEquiv_equivFunctionFieldDivisor (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    Finsupp.domCongr
        (Place.equivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
          (id (functionFieldEquiv hxt).commutes))
        (SchemeWeilDivisor.equivFunctionFieldDivisor (valuativeCriterion_existence hF hx)
          (coheight_le_one hxt) D) =
      equivDivisor hxt D := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  rw [equivDivisor_eq_trans hxt, AddEquiv.trans_apply, Place.mapEquiv_eq_equivOfRingEquiv]

/-- The coefficient of `equivDivisor hxt D` at a place `P` is the coefficient of `D` at the
corresponding codimension-one point of `X_F`. -/
@[simp]
theorem coeff_equivDivisor (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) (P : Place k F) :
    WeilDivisor.coeff (equivDivisor hxt D) P = WeilDivisor.coeff D ((equivPlace hxt).symm P) := by
  simp only [equivDivisor, Finsupp.domCongr_apply, WeilDivisor.coeff, Finsupp.equivMapDomain_apply]

/-- The coefficient of `equivDivisor hxt D` at the place of `p` is the coefficient of `D` at `p`.

Not `@[simp]`: `coeff_equivDivisor` already simplifies the left-hand side. -/
theorem coeff_equivDivisor_equivPlace (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx))
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    WeilDivisor.coeff (equivDivisor hxt D) (equivPlace hxt p) = WeilDivisor.coeff D p := by
  rw [coeff_equivDivisor, Equiv.symm_apply_apply]

/-- Pulling a divisor of `F` back to `X_F` reads its coefficient at `p` at `equivPlace hxt p`. -/
@[simp]
theorem coeff_equivDivisor_symm (hxt : Transcendental k x) (D : Divisor k F)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    WeilDivisor.coeff ((equivDivisor hxt).symm D) p =
      WeilDivisor.coeff D (equivPlace hxt p) := by
  simp only [equivDivisor, Finsupp.domCongr_symm, Finsupp.domCongr_apply, WeilDivisor.coeff,
    Finsupp.equivMapDomain_apply, Equiv.symm_symm]

/-- `equivDivisor` sends the prime divisor of a codimension-one point to the prime divisor of its
place. -/
@[simp]
theorem equivDivisor_ofPoint (hxt : Transcendental k x)
    (p : CodimensionOnePoint (twoChartModel hF hx)) :
    equivDivisor hxt (WeilDivisor.ofPoint p) = WeilDivisor.ofPoint (equivPlace hxt p) :=
  WeilDivisor.domCongr_ofPoint (equivPlace hxt) p

/-- Pulling back a prime divisor of `F` gives the prime divisor at the corresponding point of
`X_F`. -/
@[simp]
theorem equivDivisor_symm_ofPoint (hxt : Transcendental k x) (P : Place k F) :
    (equivDivisor (hF := hF) (hx := hx) hxt).symm (WeilDivisor.ofPoint P) =
      WeilDivisor.ofPoint ((equivPlace (hF := hF) (hx := hx) hxt).symm P) := by
  apply (equivDivisor (hF := hF) (hx := hx) hxt).injective
  rw [AddEquiv.apply_symm_apply, equivDivisor_ofPoint, Equiv.apply_symm_apply]

/-- `equivDivisor` preserves coefficientwise inequalities. -/
@[simp]
theorem equivDivisor_le_iff (hxt : Transcendental k x)
    {D E : SchemeWeilDivisor (twoChartModel hF hx)} :
    equivDivisor hxt D ≤ equivDivisor hxt E ↔ D ≤ E := by
  simpa only [equivDivisor, Finsupp.domCongr_apply, Finsupp.equivMapDomain_eq_mapDomain] using
    Finsupp.mapDomain_le_mapDomain_iff_le (equivPlace hxt).injective D E

/-- `(equivDivisor hxt).symm` preserves coefficientwise inequalities. -/
@[simp]
theorem equivDivisor_symm_le_iff (hxt : Transcendental k x) {D E : Divisor k F} :
    (equivDivisor (hF := hF) (hx := hx) hxt).symm D ≤
        (equivDivisor (hF := hF) (hx := hx) hxt).symm E ↔
      D ≤ E := by
  rw [← equivDivisor_le_iff (hF := hF) (hx := hx) hxt, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-- `equivDivisor` preserves effective divisors. -/
@[simp]
theorem equivDivisor_nonneg_iff (hxt : Transcendental k x)
    {D : SchemeWeilDivisor (twoChartModel hF hx)} :
    0 ≤ equivDivisor hxt D ↔ 0 ≤ D := by
  rw [← map_zero (equivDivisor hxt), equivDivisor_le_iff]

/-- `(equivDivisor hxt).symm` preserves effective divisors. -/
@[simp]
theorem equivDivisor_symm_nonneg_iff (hxt : Transcendental k x) {D : Divisor k F} :
    0 ≤ (equivDivisor (hF := hF) (hx := hx) hxt).symm D ↔ 0 ≤ D := by
  rw [← equivDivisor_nonneg_iff (hF := hF) (hx := hx) hxt, AddEquiv.apply_symm_apply]

/-! ### Degrees, principal divisors, and linear equivalence -/

/-- **Degree comparison**: the function-field degree of `equivDivisor hxt D` equals the
residue-degree-weighted degree of `D` on `X_F`. -/
@[simp]
theorem degree_equivDivisor (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    Divisor.degree (equivDivisor hxt D) =
      SchemeWeilDivisor.relativeDegree (twoChartModel hF hx ↘ Spec (.of k)) D := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  rw [← domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt D,
    Divisor.degree_domCongr_equivOfRingEquiv, SchemeWeilDivisor.degree_equivFunctionFieldDivisor]

/-- The scheme-theoretic degree of `(equivDivisor hxt).symm D` equals the function-field degree of
`D`. -/
@[simp]
theorem relativeDegree_equivDivisor_symm (hxt : Transcendental k x) (D : Divisor k F) :
    SchemeWeilDivisor.relativeDegree (twoChartModel hF hx ↘ Spec (.of k))
        ((equivDivisor hxt).symm D) =
      Divisor.degree D := by
  rw [← degree_equivDivisor hxt, AddEquiv.apply_symm_apply]

/-- **Principal divisors on `X_F` become principal divisors of `F`** under `equivDivisor` and
`functionFieldEquiv`. -/
@[simp]
theorem equivDivisor_principal (hxt : Transcendental k x)
    (z : (twoChartModel hF hx).functionFieldˣ) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    equivDivisor hxt ((WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).principalDivisor
        (Additive.ofMul z)) =
      Divisor.principal hF
        (Units.map (functionFieldEquiv hxt).toRingEquiv.toMulEquiv.toMonoidHom z) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  rw [← domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt,
    SchemeWeilDivisor.equivFunctionFieldDivisor_principal (valuativeCriterion_existence hF hx)
      (coheight_le_one hxt) (isFunctionField_functionField hxt),
    Divisor.domCongr_equivOfRingEquiv_principal (RingEquiv.refl k)
      (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes)
      (isFunctionField_functionField hxt) hF]
  exact congrArg _ (Units.ext (by simp))

/-- Pulling back the principal divisor of `z ∈ Fˣ` gives the scheme-theoretic principal divisor of
its preimage in `k(X_F)ˣ`. -/
@[simp]
theorem equivDivisor_symm_principal (hxt : Transcendental k x) (z : Fˣ) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (equivDivisor (hF := hF) (hx := hx) hxt).symm (Divisor.principal hF z) =
      (WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).principalDivisor
        (Additive.ofMul (Units.map
          (functionFieldEquiv hxt).symm.toRingEquiv.toMulEquiv.toMonoidHom z)) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  apply (equivDivisor (hF := hF) (hx := hx) hxt).injective
  rw [AddEquiv.apply_symm_apply, equivDivisor_principal hxt]
  exact congrArg _ (Units.ext (by simp))

/-- **Linear equivalence on `X_F` is linear equivalence in `F`.** -/
@[simp]
theorem linearlyEquivalent_equivDivisor_iff (hxt : Transcendental k x)
    {D E : SchemeWeilDivisor (twoChartModel hF hx)} :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (Place.orderSystem hF).LinearlyEquivalent (equivDivisor hxt D) (equivDivisor hxt E) ↔
      (WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).LinearlyEquivalent D E := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  rw [← SchemeWeilDivisor.linearlyEquivalent_equivFunctionFieldDivisor_iff
      (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
      (isFunctionField_functionField hxt),
    ← WeilDivisor.OrderSystem.divisorClass_eq_iff, ← WeilDivisor.OrderSystem.divisorClass_eq_iff,
    ← (Divisor.classGroupEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes)
      (isFunctionField_functionField hxt) hF).injective.eq_iff,
    Divisor.classGroupEquivOfRingEquiv_divisorClass,
    Divisor.classGroupEquivOfRingEquiv_divisorClass,
    domCongr_equivOfRingEquiv_equivFunctionFieldDivisor,
    domCongr_equivOfRingEquiv_equivFunctionFieldDivisor]

/-- Pulling back divisors along `equivDivisor` preserves and reflects linear equivalence. -/
@[simp]
theorem linearlyEquivalent_equivDivisor_symm_iff (hxt : Transcendental k x) {D E : Divisor k F} :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).LinearlyEquivalent
        ((equivDivisor (hF := hF) (hx := hx) hxt).symm D)
        ((equivDivisor (hF := hF) (hx := hx) hxt).symm E) ↔
      (Place.orderSystem hF).LinearlyEquivalent D E := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  rw [← linearlyEquivalent_equivDivisor_iff (hF := hF) (hx := hx) hxt, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

/-! ### The divisor class group, the Picard group, and `Pic⁰` -/

/-- **The divisor class group of `X_F` is the divisor class group of `F`**: `Cl(X_F) ≃+ Cl(F)`. -/
noncomputable def classGroupEquiv (hxt : Transcendental k x) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).ClassGroup ≃+
      (Place.orderSystem hF).ClassGroup :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  haveI := isNoetherian (hF := hF) (hx := hx)
  (SchemeWeilDivisor.classGroupEquivFunctionField (valuativeCriterion_existence hF hx)
      (coheight_le_one hxt) (isFunctionField_functionField hxt)).trans
    (Divisor.classGroupEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes) (isFunctionField_functionField hxt) hF)

/-- `classGroupEquiv` sends `[D]` on `X_F` to `[equivDivisor hxt D]` on `F`. -/
@[simp]
theorem classGroupEquiv_divisorClass (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    classGroupEquiv hxt ((WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).divisorClass D) =
      (Place.orderSystem hF).divisorClass (equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  rw [classGroupEquiv, AddEquiv.trans_apply,
    SchemeWeilDivisor.classGroupEquivFunctionField_divisorClass,
    Divisor.classGroupEquivOfRingEquiv_divisorClass,
    domCongr_equivOfRingEquiv_equivFunctionFieldDivisor]

/-- `(classGroupEquiv hxt).symm` sends `[E]` on `F` to `[(equivDivisor hxt).symm E]` on `X_F`. -/
@[simp]
theorem classGroupEquiv_symm_divisorClass (hxt : Transcendental k x) (E : Divisor k F) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (classGroupEquiv (hF := hF) (hx := hx) hxt).symm ((Place.orderSystem hF).divisorClass E) =
      (WeilDivisor.OrderSystem.ofScheme (twoChartModel hF hx)).divisorClass
        ((equivDivisor (hF := hF) (hx := hx) hxt).symm E) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  apply (classGroupEquiv (hF := hF) (hx := hx) hxt).injective
  rw [AddEquiv.apply_symm_apply, classGroupEquiv_divisorClass, AddEquiv.apply_symm_apply]

/-- **The Picard group of `X_F` is the divisor class group of `F`**:
`Pic(X_F) ≃+ Cl(F)`, sending `[𝒪_{X_F}(D)]` to `[equivDivisor hxt D]`. -/
noncomputable def picardEquivClassGroup (hxt : Transcendental k x) :
    Additive (LineBundleClass (twoChartModel hF hx)) ≃+ (Place.orderSystem hF).ClassGroup :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  haveI := isNoetherian (hF := hF) (hx := hx)
  haveI : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  (SchemeWeilDivisor.classGroupAddEquivLineBundleClass (twoChartModel hF hx)).symm.trans
    (classGroupEquiv hxt)

/-- `picardEquivClassGroup` sends the line-bundle class `[𝒪_{X_F}(D)]` to the divisor class of
`equivDivisor hxt D`. -/
@[simp]
theorem picardEquivClassGroup_toLineBundleClass (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    picardEquivClassGroup hxt
        (Additive.ofMul (SchemeWeilDivisor.toLineBundleClass (coheight_le_one hxt) D)) =
      (Place.orderSystem hF).divisorClass (equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  have : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  rw [← SchemeWeilDivisor.classGroupToLineBundleClass_divisorClass,
    ← SchemeWeilDivisor.classGroupAddEquivLineBundleClass_apply, picardEquivClassGroup,
    AddEquiv.trans_apply, AddEquiv.symm_apply_apply, classGroupEquiv_divisorClass]

/-- `(picardEquivClassGroup hxt).symm` sends the divisor class of `E` in `Cl(F)` to the line-bundle
class `[𝒪_{X_F}((equivDivisor hxt).symm E)]`. -/
@[simp]
theorem picardEquivClassGroup_symm_divisorClass (hxt : Transcendental k x) (E : Divisor k F) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    (picardEquivClassGroup (hF := hF) (hx := hx) hxt).symm ((Place.orderSystem hF).divisorClass E) =
      Additive.ofMul (SchemeWeilDivisor.toLineBundleClass (coheight_le_one hxt)
        ((equivDivisor (hF := hF) (hx := hx) hxt).symm E)) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  apply (picardEquivClassGroup (hF := hF) (hx := hx) hxt).injective
  rw [AddEquiv.apply_symm_apply, picardEquivClassGroup_toLineBundleClass, AddEquiv.apply_symm_apply]

/-- **`Pic(X_F) ≃+ Cl(F)` intertwines the Euler-characteristic degree with divisor degree.** -/
@[simp]
theorem degreeClass_picardEquivClassGroup (hxt : Transcendental k x)
    (a : Additive (LineBundleClass (twoChartModel hF hx))) :
    Divisor.degreeClass hF (picardEquivClassGroup hxt a) =
      LineBundleClass.eulerDegree k a.toMul := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  let _ := isProper (hF := hF) (hx := hx)
  have := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
    (topologicalKrullDim_eq_one hxt)
  obtain ⟨D, hD⟩ := SchemeWeilDivisor.toLineBundleClass_surjective (coheight_le_one hxt) a.toMul
  have ha : a = Additive.ofMul (SchemeWeilDivisor.toLineBundleClass (coheight_le_one hxt) D) := by
    rw [hD, ofMul_toMul]
  rw [ha, picardEquivClassGroup_toLineBundleClass, Divisor.degreeClass_divisorClass,
    degree_equivDivisor, toMul_ofMul, LineBundleClass.eulerDegree_toLineBundleClass]

/-- `(picardEquivClassGroup hxt).symm` sends a divisor class of degree `d` to a line-bundle class of
Euler-characteristic degree `d`. -/
@[simp]
theorem eulerDegree_picardEquivClassGroup_symm (hxt : Transcendental k x)
    (c : (Place.orderSystem hF).ClassGroup) :
    LineBundleClass.eulerDegree k ((picardEquivClassGroup (hF := hF) (hx := hx) hxt).symm c).toMul =
      Divisor.degreeClass hF c := by
  rw [← degreeClass_picardEquivClassGroup hxt, AddEquiv.apply_symm_apply]

/-- **`Pic⁰` of the two-chart model is the degree-zero divisor class group of `F`**:
`Pic⁰(X_F) ≃+ Cl⁰(F)`, obtained by restricting `picardEquivClassGroup`. -/
noncomputable def picZeroEquivDegreeZeroClassGroup (hxt : Transcendental k x) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    haveI := isProper (hF := hF) (hx := hx)
    haveI : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
      (topologicalKrullDim_eq_one hxt)
    LineBundleClass.picZero k (twoChartModel hF hx) ≃+ (Divisor.degreeClass hF).ker :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  haveI := isNoetherian (hF := hF) (hx := hx)
  haveI := isProper (hF := hF) (hx := hx)
  haveI : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  haveI := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
    (topologicalKrullDim_eq_one hxt)
  (SchemeWeilDivisor.picZeroAddEquivDegreeZeroClassGroup k
      (isFunctionField_functionField hxt)).trans
    (Divisor.degreeZeroClassGroupEquivOfRingEquiv (RingEquiv.refl k)
      (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes)
      (isFunctionField_functionField hxt) hF)

/-- `picZeroEquivDegreeZeroClassGroup` is the restriction of `picardEquivClassGroup`. -/
@[simp]
theorem coe_picZeroEquivDegreeZeroClassGroup_apply (hxt : Transcendental k x) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    haveI := isProper (hF := hF) (hx := hx)
    haveI : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
      (topologicalKrullDim_eq_one hxt)
    ∀ a : LineBundleClass.picZero k (twoChartModel hF hx),
      (picZeroEquivDegreeZeroClassGroup hxt a : (Place.orderSystem hF).ClassGroup) =
        picardEquivClassGroup hxt (a : Additive (LineBundleClass (twoChartModel hF hx))) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  let _ := isProper (hF := hF) (hx := hx)
  have : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  have := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
    (topologicalKrullDim_eq_one hxt)
  intro a
  rw [picZeroEquivDegreeZeroClassGroup, AddEquiv.trans_apply,
    Divisor.coe_degreeZeroClassGroupEquivOfRingEquiv_apply,
    SchemeWeilDivisor.coe_picZeroAddEquivDegreeZeroClassGroup_apply k _
      (valuativeCriterion_existence hF hx),
    picardEquivClassGroup, AddEquiv.trans_apply, classGroupEquiv, AddEquiv.trans_apply]

/-- `(picZeroEquivDegreeZeroClassGroup hxt).symm` is the restriction of
`(picardEquivClassGroup hxt).symm`. -/
@[simp]
theorem coe_picZeroEquivDegreeZeroClassGroup_symm_apply (hxt : Transcendental k x)
    (c : (Divisor.degreeClass hF).ker) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
    haveI := isNoetherian (hF := hF) (hx := hx)
    haveI := isProper (hF := hF) (hx := hx)
    haveI : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
    haveI := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
      (topologicalKrullDim_eq_one hxt)
    ((picZeroEquivDegreeZeroClassGroup hxt).symm c :
        Additive (LineBundleClass (twoChartModel hF hx))) =
      (picardEquivClassGroup hxt).symm (c : (Place.orderSystem hF).ClassGroup) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx)
  let _ := isNoetherian (hF := hF) (hx := hx)
  let _ := isProper (hF := hF) (hx := hx)
  have : Fact (∀ y : twoChartModel hF hx, coheight y ≤ 1) := ⟨coheight_le_one hxt⟩
  have := finiteDimensional_cohomology_one_trivial_of_isProper k (X := twoChartModel hF hx)
    (topologicalKrullDim_eq_one hxt)
  apply (picardEquivClassGroup hxt).injective
  rw [← coe_picZeroEquivDegreeZeroClassGroup_apply hxt, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply]

end TauCeti.AlgebraicGeometry.twoChartModel
