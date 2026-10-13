/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rational
public import TauCeti.AlgebraicGeometry.WeilDivisor.Scheme.Place
public import TauCeti.FieldTheory.FunctionField.Differential.Regular
public import TauCeti.RingTheory.Kaehler.MapSemilinear

/-!
# Regular rational differentials and Weil orders on curves

The rational image of a differential stalk at a discrete valuation ring point is the image of
the Kähler differentials of its associated place's valuation ring. This comparison holds over
an arbitrary field and does not require that the place be rational.

For an invertible differential sheaf on an open subset of dimension at most one, regularity is
detected at its codimension-one points. At rational places over a perfect exact constant field
with infinitely many rational places, the Kähler–Weil comparison identifies this condition
with nonnegative Weil order. Over an algebraically closed field all places are rational and
the infinitude and exact-constant-field conditions are automatic. Thus a nonzero Weil
differential corresponds to a regular section on the open subset exactly when it has no poles
there. This supplies the local-lattice comparison for identifying the differential line bundle
with a canonical divisor sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Section 8, and IV, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Section IV.3.

The sheaf regularity criterion is `mem_range_rationalDifferential_iff`. The valuation-ring
comparison uses `Scheme.stalkToPlaceIntegersAlgEquiv`, and the local order criterion uses
`Place.mem_range_map_iff_weilDifferentialOrder_nonneg`.
-/

public section

open AlgebraicGeometry Order
open scoped IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsIntegral X]

/-- A differential stalk at a discrete valuation ring point has the same rational image as
the Kähler differentials of the associated place's valuation ring. This holds for places of
arbitrary residue degree. -/
theorem mem_range_rationalDifferentialStalk_iff_mem_range_map (x : X)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (η : Ω[X.functionField⁄k]) :
    η ∈ Set.range (rationalDifferentialStalk k x) ↔
      η ∈ (KaehlerDifferential.map k k (X.toPlace (k := k) x).integers
        X.functionField).range := by
  let e := X.stalkToPlaceIntegersAlgEquiv (k := k) x
  have hcomp : (IsScalarTower.toAlgHom k (X.toPlace (k := k) x).integers
      X.functionField).comp e.toAlgHom =
      IsScalarTower.toAlgHom k (X.presheaf.stalk x) X.functionField := by
    ext a
    exact X.coe_stalkToPlaceIntegersAlgEquiv (k := k) x a
  have h (ξ : Ω[X.presheaf.stalk x⁄k]) :
      KaehlerDifferential.map k k (X.toPlace (k := k) x).integers X.functionField
          (KaehlerDifferential.mapSemilinear e.toAlgHom ξ) =
        KaehlerDifferential.map k k (X.presheaf.stalk x) X.functionField ξ := by
    rw [← KaehlerDifferential.mapSemilinear_toAlgHom_apply,
      ← KaehlerDifferential.mapSemilinear_comp_apply, hcomp,
      KaehlerDifferential.mapSemilinear_toAlgHom_apply]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨KaehlerDifferential.mapSemilinear e.toAlgHom
      (X.relativeDifferentialsStalkEquiv k x s), ?_⟩
    rw [h, ← rationalDifferentialStalk_symm_apply,
      LinearEquiv.symm_apply_apply]
  · rintro ⟨ξ, rfl⟩
    refine ⟨(X.relativeDifferentialsStalkEquiv k x).symm
      (KaehlerDifferential.mapSemilinear e.symm.toAlgHom ξ), ?_⟩
    rw [rationalDifferentialStalk_symm_apply, ← h,
      ← KaehlerDifferential.mapSemilinear_comp_apply, AlgEquiv.comp_symm,
      KaehlerDifferential.mapSemilinear_id_apply]

section Invertible

variable [SheafOfModules.isInvertible X (X.relativeDifferentials k)]

variable [PerfectField k]
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)
  (hinf : {P : Place k X.functionField | P.degree = 1}.Infinite)
  {t : X.functionField} (ht : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ X.functionField]

include hinf in
/-- Over a perfect exact constant field with infinitely many rational places, a nonzero Weil
differential corresponds to a regular differential on a curve open exactly when its order is
nonnegative at every codimension-one point there. The degree-one hypothesis specifies the
places for which the local Kähler–Weil regularity comparison is available. -/
theorem mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg
    (U : X.Opens) [Nonempty U] (hU : ∀ y ∈ U, coheight y ≤ 1)
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hdeg : ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
      letI := hDVR y hy
      (X.toPlace (k := k) (y : X)).degree = 1)
    (ω : weilDifferentialSpace k X.functionField)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k X.functionField)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hk ht).symm ω ∈
        Set.range (rationalDifferential k U) ↔
      ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
        letI := hDVR y hy
        0 ≤ weilDifferentialOrder hF hk ω.2 hω (X.toPlace (k := k) (y : X)) := by
  rw [mem_range_rationalDifferential_iff_codimensionOne k U hU]
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  let := hDVR y hy
  rw [mem_range_rationalDifferentialStalk_iff_mem_range_map]
  exact (X.toPlace (k := k) (y : X)).mem_range_map_iff_weilDifferentialOrder_nonneg
    (hdeg y hy) hF hk hinf ht ω hω

variable [IsLocallyNoetherian X]

include hinf in
/-- The rational differential `f dt` is regular on `U` exactly when `f` satisfies the
order bounds of the divisor of the Weil differential `dt`. Only codimension-one stalks
on `U` are required to be discrete valuation rings with rational associated places. The
constant field is perfect and exact, and has infinitely many rational places. -/
theorem smul_D_mem_range_rationalDifferential_iff (U : X.Opens) [Nonempty U]
    (hU : ∀ y ∈ U, coheight y ≤ 1)
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (hdeg : ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
      letI := hDVR y hy
      (X.toPlace (k := k) (y : X)).degree = 1) (f : X.functionField) :
    f • KaehlerDifferential.D k X.functionField t ∈ Set.range (rationalDifferential k U) ↔
      f = 0 ∨ ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
        letI := hDVR y hy;
        -weilDifferentialOrder hF hk
          (weilDifferentialOfSeparating hF ht).2
          (coe_weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)) ≤
            X.ord f y := by
  let := weilDifferentialSpaceModule hF
  by_cases hf : f = 0
  · subst f
    simp
  let ω := f • weilDifferentialOfSeparating hF ht
  have hω : (ω : Module.Dual k (repartitionSpace k X.functionField)) ≠ 0 := by
    rw [coe_weilDifferentialSpaceModule_smul]
    exact repartitionDualMul_ne_zero hF hf
      (coe_weilDifferentialOfSeparating_ne_zero hF ht)
  have he : (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF hk ht).symm ω =
      f • KaehlerDifferential.D k X.functionField t := by
    simp [ω]
  rw [← he, mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg
    hF hk hinf ht U hU hDVR hdeg ω hω]
  simp only [hf, false_or]
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  let := hDVR y hy
  have hord := weilDifferentialOrder_repartitionDualMul hF hk
    (weilDifferentialOfSeparating hF ht).2
    (coe_weilDifferentialOfSeparating_ne_zero hF ht) (Units.mk0 f hf)
    (X.toPlace (k := k) (y : X))
  simp only [Units.val_mk0, CodimensionOnePoint.toPlace_ord] at hord
  simp only [ω, coe_weilDifferentialSpaceModule_smul]
  rw [hord]
  omega

end Invertible

section IsAlgClosed

variable [IsAlgClosed k] [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  (hF : IsFunctionField k X.functionField)
  {t : X.functionField} (ht : Transcendental k t) [Algebra.IsSeparable k⟮t⟯ X.functionField]

/-- Over an algebraically closed field, a nonzero Weil differential corresponds to a regular
differential on a curve open exactly when it has nonnegative order at all codimension-one
points there. Algebraic closure supplies exact constants, rationality of every place, and
infinitely many rational places. -/
theorem mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg_of_isAlgClosed
    (U : X.Opens) [Nonempty U] (hU : ∀ y ∈ U, coheight y ≤ 1)
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X)))
    (ω : weilDifferentialSpace k X.functionField)
    (hω : (ω : Module.Dual k ↥(repartitionSpace k X.functionField)) ≠ 0) :
    (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF
        isIntegrallyClosedIn_of_isAlgClosed ht).symm ω ∈ Set.range (rationalDifferential k U) ↔
      ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
        letI := hDVR y hy
        0 ≤ weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed ω.2 hω
          (X.toPlace (k := k) (y : X)) := by
  apply mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg hF
    isIntegrallyClosedIn_of_isAlgClosed (Place.infinite_setOf_degree_eq_one hF) ht U hU hDVR
  intro y hy
  let := hDVR y hy
  exact (X.toPlace (k := k) (y : X)).degree_eq_one_of_isAlgClosed_of_isFunctionField hF

variable [IsLocallyNoetherian X]

/-- The rational differential `f dt` is regular on `U` exactly when `f` satisfies the
order bounds of the divisor of the Weil differential `dt`. Only codimension-one stalks
on `U` are required to be discrete valuation rings. -/
theorem smul_D_mem_range_rationalDifferential_iff_of_isAlgClosed (U : X.Opens) [Nonempty U]
    (hU : ∀ y ∈ U, coheight y ≤ 1)
    (hDVR : ∀ y : CodimensionOnePoint X, (y : X) ∈ U →
      IsDiscreteValuationRing (X.presheaf.stalk (y : X))) (f : X.functionField) :
    f • KaehlerDifferential.D k X.functionField t ∈ Set.range (rationalDifferential k U) ↔
      f = 0 ∨ ∀ (y : CodimensionOnePoint X) (hy : (y : X) ∈ U),
        letI := hDVR y hy;
        -weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed
          (weilDifferentialOfSeparating hF ht).2
          (coe_weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)) ≤
            X.ord f y := by
  apply smul_D_mem_range_rationalDifferential_iff hF isIntegrallyClosedIn_of_isAlgClosed
    (Place.infinite_setOf_degree_eq_one hF) ht U hU hDVR
  intro y hy
  let := hDVR y hy
  exact (X.toPlace (k := k) (y : X)).degree_eq_one_of_isAlgClosed_of_isFunctionField hF

end IsAlgClosed

end

end TauCeti.AlgebraicGeometry
