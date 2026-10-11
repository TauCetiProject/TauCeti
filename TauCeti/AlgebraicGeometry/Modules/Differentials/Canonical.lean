/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Differentials.WeilRegularity
public import TauCeti.AlgebraicGeometry.LineBundle.SerreDuality

/-!
# The differential line bundle and canonical divisors

On an integral curve over an algebraically closed field, with invertible differential sheaf
and discrete valuation rings at its codimension-one points, the sheaf of relative differentials
is the sheaf of a canonical divisor. A separating rational function `t` gives the rational basis
`dt`; its Weil divisor `K` identifies a regular differential `f dt` with a section `f` of
`𝒪_X(K)`. The isomorphism is characterized by this rational-coordinate formula.

For a proper curve this identifies the differential line bundle with the canonical bundle
constructed from Weil differentials. The comparison here is over an algebraically closed field;
it does not provide descent to an arbitrary ground field or a natural trace pairing.

## References

* R. Hartshorne, *Algebraic Geometry*, II, Section 8, and IV, Section 1.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., Sections I.5 and IV.3.

The local comparison is `mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg`,
and the rational basis and Weil divisor are those of `kaehlerBasisOfSeparating` and
`weilDifferentialDivisor`.
-/

public section

open CategoryTheory AlgebraicGeometry Order Opposite
open scoped IntermediateField

namespace TauCeti.AlgebraicGeometry

universe u

noncomputable section

variable {k : Type u} [Field k] {X : Scheme.{u}}
  [X.Over (Spec (.of k))] [IsIntegral X]
  {t : X.functionField} (ht : Transcendental k t)
  [Algebra.IsSeparable k⟮t⟯ X.functionField]

private def differentialCoordinateEquiv :
    Ω[X.functionField⁄k] ≃ₗ[X.functionField] X.functionField :=
  (kaehlerBasisOfSeparating ht).equivFun.trans (LinearEquiv.funUnique Unit _ _)

private lemma differentialCoordinateEquiv_symm_apply (f : X.functionField) :
    (differentialCoordinateEquiv ht).symm f = f • KaehlerDifferential.D k X.functionField t := by
  simp only [differentialCoordinateEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]
  simp [kaehlerBasisOfSeparating_apply]

private def differentialCoordinateApp (U : X.Opens) [Nonempty U] :
    Γ(X.relativeDifferentials k, U) →ₗ[Γ(X, U)] Γ(Scheme.rationalFunctions X, U) :=
  (Scheme.rationalFunctionsEquiv U).symm.toLinearMap.comp
    (((differentialCoordinateEquiv ht).restrictScalars Γ(X, U)).toLinearMap.comp
      (rationalDifferential k U))

private lemma differentialCoordinateApp_naturality {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(X.relativeDifferentials k, U)) :
    differentialCoordinateApp ht V ((X.relativeDifferentials k).presheaf.map i.op s) =
      (Scheme.rationalFunctions X).presheaf.map i.op (differentialCoordinateApp ht U s) := by
  apply (Scheme.rationalFunctionsEquiv V).injective
  simp only [differentialCoordinateApp, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.restrictScalars_apply, LinearEquiv.apply_symm_apply]
  rw [Scheme.rationalFunctionsEquiv_map, LinearEquiv.apply_symm_apply,
    rationalDifferential_map]

private def differentialCoordinateHom : X.relativeDifferentials k ⟶ Scheme.rationalFunctions X := by
  classical
  refine
    { val :=
      { app := fun U ↦ if hU : Nonempty U.unop then
          letI := hU
          ModuleCat.ofHom (differentialCoordinateApp ht U.unop)
        else 0
        naturality := ?_ } }
  intro U V i
  by_cases hV : Nonempty V.unop
  · let := hV
    have hU : Nonempty U.unop := ⟨⟨(Classical.choice hV).1,
      i.unop.le (Classical.choice hV).2⟩⟩
    let := hU
    simp only [dite_eq_left hU, dite_eq_left hV]
    ext s
    exact differentialCoordinateApp_naturality ht i.unop
      (id s : Γ(X.relativeDifferentials k, U.unop))
  · ext s
    exact TopCat.Presheaf.section_ext
      ⟨(Scheme.rationalFunctions X).presheaf, (Scheme.rationalFunctions X).isSheaf⟩
      V.unop _ _ fun x hx ↦ (hV ⟨⟨x, hx⟩⟩).elim

private lemma differentialCoordinateHom_app (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials k, U)) :
    Scheme.rationalFunctionsEquiv U ((differentialCoordinateHom ht).app U s) =
      differentialCoordinateEquiv ht (rationalDifferential k U s) := by
  simp only [differentialCoordinateHom, Scheme.Modules.Hom.app,
    dite_eq_left (inferInstance : Nonempty U)]
  exact (Scheme.rationalFunctionsEquiv U).apply_symm_apply _

private lemma differentialCoordinateHom_app_injective (U : X.Opens)
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)] :
    Function.Injective ((differentialCoordinateHom ht).app U) := by
  intro s s' h
  by_cases hU : Nonempty U
  · let := hU
    apply rationalDifferential_injective k U
    apply (differentialCoordinateEquiv ht).injective
    simpa only [differentialCoordinateHom_app] using
      congrArg (Scheme.rationalFunctionsEquiv U) h
  · exact TopCat.Presheaf.section_ext
      ⟨(X.relativeDifferentials k).presheaf, (X.relativeDifferentials k).isSheaf⟩
      U s s' fun x hx ↦ (hU ⟨⟨x, hx⟩⟩).elim

variable [IsAlgClosed k] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  (hF : IsFunctionField k X.functionField)

/-- The rational differential `f dt` is regular on `U` exactly when `f` satisfies the
order bounds of the divisor of the Weil differential `dt`. -/
private lemma smul_d_mem_range_iff (U : X.Opens) [Nonempty U]
    (hU : ∀ y ∈ U, coheight y ≤ 1) (f : X.functionField) :
    f • KaehlerDifferential.D k X.functionField t ∈ Set.range (rationalDifferential k U) ↔
      f = 0 ∨ ∀ (y : CodimensionOnePoint X), (y : X) ∈ U →
        -weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed
          (weilDifferentialOfSeparating hF ht).2
          (by simpa only [ne_eq, Submodule.coe_eq_zero] using
            weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)) ≤
            X.ord f y := by
  let := weilDifferentialSpaceModule hF
  by_cases hf : f = 0
  · subst f
    simp
  let ω := f • weilDifferentialOfSeparating hF ht
  have hω : (ω : Module.Dual k (repartitionSpace k X.functionField)) ≠ 0 := by
    rw [coe_weilDifferentialSpaceModule_smul]
    exact repartitionDualMul_ne_zero hF hf
      (by simpa only [ne_eq, Submodule.coe_eq_zero] using
        weilDifferentialOfSeparating_ne_zero hF ht)
  have he : (kaehlerDifferentialEquivWeilDifferentialOfSeparating hF
      isIntegrallyClosedIn_of_isAlgClosed ht).symm ω =
      f • KaehlerDifferential.D k X.functionField t := by
    simp [ω]
  rw [← he, mem_range_rationalDifferential_iff_weilDifferentialOrder_nonneg_of_isAlgClosed
    hF ht U hU (fun _ _ ↦ inferInstance) ω hω]
  simp only [hf, false_or]
  have hdiv := weilDifferentialDivisor_repartitionDualMul hF
    isIntegrallyClosedIn_of_isAlgClosed (weilDifferentialOfSeparating hF ht).2
      (by simpa only [ne_eq, Submodule.coe_eq_zero] using
        weilDifferentialOfSeparating_ne_zero hF ht) (Units.mk0 f hf)
  have hcoe : (ω : Module.Dual k (repartitionSpace k X.functionField)) =
      repartitionDualMul hF f (weilDifferentialOfSeparating hF ht) :=
    coe_weilDifferentialSpaceModule_smul _ _ _
  apply forall_congr'
  intro y
  apply forall_congr'
  intro hy
  have hord : weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed ω.2 hω
      (X.toPlace (k := k) (y : X)) = X.ord f y +
        weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed
          (weilDifferentialOfSeparating hF ht).2
          (by simpa only [ne_eq, Submodule.coe_eq_zero] using
            weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)) := by
    have hdiv' := (weilDifferentialDivisor_congr hF
      isIntegrallyClosedIn_of_isAlgClosed hcoe ω.2 hω _ _).trans hdiv
    rw [← coeff_weilDifferentialDivisor, ← coeff_weilDifferentialDivisor,
      hdiv', WeilDivisor.coeff_add, Divisor.coeff_principal]
    rw [CodimensionOnePoint.toPlace_ord]
    rfl
  rw [hord]
  omega

variable (hdim : ∀ y : X, coheight y ≤ 1) (K : SchemeWeilDivisor X)
  (hK : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff K y =
    weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed
      (weilDifferentialOfSeparating hF ht).2
      (by simpa only [ne_eq, Submodule.coe_eq_zero] using
        weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)))

include hF hdim hK in
private lemma range_differentialCoordinateHom_app (U : X.Opens)
    (s : Γ(Scheme.rationalFunctions X, U)) :
    s ∈ Set.range ((differentialCoordinateHom ht).app U) ↔
      s ∈ SchemeWeilDivisor.sections K U := by
  by_cases hU : Nonempty U
  · let := hU
    rw [SchemeWeilDivisor.mem_sections_iff]
    simp_rw [hK]
    rw [← smul_d_mem_range_iff ht hF U (fun y _ ↦ hdim y),
      ← differentialCoordinateEquiv_symm_apply ht]
    constructor
    · rintro ⟨a, rfl⟩
      rw [differentialCoordinateHom_app, LinearEquiv.symm_apply_apply]
      exact ⟨a, rfl⟩
    · rintro ⟨a, ha⟩
      refine ⟨a, (Scheme.rationalFunctionsEquiv U).injective ?_⟩
      rw [differentialCoordinateHom_app, ha, LinearEquiv.apply_symm_apply]
  · have hbot : U = ⊥ := TopologicalSpace.Opens.not_nonempty_iff_eq_bot U |>.mp
      (fun ⟨x, hx⟩ ↦ hU ⟨⟨x, hx⟩⟩)
    have := Scheme.subsingleton_rationalFunctions U hbot
    simp only [SchemeWeilDivisor.sections_eq_top_of_eq_bot K hbot, Submodule.mem_top,
      iff_true]
    exact ⟨0, Subsingleton.elim _ _⟩

include hF hdim hK in
private lemma differentialCoordinateHom_mem (U : X.Opens)
    (s : Γ(X.relativeDifferentials k, U)) :
    (differentialCoordinateHom ht).app U s ∈ SchemeWeilDivisor.sections K U :=
  (range_differentialCoordinateHom_app ht hF hdim K hK U _).mp ⟨s, rfl⟩

/-- Reading a differential in the rational basis `dt` identifies `Ω_{X/k}` with `𝒪_X(K)`,
where `K` has the Weil orders of `dt` as its coefficients. The field is algebraically closed,
and the differential sheaf is assumed invertible. -/
def relativeDifferentialsIsoDivisorSheaf :
    X.relativeDifferentials k ≅ SchemeWeilDivisor.sheaf K := by
  let φ := SchemeWeilDivisor.sheafLift K (differentialCoordinateHom ht)
    (differentialCoordinateHom_mem ht hF hdim K hK)
  haveI : IsIso φ := SchemeWeilDivisor.isIso_sheafLift K _ _
    (fun U ↦ differentialCoordinateHom_app_injective ht U)
    (fun U s hs ↦ (range_differentialCoordinateHom_app ht hF hdim K hK U s).mpr hs)
  exact asIso φ

/-- The divisor-sheaf isomorphism sends a differential to its rational coefficient in `dt`. -/
@[simp]
lemma relativeDifferentialsIsoDivisorSheaf_hom_app (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials k, U)) :
    Scheme.rationalFunctionsEquiv U ((SchemeWeilDivisor.sheafι K).app U
      ((relativeDifferentialsIsoDivisorSheaf ht hF hdim K hK).hom.app U s)) =
      (kaehlerBasisOfSeparating ht).coord () (rationalDifferential k U s) := by
  rw [relativeDifferentialsIsoDivisorSheaf, asIso_hom,
    SchemeWeilDivisor.sheafι_app_sheafLift, differentialCoordinateHom_app]
  rfl

/-- The inverse divisor-sheaf isomorphism sends a rational coefficient `f` to `f dt`. -/
@[simp]
lemma relativeDifferentialsIsoDivisorSheaf_inv_app (U : X.Opens) [Nonempty U]
    (s : Γ(SchemeWeilDivisor.sheaf K, U)) :
    rationalDifferential k U
        ((relativeDifferentialsIsoDivisorSheaf ht hF hdim K hK).inv.app U s) =
      Scheme.rationalFunctionsEquiv U ((SchemeWeilDivisor.sheafι K).app U s) •
        KaehlerDifferential.D k X.functionField t := by
  let e := relativeDifferentialsIsoDivisorSheaf ht hF hdim K hK
  have he : e.hom.app U (e.inv.app U s) = s :=
    congr($(e.inv_hom_id).val.app (op U) s)
  have h := relativeDifferentialsIsoDivisorSheaf_hom_app ht hF hdim K hK U (e.inv.app U s)
  rw [he] at h
  apply (differentialCoordinateEquiv ht).injective
  rw [← differentialCoordinateEquiv_symm_apply ht, LinearEquiv.apply_symm_apply]
  exact h.symm

section ProperCurve

variable [IsNoetherian X] [X.IsSeparated]
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))

omit [IsLocallyNoetherian X] in
include hF hdim hex in
/-- On an algebraically closed curve with all the places of its function field, the invertible
sheaf of relative differentials is isomorphic to the Weil-differential canonical bundle. -/
theorem nonempty_iso_relativeDifferentials_canonicalBundle :
    Nonempty (X.relativeDifferentials k ≅ InvertibleSheaf.canonicalBundle hex hdim hF
      isIntegrallyClosedIn_of_isAlgClosed |>.obj) := by
  obtain ⟨t, ht, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  let ω := weilDifferentialOfSeparating hF ht
  have hω : (ω : Module.Dual k (repartitionSpace k X.functionField)) ≠ 0 := by
    simpa only [ne_eq, Submodule.coe_eq_zero] using weilDifferentialOfSeparating_ne_zero hF ht
  let K := (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
    (weilDifferentialDivisor hF isIntegrallyClosedIn_of_isAlgClosed ω.2 hω)
  have hK (y : CodimensionOnePoint X) : WeilDivisor.coeff K y =
      weilDifferentialOrder hF isIntegrallyClosedIn_of_isAlgClosed ω.2 hω
        (X.toPlace (k := k) (y : X)) := by
    simp only [K, SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
      coeff_weilDifferentialDivisor]
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_canonicalBundle_sheaf hex hdim hF
    isIntegrallyClosedIn_of_isAlgClosed (K := K) (by
      dsimp only [K]
      rw [(SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).apply_symm_apply]
      exact divisorClass_weilDifferentialDivisor hF isIntegrallyClosedIn_of_isAlgClosed ω.2 hω)
  exact ⟨relativeDifferentialsIsoDivisorSheaf ht hF hdim K hK ≪≫ e.symm⟩

omit [IsLocallyNoetherian X] in
include hF hdim hex in
/-- Serre duality for a line bundle with the differential line bundle as canonical bundle,
over an algebraically closed field. This asserts existence of a linear equivalence, not a
choice of natural pairing. -/
theorem nonempty_cohomologyOneDualEquivCohomologyZero_differentials_tensor_dual
    (L : InvertibleSheaf X) :
    Nonempty (Module.Dual k (Scheme.Modules.Cohomology L.obj 1) ≃ₗ[k]
      Scheme.Modules.Cohomology
        (InvertibleSheaf.tensorProduct ⟨X.relativeDifferentials k, inferInstance⟩
          (InvertibleSheaf.dual L)).obj 0) := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle hF hdim hex
  exact InvertibleSheaf.nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual
    hex hdim hF isIntegrallyClosedIn_of_isAlgClosed L
      ⟨X.relativeDifferentials k, inferInstance⟩ (LineBundleClass.mk_eq_mk_iff.mpr ⟨e⟩)

end ProperCurve

end

end TauCeti.AlgebraicGeometry
