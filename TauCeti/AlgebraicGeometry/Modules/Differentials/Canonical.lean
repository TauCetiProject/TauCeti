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

On an integral curve over a perfect exact constant field, with invertible differential sheaf and
discrete valuation rings at its codimension-one points, the sheaf of relative differentials is the
sheaf of a canonical divisor. A separating rational function `t` gives the rational basis
`dt`; its Weil divisor `K` identifies a regular differential `f dt` with a section `f` of
`𝒪_X(K)`. The isomorphism is characterized by this rational-coordinate formula. The
codimension-one points need not be rational, so this applies over finite fields and over number
fields as well as over algebraically closed fields.

For a proper curve this identifies the differential line bundle with the canonical bundle
constructed from Weil differentials. Consequently, for every line bundle `L`, the dual of
`H¹(X, L)` is linearly equivalent to `H⁰(X, Ω_{X/k} ⊗ L⁻¹)`. This is only the existence of a
noncanonical equivalence: the comparison does not provide a natural trace pairing.

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

private lemma differentialCoordinateEquiv_apply (ω : Ω[X.functionField⁄k]) :
    differentialCoordinateEquiv ht ω = (kaehlerBasisOfSeparating ht).coord () ω := by
  simp [differentialCoordinateEquiv, Module.Basis.coord_apply]

private lemma differentialCoordinateEquiv_symm_apply (f : X.functionField) :
    (differentialCoordinateEquiv ht).symm f = f • KaehlerDifferential.D k X.functionField t := by
  simp only [differentialCoordinateEquiv, LinearEquiv.trans_symm,
    LinearEquiv.trans_apply, Module.Basis.equivFun_symm_apply]
  simp [kaehlerBasisOfSeparating_apply]

private def differentialCoordinateApp (U : X.Opens) [Nonempty U] :
    (X.relativeDifferentials k).val.obj (op U) ⟶ (Scheme.rationalFunctions X).val.obj (op U) :=
  ModuleCat.ofHom (R := Γ(X, U)) (X := Γ(X.relativeDifferentials k, U))
    (Y := Γ(Scheme.rationalFunctions X, U)) <|
    (Scheme.rationalFunctionsEquiv U).symm.toLinearMap.comp
    (((differentialCoordinateEquiv ht).restrictScalars Γ(X, U)).toLinearMap.comp
      (rationalDifferential k U))

private lemma differentialCoordinateApp_apply (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials k, U)) :
    differentialCoordinateApp ht U s = (Scheme.rationalFunctionsEquiv U).symm
      (differentialCoordinateEquiv ht (rationalDifferential k U s)) :=
  (rfl)

private lemma differentialCoordinateApp_naturality {U V : X.Opens}
    [Nonempty U] [Nonempty V] (i : V ⟶ U) (s : Γ(X.relativeDifferentials k, U)) :
    differentialCoordinateApp ht V ((X.relativeDifferentials k).presheaf.map i.op s) =
      (Scheme.rationalFunctions X).presheaf.map i.op (differentialCoordinateApp ht U s) := by
  apply (Scheme.rationalFunctionsEquiv V).injective
  simp only [differentialCoordinateApp_apply, Scheme.rationalFunctionsEquiv_map,
    LinearEquiv.apply_symm_apply, rationalDifferential_map]

private def differentialCoordinateHom : X.relativeDifferentials k ⟶ Scheme.rationalFunctions X :=
  Scheme.rationalFunctionsHom (X.relativeDifferentials k) (differentialCoordinateApp ht)
    (fun i s ↦ differentialCoordinateApp_naturality ht i s)

private lemma differentialCoordinateHom_app (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials k, U)) :
    Scheme.rationalFunctionsEquiv U ((differentialCoordinateHom ht).app U s) =
      differentialCoordinateEquiv ht (rationalDifferential k U s) := by
  rw [differentialCoordinateHom, Scheme.rationalFunctionsHom_app]
  exact (Scheme.rationalFunctionsEquiv U).apply_symm_apply _

private lemma differentialCoordinateHom_app_injective (U : X.Opens)
    [SheafOfModules.isInvertible X (X.relativeDifferentials k)] :
    Function.Injective ((differentialCoordinateHom ht).app U) := by
  apply Scheme.rationalFunctionsHom_app_injective
  intro U _ s s' h
  apply rationalDifferential_injective k U
  apply (differentialCoordinateEquiv ht).injective
  simpa only [differentialCoordinateApp_apply ht U s, differentialCoordinateApp_apply ht U s',
    LinearEquiv.apply_symm_apply] using
    congrArg (Scheme.rationalFunctionsEquiv U) h

section Comparison

variable [PerfectField k] [IsLocallyNoetherian X]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)

variable (hdim : ∀ y : X, coheight y ≤ 1) (K : SchemeWeilDivisor X)
  (hK : ∀ y : CodimensionOnePoint X, WeilDivisor.coeff K y =
    weilDifferentialOrder hF hk
      (weilDifferentialOfSeparating hF ht).2
      (coe_weilDifferentialOfSeparating_ne_zero hF ht) (X.toPlace (k := k) (y : X)))

include hF hdim hK in
private lemma range_differentialCoordinateHom_app (U : X.Opens)
    (s : Γ(Scheme.rationalFunctions X, U)) :
    s ∈ Set.range ((differentialCoordinateHom ht).app U) ↔
      s ∈ SchemeWeilDivisor.sections K U := by
  by_cases hU : Nonempty U
  · let := hU
    rw [SchemeWeilDivisor.mem_sections_iff]
    simp_rw [hK]
    rw [← smul_D_mem_range_rationalDifferential_iff hF hk ht U (fun y _ ↦ hdim y)
      (fun _ _ ↦ inferInstance),
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
  (range_differentialCoordinateHom_app ht hF hk hdim K hK U _).mp ⟨s, rfl⟩

/-- Reading a differential in the rational basis `dt` identifies `Ω_{X/k}` with `𝒪_X(K)`,
where `K` has the Weil orders of `dt` as its coefficients. The constant field is perfect and
exact, and the differential sheaf is assumed invertible; the codimension-one places may have any
degree. -/
def relativeDifferentialsIsoDivisorSheaf :
    X.relativeDifferentials k ≅ SchemeWeilDivisor.sheaf K := by
  let φ := SchemeWeilDivisor.sheafLift K (differentialCoordinateHom ht)
    (differentialCoordinateHom_mem ht hF hk hdim K hK)
  haveI : IsIso φ := SchemeWeilDivisor.isIso_sheafLift K _ _
    (fun U ↦ differentialCoordinateHom_app_injective ht U)
    (fun U s hs ↦ (range_differentialCoordinateHom_app ht hF hk hdim K hK U s).mpr hs)
  exact asIso φ

/-- The divisor-sheaf isomorphism sends a differential to its rational coefficient in `dt`. -/
@[simp]
lemma relativeDifferentialsIsoDivisorSheaf_hom_app (U : X.Opens) [Nonempty U]
    (s : Γ(X.relativeDifferentials k, U)) :
    Scheme.rationalFunctionsEquiv U ((SchemeWeilDivisor.sheafι K).app U
      ((relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK).hom.app U s)) =
      (kaehlerBasisOfSeparating ht).coord () (rationalDifferential k U s) := by
  rw [relativeDifferentialsIsoDivisorSheaf, asIso_hom,
    SchemeWeilDivisor.sheafι_app_sheafLift, differentialCoordinateHom_app,
    differentialCoordinateEquiv_apply]

/-- The inverse divisor-sheaf isomorphism sends a rational coefficient `f` to `f dt`. -/
@[simp]
lemma relativeDifferentialsIsoDivisorSheaf_inv_app (U : X.Opens) [Nonempty U]
    (s : Γ(SchemeWeilDivisor.sheaf K, U)) :
    rationalDifferential k U
        ((relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK).inv.app U s) =
      Scheme.rationalFunctionsEquiv U ((SchemeWeilDivisor.sheafι K).app U s) •
        KaehlerDifferential.D k X.functionField t := by
  let e := relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK
  have he : e.hom.app U (e.inv.app U s) = s :=
    congr($(e.inv_hom_id).val.app (op U) s)
  have h := relativeDifferentialsIsoDivisorSheaf_hom_app ht hF hk hdim K hK U
    (e.inv.app U s)
  rw [he] at h
  apply (differentialCoordinateEquiv ht).injective
  rw [← differentialCoordinateEquiv_symm_apply ht, LinearEquiv.apply_symm_apply]
  exact h.symm

end Comparison

section ProperCurve

variable [PerfectField k] [IsNoetherian X] [X.IsSeparated]
  [∀ y : CodimensionOnePoint X, IsDiscreteValuationRing (X.presheaf.stalk (y : X))]
  [SheafOfModules.isInvertible X (X.relativeDifferentials k)]
  (hF : IsFunctionField k X.functionField) (hk : IsIntegrallyClosedIn k X.functionField)
  (hdim : ∀ y : X, coheight y ≤ 1)
  (hex : ValuativeCriterion.Existence (X ↘ Spec (.of k)))

include hF hk hdim hex in
/-- On a curve over a perfect exact constant field with all the places of its function field, the
invertible sheaf of relative differentials is isomorphic to the Weil-differential canonical
bundle. -/
theorem nonempty_iso_relativeDifferentials_canonicalBundle :
    Nonempty (X.relativeDifferentials k ≅
      (InvertibleSheaf.canonicalBundle hex hdim hF hk).obj) := by
  obtain ⟨t, ht, hsep⟩ := hF.exists_transcendental_and_isSeparable_adjoin_of_perfectField
  let := hsep
  let ω := weilDifferentialOfSeparating hF ht
  have hω : (ω : Module.Dual k (repartitionSpace k X.functionField)) ≠ 0 :=
    coe_weilDifferentialOfSeparating_ne_zero hF ht
  let K := (SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).symm
    (weilDifferentialDivisor hF hk ω.2 hω)
  have hK (y : CodimensionOnePoint X) : WeilDivisor.coeff K y =
      weilDifferentialOrder hF hk ω.2 hω (X.toPlace (k := k) (y : X)) := by
    simp only [K, SchemeWeilDivisor.coeff_equivFunctionFieldDivisor_symm,
      coeff_weilDifferentialDivisor]
  obtain ⟨e⟩ := InvertibleSheaf.nonempty_iso_canonicalBundle_sheaf hex hdim hF hk (K := K) (by
    dsimp only [K]
    rw [(SchemeWeilDivisor.equivFunctionFieldDivisor hex hdim).apply_symm_apply]
    exact divisorClass_weilDifferentialDivisor hF hk ω.2 hω)
  exact ⟨relativeDifferentialsIsoDivisorSheaf ht hF hk hdim K hK ≪≫ e.symm⟩

include hF hk hdim hex in
/-- Over a perfect exact constant field, the dual of `H¹(X, L)` is linearly equivalent to
`H⁰(X, Ω_{X/k} ⊗ L⁻¹)`, by the identification of the differential line bundle with the canonical
bundle. This asserts only the existence of a noncanonical linear equivalence, not a natural
duality pairing. -/
theorem nonempty_cohomologyOneDualEquivCohomologyZero_differentials_tensor_dual
    (L : InvertibleSheaf X) :
    Nonempty (Module.Dual k (Scheme.Modules.Cohomology L.obj 1) ≃ₗ[k]
      Scheme.Modules.Cohomology
        (InvertibleSheaf.tensorProduct ⟨X.relativeDifferentials k, inferInstance⟩
          (InvertibleSheaf.dual L)).obj 0) := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle hF hk hdim hex
  exact InvertibleSheaf.nonempty_cohomologyOneDualEquivCohomologyZero_tensor_dual
    hex hdim hF hk L
      ⟨X.relativeDifferentials k, inferInstance⟩ (LineBundleClass.mk_eq_mk_iff.mpr ⟨e⟩)

end ProperCurve

end

end TauCeti.AlgebraicGeometry
