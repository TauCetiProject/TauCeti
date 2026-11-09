/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Divisor
public import TauCeti.AlgebraicGeometry.Curves.TwoChartModel.Genus
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Canonical
public import TauCeti.AlgebraicGeometry.Modules.Differentials.Rank
public import TauCeti.AlgebraicGeometry.Morphisms.Smooth.RelativeDimension
public import TauCeti.FieldTheory.FunctionField.Differential.Equiv

/-!
# Sheaf cohomology, Riemann–Roch, Serre duality, and differentials on the two-chart model

Let `F / k` be an algebraic function field, `x ∈ F` transcendental over `k`, and
`X_F = TauCeti.AlgebraicGeometry.twoChartModel hF hx` its regular proper curve model over `k`.
Using the divisor equivalence `twoChartModel.equivDivisor` (`Div(X_F) ≃+ Div(F)`), the
function-field isomorphism `twoChartModel.functionFieldEquiv` (`k(X_F) ≃ₐ[k] F`), and the
transport of Riemann–Roch spaces, repartitions, and Weil differentials, this file identifies the
sheaf cohomology and canonical invariants of `X_F` with their function-field counterparts on `F`:

* **Over an arbitrary base field `k`**:
  `Γ(X_F, 𝒪(D)) ≃ₗ[k] L(D)` (`twoChartModel.globalSectionsEquivRiemannRochSpace`),
  `H⁰(X_F, 𝒪(D)) ≃ₗ[k] L(D)` (`twoChartModel.cohomologyZeroEquivRiemannRochSpace`),
  `dim_k H⁰(X_F, 𝒪(D)) = ℓ(D)` (`twoChartModel.finrank_cohomology_zero_sheaf_eq_dim`),
  `A_F ⧸ (A_F(D) + F) ≃ₗ[k] H¹(X_F, 𝒪(D))` (`twoChartModel.repartitionQuotientEquivCohomologyOne`),
  and `H¹(X_F, 𝒪(D))^∨ ≃ₗ[k] Ω_F(D)`
  (`twoChartModel.cohomologyOneDualEquivWeilDifferentialFiltration`).
* **When `k` is integrally closed in `F`** (`IsIntegrallyClosedIn k F`):
  `dim_k H¹(X_F, 𝒪(D)) = i(D) = ℓ(W - D)`
  (`twoChartModel.finrank_cohomology_one_sheaf_eq_indexOfSpecialty` and
  `twoChartModel.finrank_cohomology_one_sheaf_eq_dim_sub`), the Euler-characteristic and
  dimension forms of Riemann–Roch on `X_F`
  (`twoChartModel.eulerCharBelow_sheaf_eq_degree_add_one_sub_genus` and
  `twoChartModel.finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf`), and Serre
  duality `H¹(X_F, 𝒪(D))^∨ ≃ₗ[k] H⁰(X_F, 𝒪(K - D))`
  (`twoChartModel.cohomologyOneDualEquivCohomologyZero`) with explicit pairing `(f, [a]) ↦ ω(f · a)`
  on `F`
  (`twoChartModel.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne`).
* **Canonical bundle and relative differentials** (still for `IsIntegrallyClosedIn k F`):
  `twoChartModel.canonicalBundle` maps under `twoChartModel.picardEquivClassGroup` (`Pic(X_F) ≃+
  Cl(F)`) to `TauCeti.canonicalClass` and has Euler-characteristic degree `2g - 2`, `g` global
  sections, and one-dimensional `H¹`. When `Ω_{X_F/k}` is invertible — in particular whenever
  `X_F` is smooth over `k` (`twoChartModel.smoothOfRelativeDimension_one`,
  `twoChartModel.isInvertible_relativeDifferentials`) — `[Ω_{X_F/k}]` also
  maps to `TauCeti.canonicalClass` and satisfies `deg Ω_{X_F/k} = 2g - 2`,
  `dim_k H⁰(X_F, Ω_{X_F/k}) = g`, and `dim_k H¹(X_F, Ω_{X_F/k}) = 1`.

## References

* J.-P. Serre, *Algebraic Groups and Class Fields*, Chapter II.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Section I.5 and Appendix B.
* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Chapter IV, Section 1.
-/

public section

open CategoryTheory _root_.AlgebraicGeometry Order
open Module (finrank)

namespace TauCeti.AlgebraicGeometry.twoChartModel

universe u

variable {k F : Type u} [Field k] [Field F] [Algebra k F] {hF : IsFunctionField k F} {x : F}
  {hx : x ≠ 0}

/-- The top open of `twoChartModel hF hx` is nonempty. -/
local instance nonemptyTopOpensTwoChartModel : Nonempty (⊤ : (twoChartModel hF hx).Opens) :=
  ⟨⟨Classical.choice inferInstance, trivial⟩⟩

/-! ### Global sections, `H⁰`, repartition quotients, and `H¹^∨` over an arbitrary field -/

private noncomputable def riemannRochSpaceFunctionFieldEquiv (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) :
    ↥(riemannRochSpace D) ≃ₗ[k]
      ↥(riemannRochSpace (Finsupp.domCongr
        (Place.equivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
          (id (functionFieldEquiv hxt).commutes)) D)) :=
  riemannRochSpaceEquivOfRingEquiv (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) D

@[simp]
private theorem coe_riemannRochSpaceFunctionFieldEquiv_apply (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) (z : ↥(riemannRochSpace D)) :
    (riemannRochSpaceFunctionFieldEquiv hxt D z : F) = functionFieldEquiv hxt (z : _) :=
  riemannRochSpaceEquivOfRingEquiv_apply (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
    (id (functionFieldEquiv hxt).commutes) D z

/-- **Global sections of `𝒪_{X_F}(D)` form the Riemann–Roch space `L(D)` in `F`.** -/
noncomputable def globalSectionsEquivRiemannRochSpace (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Γ(SchemeWeilDivisor.sheaf D, ⊤) ≃ₗ[k] ↥(riemannRochSpace (equivDivisor hxt D)) :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  (SchemeWeilDivisor.globalSectionsEquivRiemannRochSpace
      (valuativeCriterion_existence hF hx) (coheight_le_one hxt) D).trans
    ((riemannRochSpaceFunctionFieldEquiv hxt _).trans (LinearEquiv.ofEq _ _
      (congrArg riemannRochSpace (domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt D))))

/-- `globalSectionsEquivRiemannRochSpace` sends a global section of `𝒪_{X_F}(D)` to its underlying
element of `F` via `functionFieldEquiv`. -/
@[simp]
theorem coe_globalSectionsEquivRiemannRochSpace_apply (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    ∀ s : Γ(SchemeWeilDivisor.sheaf D, ⊤),
      (globalSectionsEquivRiemannRochSpace hxt D s : F) =
        functionFieldEquiv hxt
          (Scheme.rationalFunctionsEquiv ⊤ ((SchemeWeilDivisor.sheafι D).app ⊤ s)) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  intro s
  simp [globalSectionsEquivRiemannRochSpace]

/-- `(globalSectionsEquivRiemannRochSpace hxt D).symm` sends `f ∈ L(D)` to the global section whose
underlying rational function is `(functionFieldEquiv hxt).symm f`. -/
@[simp]
theorem rationalFunctionsEquiv_sheafι_globalSectionsEquivRiemannRochSpace_symm
    (hxt : Transcendental k x) (D : SchemeWeilDivisor (twoChartModel hF hx))
    (f : ↥(riemannRochSpace (equivDivisor hxt D))) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Scheme.rationalFunctionsEquiv ⊤ ((SchemeWeilDivisor.sheafι D).app ⊤
        ((globalSectionsEquivRiemannRochSpace hxt D).symm f)) =
      (functionFieldEquiv hxt).symm (f : F) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  apply (functionFieldEquiv hxt).injective
  rw [← coe_globalSectionsEquivRiemannRochSpace_apply hxt D, LinearEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- **Zeroth cohomology of `𝒪_{X_F}(D)` is the Riemann–Roch space `L(D)` in `F`.** -/
noncomputable def cohomologyZeroEquivRiemannRochSpace (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0 ≃ₗ[k]
      ↥(riemannRochSpace (equivDivisor hxt D)) :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  (Scheme.Modules.cohomologyZeroBaseLinearEquiv k (twoChartModel hF hx)
    (SchemeWeilDivisor.sheaf D)).trans (globalSectionsEquivRiemannRochSpace hxt D)

/-- `cohomologyZeroEquivRiemannRochSpace` reads a degree-zero cohomology class as an element of `F`
via `cohomologyZeroEquiv` and `functionFieldEquiv`. -/
@[simp]
theorem coe_cohomologyZeroEquivRiemannRochSpace_apply (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    ∀ s : Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0,
      (cohomologyZeroEquivRiemannRochSpace hxt D s : F) =
        functionFieldEquiv hxt (Scheme.rationalFunctionsEquiv ⊤
          ((SchemeWeilDivisor.sheafι D).app ⊤ (Scheme.Modules.cohomologyZeroEquiv _ s))) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  intro s
  simp [cohomologyZeroEquivRiemannRochSpace]

/-- `(cohomologyZeroEquivRiemannRochSpace hxt D).symm` sends `f ∈ L(D)` to the degree-zero
cohomology class whose global section has rational function `(functionFieldEquiv hxt).symm f`. -/
@[simp]
theorem rationalFunctionsEquiv_sheafι_cohomologyZeroEquivRiemannRochSpace_symm
    (hxt : Transcendental k x) (D : SchemeWeilDivisor (twoChartModel hF hx))
    (f : ↥(riemannRochSpace (equivDivisor hxt D))) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Scheme.rationalFunctionsEquiv ⊤ ((SchemeWeilDivisor.sheafι D).app ⊤
        (Scheme.Modules.cohomologyZeroEquiv _
          ((cohomologyZeroEquivRiemannRochSpace hxt D).symm f))) =
      (functionFieldEquiv hxt).symm (f : F) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  apply (functionFieldEquiv hxt).injective
  rw [← coe_cohomologyZeroEquivRiemannRochSpace_apply hxt D, LinearEquiv.apply_symm_apply,
    AlgEquiv.apply_symm_apply]

/-- **`dim_k H⁰(X_F, 𝒪_{X_F}(D)) = ℓ(D)`** over any base field `k`. -/
theorem finrank_cohomology_zero_sheaf_eq_dim (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0) =
      Divisor.dim (equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  rw [Divisor.dim_def]
  exact (cohomologyZeroEquivRiemannRochSpace hxt D).finrank_eq

/-- The first cohomology class in `H¹(X_F, 𝒪_{X_F}(D))` attached to a repartition of `F`. -/
noncomputable def repartitionToCohomologyOne (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    ↥(repartitionSpace k F) →ₗ[k] Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1 :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  let e : ↥(repartitionSpace k (twoChartModel hF hx).functionField) ≃ₗ[k]
      ↥(repartitionSpace k F) :=
    repartitionSpaceEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes)
  (SchemeWeilDivisor.repartitionToCohomologyOne (valuativeCriterion_existence hF hx)
    (coheight_le_one hxt) D).comp e.symm.toLinearMap

-- Not `@[simp]`: `SchemeWeilDivisor.repartitionToCohomologyOne_apply` would further expand the
-- right-hand side into `principalPartsBoundary`.
/-- `repartitionToCohomologyOne` transports `a ∈ A_F` along `(functionFieldEquiv hxt).symm` and
applies `SchemeWeilDivisor.repartitionToCohomologyOne`. -/
theorem repartitionToCohomologyOne_apply (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) (a : ↥(repartitionSpace k F)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    repartitionToCohomologyOne hxt D a =
      SchemeWeilDivisor.repartitionToCohomologyOne (valuativeCriterion_existence hF hx)
        (coheight_le_one hxt) D
        ((repartitionSpaceEquivOfRingEquiv (RingEquiv.refl k)
          (functionFieldEquiv hxt).toRingEquiv
          (id (functionFieldEquiv hxt).commutes)).symm a) :=
  (rfl)

/-- Every class in `H¹(X_F, 𝒪_{X_F}(D))` is represented by a repartition of `F`. -/
theorem repartitionToCohomologyOne_surjective (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Function.Surjective (repartitionToCohomologyOne hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  let e : ↥(repartitionSpace k (twoChartModel hF hx).functionField) ≃ₗ[k]
      ↥(repartitionSpace k F) :=
    repartitionSpaceEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes)
  exact (SchemeWeilDivisor.repartitionToCohomologyOne_surjective
    (valuativeCriterion_existence hF hx) (coheight_le_one hxt) D).comp e.symm.surjective

private noncomputable def repartitionQuotientFunctionFieldEquiv (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) :
    (↥(repartitionSpace k (twoChartModel hF hx).functionField) ⧸
        submoduleOfAdeleFiltrationSupDiagonalRepartitions D) ≃ₗ[k]
      (↥(repartitionSpace k F) ⧸
        submoduleOfAdeleFiltrationSupDiagonalRepartitions
          (Finsupp.domCongr (Place.equivOfRingEquiv (RingEquiv.refl k)
            (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes)) D)) :=
  repartitionQuotientEquivOfRingEquiv (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) D

@[simp]
private theorem repartitionQuotientFunctionFieldEquiv_symm_mk (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) (b : ↥(repartitionSpace k F)) :
    (repartitionQuotientFunctionFieldEquiv hxt D).symm (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk ((repartitionSpaceEquivOfRingEquiv (RingEquiv.refl k)
        (functionFieldEquiv hxt).toRingEquiv
        (id (functionFieldEquiv hxt).commutes)).symm b) :=
  repartitionQuotientEquivOfRingEquiv_symm_mk (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) D b

/-- **First cohomology of `𝒪_{X_F}(D)` as a repartition quotient of `F`**:
`A_F ⧸ (A_F(D) + F) ≃ₗ[k] H¹(X_F, 𝒪_{X_F}(D))`. -/
noncomputable def repartitionQuotientEquivCohomologyOne (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    (↥(repartitionSpace k F) ⧸
        submoduleOfAdeleFiltrationSupDiagonalRepartitions (equivDivisor hxt D)) ≃ₗ[k]
      Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1 :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  (Submodule.quotEquivOfEq _ _ (congrArg submoduleOfAdeleFiltrationSupDiagonalRepartitions
      (domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt D).symm)).trans <|
    (repartitionQuotientFunctionFieldEquiv hxt _).symm.trans
      (SchemeWeilDivisor.repartitionQuotientEquivCohomologyOne
        (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
        (isFunctionField_functionField hxt) D)

/-- `repartitionQuotientEquivCohomologyOne` sends the class of `a ∈ A_F` to
`repartitionToCohomologyOne hxt D a`. -/
@[simp]
theorem repartitionQuotientEquivCohomologyOne_mk (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) (a : ↥(repartitionSpace k F)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    repartitionQuotientEquivCohomologyOne hxt D (Submodule.Quotient.mk a) =
      repartitionToCohomologyOne hxt D a := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  simp only [repartitionQuotientEquivCohomologyOne, LinearEquiv.trans_apply,
    Submodule.quotEquivOfEq_mk, repartitionQuotientFunctionFieldEquiv_symm_mk,
    SchemeWeilDivisor.repartitionQuotientEquivCohomologyOne_mk, repartitionToCohomologyOne_apply]

/-- The kernel of `repartitionToCohomologyOne hxt D` is `(A_F(equivDivisor hxt D) + F) ∩ A_F`. -/
theorem ker_repartitionToCohomologyOne (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    LinearMap.ker (repartitionToCohomologyOne hxt D) =
      submoduleOfAdeleFiltrationSupDiagonalRepartitions (equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  ext a
  rw [LinearMap.mem_ker, ← repartitionQuotientEquivCohomologyOne_mk,
    map_eq_zero_iff _ (repartitionQuotientEquivCohomologyOne hxt D).injective,
    Submodule.Quotient.mk_eq_zero]

private noncomputable def weilDifferentialFiltrationFunctionFieldEquiv (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) :
    ↥(weilDifferentialFiltration D) ≃ₗ[k]
      ↥(weilDifferentialFiltration (Finsupp.domCongr
        (Place.equivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
          (id (functionFieldEquiv hxt).commutes)) D)) :=
  weilDifferentialFiltrationEquivOfRingEquiv (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) D

@[simp]
private theorem coe_weilDifferentialFiltrationFunctionFieldEquiv_apply (hxt : Transcendental k x)
    (D : Divisor k (twoChartModel hF hx).functionField) (ω : ↥(weilDifferentialFiltration D)) :
    (weilDifferentialFiltrationFunctionFieldEquiv hxt D ω :
        Module.Dual k ↥(repartitionSpace k F)) =
      repartitionDualEquivOfRingEquiv (RingEquiv.refl k)
        (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) ω :=
  coe_weilDifferentialFiltrationEquivOfRingEquiv_apply (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) D ω

/-- **The dual of `H¹(X_F, 𝒪_{X_F}(D))` is the space `Ω_F(D)` of Weil differentials of `F` bounded
by `D`.** No exact-constant assumption is needed. -/
noncomputable def cohomologyOneDualEquivWeilDifferentialFiltration (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Module.Dual k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) ≃ₗ[k]
      ↥(weilDifferentialFiltration (equivDivisor hxt D)) :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  (SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration
      (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
      (isFunctionField_functionField hxt) D).trans <|
    (weilDifferentialFiltrationFunctionFieldEquiv hxt _).trans (LinearEquiv.ofEq _ _
      (congrArg weilDifferentialFiltration
        (domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt D)))

/-- The Weil differential on `F` attached to a linear form `φ` on `H¹(X_F, 𝒪_{X_F}(D))` evaluates a
repartition `a ∈ A_F` by applying `φ` to `repartitionToCohomologyOne hxt D a`. -/
@[simp]
theorem cohomologyOneDualEquivWeilDifferentialFiltration_apply_apply (hxt : Transcendental k x)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    ∀ (φ : Module.Dual k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1))
      (a : ↥(repartitionSpace k F)),
      (cohomologyOneDualEquivWeilDifferentialFiltration hxt D φ :
          Module.Dual k ↥(repartitionSpace k F)) a =
        φ (repartitionToCohomologyOne hxt D a) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  intro φ a
  simp only [cohomologyOneDualEquivWeilDifferentialFiltration, LinearEquiv.trans_apply,
    LinearEquiv.coe_ofEq_apply, coe_weilDifferentialFiltrationFunctionFieldEquiv_apply,
    repartitionDualEquivOfRingEquiv_apply_apply, RingEquiv.refl_apply,
    SchemeWeilDivisor.cohomologyOneDualEquivWeilDifferentialFiltration_apply_apply,
    repartitionToCohomologyOne_apply]

/-! ### Exact constant field: `h¹ = i(D) = ℓ(W - D)`, Riemann–Roch, and Serre duality -/

/-- **`dim_k H¹(X_F, 𝒪_{X_F}(D)) = i(D)`**: when `k` is integrally closed in `F`, the first
cohomology dimension of `𝒪_{X_F}(D)` equals the index of specialty of `equivDivisor hxt D`. -/
theorem finrank_cohomology_one_sheaf_eq_indexOfSpecialty (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    (finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) : ℤ) =
      Divisor.indexOfSpecialty (equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  rw [← (repartitionQuotientEquivCohomologyOne hxt D).finrank_eq,
    submoduleOfAdeleFiltrationSupDiagonalRepartitions_eq_submoduleOf,
    finrank_quotient_repartitionSpace hF hk]

/-- **`dim_k H¹(X_F, 𝒪_{X_F}(D)) = ℓ(W - D)`** for every canonical divisor `W` of `F`. -/
theorem finrank_cohomology_one_sheaf_eq_dim_sub (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) {W : Divisor k F}
    (hW : (Place.orderSystem hF).divisorClass W = canonicalClass hF hk)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) =
      Divisor.dim (W - equivDivisor hxt D) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  obtain ⟨ω, -, -, hgreat⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass hF hk hW
  have := SchemeWeilDivisor.finiteDimensional_cohomology_one_sheaf_of_isFunctionField
    (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
    (isFunctionField_functionField hxt) D
  rw [← Subspace.dual_finrank_eq,
    (cohomologyOneDualEquivWeilDifferentialFiltration hxt D).finrank_eq,
    ← dim_sub_eq_finrank_weilDifferentialFiltration hF hk hgreat]

/-- **Serre duality on `X_F`, in dimensions**: for every divisor `K` on `X_F` whose image in `F`
represents `canonicalClass hF hk`, `dim_k H¹(X_F, 𝒪(D)) = dim_k H⁰(X_F, 𝒪(K - D))`. -/
theorem finrank_cohomology_one_sheaf_eq_finrank_cohomology_zero_sheaf_sub
    (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F)
    {K : SchemeWeilDivisor (twoChartModel hF hx)}
    (hK : (Place.orderSystem hF).divisorClass (equivDivisor hxt K) = canonicalClass hF hk)
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) =
      finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf (K - D)) 0) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  refine SchemeWeilDivisor.finrank_cohomology_one_sheaf_eq_finrank_cohomology_zero_sheaf_sub
    (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
    (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk) ?_ D
  apply (Divisor.classGroupEquivOfRingEquiv (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes)
    (isFunctionField_functionField hxt) hF).injective
  rw [Divisor.classGroupEquivOfRingEquiv_divisorClass,
    domCongr_equivOfRingEquiv_equivFunctionFieldDivisor,
    Divisor.classGroupEquivOfRingEquiv_canonicalClass]
  exact hK

private noncomputable def repartitionDualFunctionFieldEquiv (hxt : Transcendental k x) :
    Module.Dual k ↥(repartitionSpace k (twoChartModel hF hx).functionField) ≃ₗ[k]
      Module.Dual k ↥(repartitionSpace k F) :=
  repartitionDualEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
    (id (functionFieldEquiv hxt).commutes)

private theorem repartitionDualFunctionFieldEquiv_apply (hxt : Transcendental k x)
    (ω : Module.Dual k ↥(repartitionSpace k (twoChartModel hF hx).functionField)) :
    repartitionDualFunctionFieldEquiv hxt ω =
      repartitionDualEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
        (id (functionFieldEquiv hxt).commutes) ω :=
  (rfl)

private theorem repartitionDualFunctionFieldEquiv_symm_apply_apply (hxt : Transcendental k x)
    (η : Module.Dual k ↥(repartitionSpace k F))
    (a : ↥(repartitionSpace k (twoChartModel hF hx).functionField)) :
    (repartitionDualFunctionFieldEquiv hxt).symm η a =
      η (repartitionSpaceEquivOfRingEquiv (RingEquiv.refl k)
        (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) a) :=
  repartitionDualEquivOfRingEquiv_symm_apply_apply (RingEquiv.refl k)
    (functionFieldEquiv hxt).toRingEquiv (id (functionFieldEquiv hxt).commutes) η a

/-- **Serre duality on the two-chart model.** Let `ω` be a nonzero Weil differential of `F` and `K`
the Weil divisor on `X_F` corresponding to `(ω)`. For every Weil divisor `D` on `X_F`, the dual of
`H¹(X_F, 𝒪(D))` is `k`-linearly isomorphic to `H⁰(X_F, 𝒪(K - D))`; a class in `H⁰(X_F, 𝒪(K - D))`
with underlying function `f ∈ F` pairs with the class of `a ∈ A_F` to `ω(f · a)`
(`twoChartModel.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne`). -/
noncomputable def cohomologyOneDualEquivCohomologyZero (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) {ω : Module.Dual k ↥(repartitionSpace k F)}
    {K : SchemeWeilDivisor (twoChartModel hF hx)}
    (hK : IsGreatest {E : Divisor k F | ω ∈ weilDifferentialFiltration E} (equivDivisor hxt K))
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Module.Dual k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) ≃ₗ[k]
      Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf (K - D)) 0 :=
  haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  haveI := isNoetherian (hF := hF) (hx := hx) hxt
  SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero (valuativeCriterion_existence hF hx)
    (coheight_le_one hxt) (isFunctionField_functionField hxt)
    (isIntegrallyClosedIn_functionField hxt hk)
    ((isGreatest_weilDifferentialFiltration_repartitionDualEquivOfRingEquiv_iff
      (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes)
      ((repartitionDualFunctionFieldEquiv hxt).symm ω) _).mp (by
        simpa only [← repartitionDualFunctionFieldEquiv_apply, LinearEquiv.apply_symm_apply,
          domCongr_equivOfRingEquiv_equivFunctionFieldDivisor] using hK))
    D

/-- **The Serre duality pairing on `X_F` in terms of `F`**: a class `s ∈ H⁰(X_F, 𝒪(K - D))` pairs
with the cohomology class of a repartition `a ∈ A_F` to `ω(f · a)`, where `f ∈ F` is the function
attached to `s` by `cohomologyZeroEquivRiemannRochSpace`. -/
theorem cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne
    (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F)
    {ω : Module.Dual k ↥(repartitionSpace k F)}
    {K : SchemeWeilDivisor (twoChartModel hF hx)}
    (hK : IsGreatest {E : Divisor k F | ω ∈ weilDifferentialFiltration E} (equivDivisor hxt K))
    (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    ∀ (s : Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf (K - D)) 0)
      (a : ↥(repartitionSpace k F)),
      (cohomologyOneDualEquivCohomologyZero hxt hk hK D).symm s
          (repartitionToCohomologyOne hxt D a) =
        ω (repartitionMul hF (cohomologyZeroEquivRiemannRochSpace hxt (K - D) s : F) a) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  intro s a
  rw [cohomologyOneDualEquivCohomologyZero, repartitionToCohomologyOne_apply,
    SchemeWeilDivisor.cohomologyOneDualEquivCohomologyZero_symm_apply_repartitionToCohomologyOne,
    repartitionDualFunctionFieldEquiv_symm_apply_apply,
    repartitionSpaceEquivOfRingEquiv_repartitionMul _ _ _ _ hF]
  exact congrArg ω (congrArg₂ (fun z b ↦ repartitionMul hF z b)
    (coe_cohomologyZeroEquivRiemannRochSpace_apply hxt (K - D) s).symm
    (LinearEquiv.apply_symm_apply _ a))

/-- **The Riemann–Roch theorem on `X_F` in Euler-characteristic form**: when `k` is integrally
closed in `F`, `χ(𝒪_{X_F}(D)) = deg D + 1 - g(F)`. -/
theorem eulerCharBelow_sheaf_eq_degree_add_one_sub_genus (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    Scheme.Modules.eulerCharBelow k (twoChartModel hF hx) (SchemeWeilDivisor.sheaf D) 2 =
      Divisor.degree (equivDivisor hxt D) + 1 - genus k F := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  rw [Scheme.Modules.eulerCharBelow_two, finrank_cohomology_zero_sheaf_eq_dim hxt D,
    finrank_cohomology_one_sheaf_eq_indexOfSpecialty hxt hk D, Divisor.indexOfSpecialty_def]
  omega

/-- **The Riemann–Roch theorem on `X_F` in dimension form**: when `k` is integrally closed in `F`,
`dim_k H⁰(X_F, 𝒪(D)) - dim_k H¹(X_F, 𝒪(D)) = deg D + 1 - g(F)`. -/
theorem finrank_cohomology_zero_sheaf_sub_finrank_cohomology_one_sheaf (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) (D : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    (finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 0) : ℤ) -
        finrank k (Scheme.Modules.Cohomology (SchemeWeilDivisor.sheaf D) 1) =
      Divisor.degree (equivDivisor hxt D) + 1 - genus k F := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  rw [← Scheme.Modules.eulerCharBelow_two,
    eulerCharBelow_sheaf_eq_degree_add_one_sub_genus hxt hk D]

/-! ### Canonical bundle and relative differentials `[Ω_{X_F/k}]` -/

/-- **A canonical line bundle on `X_F`**, obtained from `InvertibleSheaf.canonicalBundle` when `k`
is integrally closed in `F`. Its class in `Pic(X_F) ≃+ Cl(F)` is `canonicalClass hF hk`. -/
noncomputable def canonicalBundle (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F) :
    InvertibleSheaf (twoChartModel hF hx) :=
  letI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  letI := isNoetherian (hF := hF) (hx := hx) hxt
  InvertibleSheaf.canonicalBundle (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
    (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk)

/-- A Weil divisor `K` on `X_F` represents the class of `canonicalBundle` if and only if
`equivDivisor hxt K` represents `canonicalClass hF hk` in `Cl(F)`. -/
@[simp]
theorem mk_canonicalBundle_eq_iff (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F)
    (K : SchemeWeilDivisor (twoChartModel hF hx)) :
    haveI := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
    haveI := isNoetherian (hF := hF) (hx := hx) hxt
    LineBundleClass.mk (canonicalBundle hxt hk) =
        SchemeWeilDivisor.toLineBundleClass (coheight_le_one hxt) K ↔
      (Place.orderSystem hF).divisorClass (equivDivisor hxt K) = canonicalClass hF hk := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  rw [canonicalBundle, InvertibleSheaf.mk_canonicalBundle_eq_iff
      (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
      (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk) K,
    ← (Divisor.classGroupEquivOfRingEquiv (RingEquiv.refl k) (functionFieldEquiv hxt).toRingEquiv
      (id (functionFieldEquiv hxt).commutes)
      (isFunctionField_functionField hxt) hF).injective.eq_iff,
    Divisor.classGroupEquivOfRingEquiv_divisorClass,
    domCongr_equivOfRingEquiv_equivFunctionFieldDivisor hxt K,
    Divisor.classGroupEquivOfRingEquiv_canonicalClass]

/-- **Under `Pic(X_F) ≃+ Cl(F)`, the canonical bundle maps to `canonicalClass hF hk`.** -/
@[simp]
theorem picardEquivClassGroup_canonicalBundle (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    picardEquivClassGroup hxt
        (Additive.ofMul (LineBundleClass.mk (canonicalBundle (hF := hF) (hx := hx) hxt hk))) =
      canonicalClass hF hk := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  obtain ⟨W, hW⟩ := (Place.orderSystem hF).divisorClass_surjective (canonicalClass hF hk)
  have hmk : LineBundleClass.mk (canonicalBundle (hF := hF) (hx := hx) hxt hk) =
      SchemeWeilDivisor.toLineBundleClass (coheight_le_one hxt) ((equivDivisor hxt).symm W) := by
    rw [mk_canonicalBundle_eq_iff hxt hk, AddEquiv.apply_symm_apply, hW]
  rw [hmk, picardEquivClassGroup_toLineBundleClass, AddEquiv.apply_symm_apply, hW]

/-- **The canonical bundle on `X_F` has Euler-characteristic degree `2g - 2`.** -/
@[simp]
theorem eulerDegree_canonicalBundle (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F) :
    (canonicalBundle (hF := hF) (hx := hx) hxt hk).eulerDegree k = 2 * genus k F - 2 := by
  rw [← LineBundleClass.eulerDegree_mk,
    ← toMul_ofMul (LineBundleClass.mk (canonicalBundle (hF := hF) (hx := hx) hxt hk)),
    ← degreeClass_picardEquivClassGroup hxt, picardEquivClassGroup_canonicalBundle,
    degreeClass_canonicalClass]

/-- **`dim_k H⁰(X_F, ω_{X_F}) = g(F)`.** -/
theorem finrank_cohomology_zero_canonicalBundle (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    finrank k (Scheme.Modules.Cohomology (canonicalBundle (hF := hF) (hx := hx) hxt hk).obj 0) =
      genus k F := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  let _ := isProper (hF := hF) (hx := hx) hxt
  rw [← genus_eq_genus hxt hk]
  exact InvertibleSheaf.finrank_cohomology_zero_eq_genus_of_mk_eq_canonicalBundle
    (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
    (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk) _ rfl

/-- **`dim_k H¹(X_F, ω_{X_F}) = 1`.** -/
@[simp]
theorem finrank_cohomology_one_canonicalBundle (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    finrank k (Scheme.Modules.Cohomology (canonicalBundle (hF := hF) (hx := hx) hxt hk).obj 1) =
      1 := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  exact InvertibleSheaf.finrank_cohomology_one_eq_one_of_mk_eq_canonicalBundle
    (valuativeCriterion_existence hF hx) (coheight_le_one hxt)
    (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk) _ rfl

section InvertibleDifferentials

variable [hinv : SheafOfModules.isInvertible (twoChartModel hF hx)
  ((twoChartModel hF hx).relativeDifferentials k)]

/-- When `Ω_{X_F/k}` is invertible and `k` is integrally closed in `F`, `Ω_{X_F/k}` is isomorphic
to `twoChartModel.canonicalBundle`. -/
theorem nonempty_iso_relativeDifferentials_canonicalBundle (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    Nonempty ((twoChartModel hF hx).relativeDifferentials k ≅
      (canonicalBundle (hF := hF) (hx := hx) hxt hk).obj) := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  exact TauCeti.AlgebraicGeometry.nonempty_iso_relativeDifferentials_canonicalBundle
    (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk)
    (coheight_le_one hxt) (valuativeCriterion_existence hF hx)

/-- **When `Ω_{X_F/k}` is invertible, its class in `Pic(X_F) ≃+ Cl(F)` is `canonicalClass hF hk`.**
-/
@[simp]
theorem picardEquivClassGroup_relativeDifferentials_of_isInvertible (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    picardEquivClassGroup hxt (Additive.ofMul (LineBundleClass.mk
        (⟨(twoChartModel hF hx).relativeDifferentials k, hinv⟩ :
          InvertibleSheaf (twoChartModel hF hx)))) =
      canonicalClass hF hk := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle (hF := hF) (hx := hx) hxt hk
  have hmk : LineBundleClass.mk
      (⟨(twoChartModel hF hx).relativeDifferentials k, hinv⟩ :
        InvertibleSheaf (twoChartModel hF hx)) =
      LineBundleClass.mk (canonicalBundle (hF := hF) (hx := hx) hxt hk) :=
    LineBundleClass.mk_eq_mk_iff.mpr ⟨e⟩
  rw [hmk, picardEquivClassGroup_canonicalBundle]

/-- **When `Ω_{X_F/k}` is invertible, its Euler-characteristic degree is `2g - 2`.** -/
theorem eulerDegree_relativeDifferentials_of_isInvertible (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    InvertibleSheaf.eulerDegree k
        (⟨(twoChartModel hF hx).relativeDifferentials k, hinv⟩ :
          InvertibleSheaf (twoChartModel hF hx)) =
      2 * genus k F - 2 := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle (hF := hF) (hx := hx) hxt hk
  rw [InvertibleSheaf.eulerDegree_congr k e, eulerDegree_canonicalBundle hxt hk]

/-- **When `Ω_{X_F/k}` is invertible, `dim_k H⁰(X_F, Ω_{X_F/k}) = g(F)`.** -/
theorem finrank_cohomology_zero_relativeDifferentials (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    finrank k (Scheme.Modules.Cohomology ((twoChartModel hF hx).relativeDifferentials k) 0) =
      genus k F := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle (hF := hF) (hx := hx) hxt hk
  rw [Scheme.Modules.finrank_cohomology_congr k e 0, finrank_cohomology_zero_canonicalBundle hxt hk]

/-- **When `Ω_{X_F/k}` is invertible, `dim_k H¹(X_F, Ω_{X_F/k}) = 1`.** -/
theorem finrank_cohomology_one_relativeDifferentials (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F) :
    finrank k (Scheme.Modules.Cohomology ((twoChartModel hF hx).relativeDifferentials k) 1) =
      1 := by
  obtain ⟨e⟩ := nonempty_iso_relativeDifferentials_canonicalBundle (hF := hF) (hx := hx) hxt hk
  rw [Scheme.Modules.finrank_cohomology_congr k e 1, finrank_cohomology_one_canonicalBundle hxt hk]

/-- **Line-bundle Riemann–Roch on `X_F` with `Ω_{X_F/k}`**: when `Ω_{X_F/k}` is invertible and `k`
is integrally closed in `F`, every line bundle `L` on `X_F` satisfies
`dim_k H⁰(X_F, L) - dim_k H⁰(X_F, Ω_{X_F/k} ⊗ L⁻¹) = deg L + 1 - g(F)`. -/
theorem finrank_cohomology_zero_sub_finrank_cohomology_zero_differentials_tensor_dual
    (hxt : Transcendental k x) (hk : IsIntegrallyClosedIn k F)
    (L : InvertibleSheaf (twoChartModel hF hx)) :
    (finrank k (Scheme.Modules.Cohomology L.obj 0) : ℤ) -
        finrank k (Scheme.Modules.Cohomology
          (InvertibleSheaf.tensorProduct ⟨(twoChartModel hF hx).relativeDifferentials k, hinv⟩
            (InvertibleSheaf.dual L)).obj 0) =
      L.eulerDegree k + 1 - genus k F := by
  let _ := isDiscreteValuationRing_stalk (hF := hF) (hx := hx) hxt
  let _ := isNoetherian (hF := hF) (hx := hx) hxt
  let _ := isProper (hF := hF) (hx := hx) hxt
  rw [← genus_eq_genus hxt hk]
  exact
    AlgebraicGeometry.finrank_cohomology_zero_sub_finrank_cohomology_zero_differentials_tensor_dual
      (isFunctionField_functionField hxt) (isIntegrallyClosedIn_functionField hxt hk)
      (coheight_le_one hxt) (valuativeCriterion_existence hF hx) L

end InvertibleDifferentials

section Smooth

/-- If `twoChartModel hF hx` is smooth over `Spec k`, it is smooth of relative dimension one. -/
theorem smoothOfRelativeDimension_one (hxt : Transcendental k x)
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))] :
    SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k)) :=
  smoothOfRelativeDimension_of_topologicalKrullDim_eq (twoChartModel hF hx ↘ Spec (.of k))
    (topologicalKrullDim_eq_one hxt)

/-- If `twoChartModel hF hx` is smooth over `Spec k`, its sheaf of relative differentials
`Ω_{X_F/k}` is invertible. -/
theorem isInvertible_relativeDifferentials (hxt : Transcendental k x)
    [Smooth (twoChartModel hF hx ↘ Spec (.of k))] :
    SheafOfModules.isInvertible (twoChartModel hF hx)
      ((twoChartModel hF hx).relativeDifferentials k) :=
  letI := smoothOfRelativeDimension_one (hF := hF) (hx := hx) hxt
  TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials k

/-- **On a smooth two-chart model, `[Ω_{X_F/k}]` maps to `canonicalClass hF hk` under
`Pic(X_F) ≃+ Cl(F)`.** -/
@[simp]
theorem picardEquivClassGroup_relativeDifferentials (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F)
    [SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k))] :
    picardEquivClassGroup hxt (Additive.ofMul (LineBundleClass.mk
        (InvertibleSheaf.relativeDifferentials k (twoChartModel hF hx)))) =
      canonicalClass hF hk := by
  let hinv := TauCeti.AlgebraicGeometry.isInvertible_relativeDifferentials k
    (X := twoChartModel hF hx)
  have hmk : LineBundleClass.mk (InvertibleSheaf.relativeDifferentials k (twoChartModel hF hx)) =
      LineBundleClass.mk (⟨(twoChartModel hF hx).relativeDifferentials k, hinv⟩ :
        InvertibleSheaf (twoChartModel hF hx)) :=
    LineBundleClass.mk_eq_mk_iff.mpr
      ⟨eqToIso (InvertibleSheaf.relativeDifferentials_obj k (twoChartModel hF hx))⟩
  rw [hmk, picardEquivClassGroup_relativeDifferentials_of_isInvertible hxt hk]

/-- **On a smooth two-chart model, `Ω_{X_F/k}` has Euler-characteristic degree `2g - 2`.** -/
@[simp]
theorem eulerDegree_relativeDifferentials (hxt : Transcendental k x)
    (hk : IsIntegrallyClosedIn k F)
    [SmoothOfRelativeDimension 1 (twoChartModel hF hx ↘ Spec (.of k))] :
    (InvertibleSheaf.relativeDifferentials k (twoChartModel hF hx)).eulerDegree k =
      2 * genus k F - 2 := by
  rw [← LineBundleClass.eulerDegree_mk,
    ← toMul_ofMul
      (LineBundleClass.mk (InvertibleSheaf.relativeDifferentials k (twoChartModel hF hx))),
    ← degreeClass_picardEquivClassGroup hxt, picardEquivClassGroup_relativeDifferentials hxt hk,
    degreeClass_canonicalClass]

end Smooth

end TauCeti.AlgebraicGeometry.twoChartModel
