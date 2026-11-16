/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Polynomial.Eisenstein.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import TauCeti.FieldTheory.IntermediateField.Adjoin.EqTop

/-!
# Minimal polynomials, `AdjoinRoot` presentations, and degrees of Eisenstein roots

An Eisenstein polynomial with unit leading coefficient over an integrally closed domain `R` is
associated to the minimal polynomial of any of its roots in a domain algebra with injective
structure map from `R`. Consequently, it generates the evaluation kernel, induces an `AdjoinRoot`
isomorphism whenever the root generates the algebra over `R`, remains irreducible over the fraction
field `K = Frac R`, and determines the field degree `[K(α) : K] = deg f`.

## Main definitions and results

* `Polynomial.IsEisensteinAt.isUnit_leadingCoeff` and
  `Polynomial.IsEisensteinAt.isIntegral_of_aeval_eq_zero`: over a local ring, a polynomial that is
  Eisenstein at the maximal ideal has unit leading coefficient, so any root of it is integral.
* `Polynomial.IsEisensteinAt.associated_minpoly` and
  `Polynomial.IsEisensteinAt.minpoly_eq_of_monic`: identify the minimal polynomial up to a unit
  (and on the nose when `f` is monic).
* `Polynomial.IsEisensteinAt.ker_aeval_eq_span` and
  `Polynomial.IsEisensteinAt.adjoinRootAlgEquiv`: evaluation kernel `Ideal.span {f}` and canonical
  isomorphism `AdjoinRoot f ≃ₐ[R] S` when `x` generates `S` over `R`.
* `Polynomial.IsEisensteinAt.irreducible_map_fractionRing`: `f.map (algebraMap R K)` is irreducible
  over `K = Frac R`.
* `Polynomial.IsEisensteinAt.finrank_adjoin_eq_natDegree`,
  `Polynomial.IsEisensteinAt.finrank_eq_natDegree`, and
  `Polynomial.IsEisensteinAt.finrank_eq_natDegree_of_adjoin_eq_top`: field degree formulas over
  `K = Frac R`.
-/

public section

open IntermediateField

namespace Polynomial.IsEisensteinAt

/-- Over a local ring, a polynomial that is Eisenstein at the maximal ideal has unit leading
coefficient. -/
theorem isUnit_leadingCoeff {R : Type*} [CommSemiring R] [IsLocalRing R] {f : R[X]}
    (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R)) : IsUnit f.leadingCoeff :=
  IsLocalRing.notMem_maximalIdeal.mp hf.leading

private theorem isIntegral_of_isUnit_leadingCoeff {R S : Type*} [CommRing R] [Ring S] [Algebra R S]
    {f : R[X]} {x : S} (hlc : IsUnit f.leadingCoeff) (hx : aeval x f = 0) : IsIntegral R x :=
  ⟨hlc.unit⁻¹ • f, monic_of_isUnit_leadingCoeff_inv_smul hlc, by
    rw [← aeval_def, Units.smul_def, smul_eq_C_mul, map_mul, hx, mul_zero]⟩

private theorem associated_unit_smul {R : Type*} [CommSemiring R] (u : Rˣ) (f : R[X]) :
    Associated (u • f) f := by
  rw [Units.smul_def, smul_eq_C_mul]
  exact associated_unit_mul_left f _ (isUnit_C.mpr u.isUnit)

/-- Any root of a polynomial that is Eisenstein at the maximal ideal of a local ring is integral
over that ring. -/
theorem isIntegral_of_aeval_eq_zero {R S : Type*} [CommRing R] [IsLocalRing R] [Ring S]
    [Algebra R S] {f : R[X]} {x : S} (hf : f.IsEisensteinAt (IsLocalRing.maximalIdeal R))
    (hx : aeval x f = 0) : IsIntegral R x :=
  isIntegral_of_isUnit_leadingCoeff hf.isUnit_leadingCoeff hx

private theorem irreducible_of_isUnit_leadingCoeff {R : Type*} [CommRing R] [IsDomain R]
    {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} (hf : f.IsEisensteinAt 𝓟)
    (hlc : IsUnit f.leadingCoeff) (hdeg : 0 < f.natDegree) : Irreducible f :=
  hf.irreducible inferInstance
    (isPrimitive_iff_isUnit_of_C_dvd.2 fun r hr ↦
      isUnit_of_dvd_unit (by simpa using (C_dvd_iff_dvd_coeff r f).1 hr f.natDegree) hlc) hdeg

section IntegrallyClosed

variable {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [CommRing S] [IsDomain S] [Algebra R S]

/-- The minimal polynomial of a root of an Eisenstein polynomial `f` with unit leading coefficient
over an integrally closed domain is associated to `f`. -/
theorem associated_minpoly [Module.IsTorsionFree R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {ξ : S}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hroot : (f.map (algebraMap R S)).IsRoot ξ) : Associated (minpoly R ξ) f := by
  have haeval : aeval ξ f = 0 := by simpa [aeval_def] using hroot
  have hdeg : 0 < f.natDegree :=
    natDegree_pos_of_aeval_root (leadingCoeff_ne_zero.1 hlc.ne_zero) haeval
      fun _ ↦ (FaithfulSMul.algebraMap_eq_zero_iff R S).1
  have hfirr : Irreducible f := hf.irreducible_of_isUnit_leadingCoeff hlc hdeg
  have hξ : IsIntegral R ξ :=
    (minpoly.IsIntegrallyClosed.isIntegral_iff_isUnit_leadingCoeff hfirr haeval).2 hlc
  exact (minpoly.irreducible hξ).associated_of_dvd hfirr (minpoly.isIntegrallyClosed_dvd hξ haeval)

/-- If `f` is monic and Eisenstein at a prime ideal of an integrally closed domain `R`, then `f`
is the minimal polynomial over `R` of any of its roots in a domain `S` with injective structure map
from `R`. -/
theorem minpoly_eq_of_monic [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {ξ : S}
    (hf : f.IsEisensteinAt 𝓟) (hmo : f.Monic) (hξ : aeval ξ f = 0) :
    minpoly R ξ = f := by
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R S)
  have hroot : (f.map (algebraMap R S)).IsRoot ξ := by rwa [IsRoot.def, eval_map_algebraMap]
  exact eq_of_monic_of_associated (minpoly.monic ⟨f, hmo, hξ⟩) hmo
    (hf.associated_minpoly (hmo.leadingCoeff.symm ▸ isUnit_one) hroot)

/-- Over an integrally closed domain `R`, the kernel of `aeval x : R[X] →ₐ[R] S` at a root `x` of
an Eisenstein polynomial `f` with unit leading coefficient in a domain `S` with injective structure
map from `R` is `Ideal.span {f}`. -/
theorem ker_aeval_eq_span [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]} {x : S}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff) (hx : aeval x f = 0) :
    RingHom.ker (aeval x : R[X] →ₐ[R] S) = Ideal.span {f} := by
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R S)
  have hroot : (f.map (algebraMap R S)).IsRoot x := by rwa [IsRoot.def, eval_map_algebraMap]
  have hx_int : IsIntegral R x := isIntegral_of_isUnit_leadingCoeff hlc hx
  ext p
  rw [RingHom.mem_ker, minpoly.isIntegrallyClosed_dvd_iff hx_int, ← Ideal.mem_span_singleton,
    Ideal.span_singleton_eq_span_singleton.mpr (hf.associated_minpoly hlc hroot)]

/-- Canonical `R`-algebra isomorphism `AdjoinRoot f ≃ₐ[R] S` sending `AdjoinRoot.root f` to `x`,
for an Eisenstein polynomial `f` with unit leading coefficient over an integrally closed domain `R`
and a domain `S` with injective structure map from `R` generated over `R` by a root `x` of `f`. -/
noncomputable def adjoinRootAlgEquiv [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    {x : S} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) :
    AdjoinRoot f ≃ₐ[R] S :=
  have : Module.IsTorsionFree R S :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R S)
  have hroot : (f.map (algebraMap R S)).IsRoot x := by rwa [IsRoot.def, eval_map_algebraMap]
  have hx_int : IsIntegral R x := isIntegral_of_isUnit_leadingCoeff hlc hx
  ((AdjoinRoot.algEquivOfAssociated R f (minpoly R x)
      (hf.associated_minpoly hlc hroot).symm).trans (minpoly.equivAdjoin hx_int)).trans
    ((Subalgebra.equivOfEq _ _ hadj).trans Subalgebra.topEquiv)

/-- `adjoinRootAlgEquiv` sends `AdjoinRoot.root f` to `x`. -/
@[simp]
theorem adjoinRootAlgEquiv_apply_root [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    {x : S} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) :
    hf.adjoinRootAlgEquiv hlc hx hadj (AdjoinRoot.root f) = x := by
  simp [adjoinRootAlgEquiv]

/-- `adjoinRootAlgEquiv` evaluates `AdjoinRoot.mk f p` to `aeval x p`. -/
@[simp]
theorem adjoinRootAlgEquiv_apply_mk [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    {x : S} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) (p : R[X]) :
    hf.adjoinRootAlgEquiv hlc hx hadj (AdjoinRoot.mk f p) = aeval x p := by
  rw [← AdjoinRoot.aeval_eq, ← aeval_algHom_apply, adjoinRootAlgEquiv_apply_root]

/-- Inverse of `adjoinRootAlgEquiv` on `aeval x p`. -/
@[simp]
theorem adjoinRootAlgEquiv_symm_apply_aeval [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime]
    {f : R[X]} {x : S} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) (p : R[X]) :
    (hf.adjoinRootAlgEquiv hlc hx hadj).symm (aeval x p) = AdjoinRoot.mk f p := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootAlgEquiv_apply_mk]

/-- Inverse of `adjoinRootAlgEquiv` on the generator `x`. -/
@[simp]
theorem adjoinRootAlgEquiv_symm_apply_gen [FaithfulSMul R S] {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    {x : S} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) :
    (hf.adjoinRootAlgEquiv hlc hx hadj).symm x = AdjoinRoot.root f := by
  rw [AlgEquiv.symm_apply_eq, adjoinRootAlgEquiv_apply_root]

/-- Over an integrally closed domain `R`, an Eisenstein polynomial `f : R[X]` of positive degree
with unit leading coefficient remains irreducible over `K = Frac R`. -/
theorem irreducible_map_fractionRing {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff) (K : Type*) [Field K] [Algebra R K]
    [IsFractionRing R K] (hdeg : 0 < f.natDegree) :
    Irreducible (f.map (algebraMap R K)) := by
  let g : R[X] := hlc.unit⁻¹ • f
  have hg_mo : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hlc
  have hassoc : Associated g f := associated_unit_smul hlc.unit⁻¹ f
  have hmap_irr : Irreducible (g.map (algebraMap R K)) :=
    (hg_mo.irreducible_iff_irreducible_map_fraction_map (K := K)).mp
      (hassoc.symm.irreducible (hf.irreducible_of_isUnit_leadingCoeff hlc hdeg))
  exact (hassoc.map (Polynomial.mapRingHom (algebraMap R K))).irreducible hmap_irr

/-- If `α` is a root of an Eisenstein polynomial `f : R[X]` with unit leading coefficient in a
field extension `E` of `K = Frac R`, then `[K⟮α⟯ : K] = f.natDegree`. -/
theorem finrank_adjoin_eq_natDegree {K E : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E] {𝓟 : Ideal R} [𝓟.IsPrime]
    {f : R[X]} {α : E} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hα : aeval α f = 0) :
    Module.finrank K K⟮α⟯ = f.natDegree := by
  have : FaithfulSMul R E := FaithfulSMul.trans R K E
  have : Module.IsTorsionFree R E :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr (FaithfulSMul.algebraMap_injective R E)
  have hroot : (f.map (algebraMap R E)).IsRoot α := by rwa [IsRoot.def, eval_map_algebraMap]
  let g : R[X] := hlc.unit⁻¹ • f
  have hg_mo : g.Monic := monic_of_isUnit_leadingCoeff_inv_smul hlc
  have hα_int : IsIntegral R α := isIntegral_of_isUnit_leadingCoeff hlc hα
  have hassoc : Associated (minpoly R α) g :=
    (hf.associated_minpoly hlc hroot).trans (associated_unit_smul hlc.unit⁻¹ f).symm
  have hmin : minpoly R α = g := eq_of_monic_of_associated (minpoly.monic hα_int) hg_mo hassoc
  rw [IntermediateField.adjoin.finrank hα_int.tower_top,
    minpoly.isIntegrallyClosed_eq_field_fractions' K hα_int, (minpoly.monic hα_int).natDegree_map,
    hmin, natDegree_smul_of_smul_regular f (IsSMulRegular.all _)]

/-- If `E = K⟮α⟯` is generated over `K = Frac R` by a root `α` of an Eisenstein polynomial
`f : R[X]` with unit leading coefficient, then `[E : K] = f.natDegree`. -/
theorem finrank_eq_natDegree {K E : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    [Field E] [Algebra K E] [Algebra R E] [IsScalarTower R K E] {𝓟 : Ideal R} [𝓟.IsPrime]
    {f : R[X]} {α : E} (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff)
    (hα : aeval α f = 0) (hgen : K⟮α⟯ = ⊤) :
    Module.finrank K E = f.natDegree := by
  rw [← IntermediateField.finrank_top', ← hgen, hf.finrank_adjoin_eq_natDegree hlc hα]

/-- If `E / K` is algebraic over `K = Frac R` and `integralClosure R E = R[x]` for a root `x` of an
Eisenstein polynomial `f : R[X]` with unit leading coefficient, then `[E : K] = f.natDegree`. -/
theorem finrank_eq_natDegree_of_adjoin_eq_top {𝓟 : Ideal R} [𝓟.IsPrime] {f : R[X]}
    (hf : f.IsEisensteinAt 𝓟) (hlc : IsUnit f.leadingCoeff) (K : Type*) [Field K]
    [Algebra R K] [IsFractionRing R K] {E : Type*} [Field E] [Algebra R E] [Algebra K E]
    [IsScalarTower R K E] [Algebra.IsAlgebraic K E] {x : integralClosure R E}
    (hx : aeval x f = 0) (hadj : Algebra.adjoin R {x} = ⊤) :
    Module.finrank K E = f.natDegree := by
  have hxE : aeval (x : E) f = 0 := by
    rw [← aeval_subalgebra_coe f (integralClosure R E) x, hx, ZeroMemClass.coe_zero]
  exact hf.finrank_eq_natDegree hlc hxE
    (TauCeti.IntermediateField.adjoin_coe_eq_top_of_algebra_adjoin_eq_top hadj)

end IntegrallyClosed

end Polynomial.IsEisensteinAt
