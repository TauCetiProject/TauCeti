/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Unramified
public import TauCeti.NumberTheory.NumberField.Global.Places.Completion
public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import TauCeti.NumberTheory.NumberField.GaloisCohomology.FiniteRamification

/-!
# Restricted localization for an isogeny

For an isogeny `φ` over a number field `K`, the diagonal restriction map from global kernel
cohomology takes values in the restricted product of local kernel cohomology over every place
of `K`, relative to the local Kummer conditions. Indeed, a global class is unramified at all but
finitely many finite places, and these conditions agree with unramified cohomology away from a
finite set. The infinite places form a finite set as well.

`restrictedKerLocalization` constructs this diagonal homomorphism with the caller's embeddings
of separable closures. Its target uses the canonical local coefficient kernels, so the carrier is
independent of those embeddings. The Selmer group is the pullback of
the subgroup satisfying the local conditions at every place.
This is the restricted-product localization used in the global duality approach to Cassels'
isogeny formula.

## References

* J. S. Milne, *Arithmetic Duality Theorems*, 2nd ed., Chapter I, §4.
* J. W. S. Cassels, *Arithmetic on curves of genus 1. VIII. On conjectures of Birch and
  Swinnerton-Dyer*, J. Reine Angew. Math. 217 (1965), 180–199.
-/

public noncomputable section

namespace TauCeti.Isogeny

open WeierstrassCurve TauCeti.ContCohomology GlobalNumberFields IsDedekindDomain
open Hom (ofIsogeny)
open scoped _root_.NumberField RestrictedProduct

variable {K : Type*} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)

private theorem eventually_kerRes_mem_unramifiedKerCohomology
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    ∀ᶠ v in Filter.cofinite,
      φ.kerRes (τf v) c ∈ (φ.baseChange (v.adicCompletion K)).unramifiedKerCohomology := by
  simpa only [unramifiedKerCohomology_eq_unramifiedH1, kerRes_eq_explicitMap1] using
    (eventually_explicitMap1_mem_unramifiedH1
      (M := (ofIsogeny φ).KerCoeff)
      (N := fun v ↦ (ofIsogeny (φ.baseChange (v.adicCompletion K))).KerCoeff)
      τf (fun v ↦ φ.kerCoeffBaseChange (τf v))
      (fun _ ↦ continuous_of_discreteTopology)
      (fun v ↦ φ.kerCoeffBaseChange_smul (τf v)) c)

private theorem eventually_kerRes_mem_finiteLocalCondition
    (τf : ∀ v : HeightOneSpectrum (𝓞 K),
      SeparableClosure K →ₐ[K] SeparableClosure (v.adicCompletion K))
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    ∀ᶠ v in Filter.cofinite, φ.kerRes (τf v) c ∈ (φ.selmerStructure τf).localCondition v := by
  have hcond := φ.eventually_localCondition_selmerStructure_eq_unramifiedKerCohomology
    (_root_.NumberField.RingOfIntegers K) τf (Nat.cast_ne_zero.mpr φ.degree_ne_zero)
  filter_upwards [eventually_kerRes_mem_unramifiedKerCohomology φ τf c, hcond] with v hv hvc
  rw [hvc]
  exact hv

variable (τ : ∀ v : GlobalNumberFields.Place K,
  SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

/-- Every global kernel cohomology class satisfies the local Kummer condition at almost every
place of a number field. -/
theorem eventually_kerRes_mem_localCondition
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    ∀ᶠ v in Filter.cofinite, φ.kerRes (τ v) c ∈ (φ.selmerStructure τ).localCondition v := by
  rw [Filter.eventually_cofinite]
  apply Set.finite_preimage_inl_and_inr.mp
  refine ⟨Filter.eventually_cofinite.mp ?_, Set.toFinite _⟩
  have h := eventually_kerRes_mem_finiteLocalCondition φ (fun v ↦ τ (Sum.inl v)) c
  filter_upwards [h] with v hv
  rw [selmerStructure_localCondition] at hv ⊢
  exact hv

/-- The diagonal localization of global kernel cohomology into the all-place restricted
product relative to the local Kummer conditions. -/
def restrictedKerLocalization :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      Πʳ v : GlobalNumberFields.Place K,
        [H1 (AbsoluteGaloisGroup v.Completion) (ofIsogeny (φ.baseChange v.Completion)).KerCoeff,
          (explicitCoeff1 _ _ (ofIsogeny (φ.baseChange v.Completion)).kerCoeffIncl
            continuous_of_discreteTopology).ker] where
  toFun c := RestrictedProduct.mk (fun v ↦ φ.kerRes (τ v) c)
    (by simpa only [selmerStructure_localCondition, SetLike.mem_coe] using
      φ.eventually_kerRes_mem_localCondition τ c)
  map_zero' := by
    apply RestrictedProduct.ext
    intro v
    exact map_zero (φ.kerRes (τ v))
  map_add' c d := by
    apply RestrictedProduct.ext
    intro v
    exact map_add (φ.kerRes (τ v)) c d

/-- A coordinate of restricted localization is the corresponding kernel restriction. -/
@[simp]
theorem restrictedKerLocalization_apply
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) (v : GlobalNumberFields.Place K) :
    φ.restrictedKerLocalization τ c v = φ.kerRes (τ v) c := by
  simp only [restrictedKerLocalization, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    RestrictedProduct.mk_apply]

/-- The diagonal localization vanishes exactly when every local restriction vanishes. -/
theorem restrictedKerLocalization_eq_zero_iff
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    φ.restrictedKerLocalization τ c = 0 ↔ ∀ v, φ.kerRes (τ v) c = 0 := by
  constructor
  · intro h v
    exact congrArg (fun x ↦ x v) h
  · intro h
    apply RestrictedProduct.ext
    intro v
    simpa only [restrictedKerLocalization_apply, RestrictedProduct.zero_apply] using h v

/-- The Selmer group is the pullback, along restricted localization, of the subgroup satisfying
the local conditions at every place. -/
theorem selmerGroup_eq_comap_restrictedKerLocalization :
    φ.selmerGroup τ =
      ((AddSubgroup.pi Set.univ (φ.selmerStructure τ).localCondition).comap
        RestrictedProduct.coeAddMonoidHom).comap (φ.restrictedKerLocalization τ) := by
  ext c
  simp only [mem_selmerGroup_iff, mem_shafarevichTateGroup_iff,
    AddSubgroup.mem_comap, AddSubgroup.mem_pi, Set.mem_univ, forall_const,
    selmerStructure_localCondition, AddMonoidHom.mem_ker, pointRes_kerCoeffIncl]
  rfl

end TauCeti.Isogeny
