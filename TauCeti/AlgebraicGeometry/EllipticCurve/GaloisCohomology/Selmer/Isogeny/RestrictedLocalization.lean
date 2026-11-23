/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisCohomology.Selmer.Isogeny.Unramified
public import TauCeti.RepresentationTheory.Homological.ContCohomology.SelmerStructure.RestrictedLocalization

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

open WeierstrassCurve TauCeti.ContCohomology
open Hom (ofIsogeny)
open scoped RestrictedProduct

variable {K : Type*} [Field K] [NumberField K]
  {W₁ W₂ : WeierstrassCurve K} [W₁.IsElliptic] [W₂.IsElliptic]
  (φ : Isogeny W₁.toAffine W₂.toAffine)
  (τ : ∀ v : GlobalNumberFields.Place K, SeparableClosure K →ₐ[K] SeparableClosure v.Completion)

private theorem eventually_localization_mem_localKummerCondition
    (c : H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff) :
    ∀ᶠ v in Filter.cofinite,
      (φ.selmerStructure τ).localization v c ∈
        (φ.baseChange v.Completion).localKummerCondition := by
  simpa only [selmerStructure_localization] using
    φ.eventually_kerRes_mem_localKummerCondition τ c

/-- The diagonal localization of global kernel cohomology into the all-place restricted
product relative to the local Kummer conditions. -/
def restrictedKerLocalization :
    H1 (AbsoluteGaloisGroup K) (ofIsogeny φ).KerCoeff →+
      Πʳ v : GlobalNumberFields.Place K,
        [H1 (AbsoluteGaloisGroup v.Completion) (ofIsogeny (φ.baseChange v.Completion)).KerCoeff,
          ((φ.baseChange v.Completion).localKummerCondition : Set _)] :=
  addRationalDiagonal (φ.selmerStructure τ).localization
    (fun v ↦ (φ.baseChange v.Completion).localKummerCondition)
    (eventually_localization_mem_localKummerCondition φ τ)

/-- Restricted kernel localization is the generic diagonal of the caller's restriction maps
relative to the canonical local Kummer conditions. -/
@[simp] theorem restrictedKerLocalization_def :
    φ.restrictedKerLocalization τ =
      addRationalDiagonal (fun v ↦ φ.kerRes (τ v))
        (fun v ↦ (φ.baseChange v.Completion).localKummerCondition)
        (φ.eventually_kerRes_mem_localKummerCondition τ) := by
  apply AddMonoidHom.ext
  intro c
  apply RestrictedProduct.ext
  intro v
  simp only [restrictedKerLocalization, addRationalDiagonal_apply, selmerStructure_localization]

/-- The Selmer group is the pullback, along restricted localization, of the subgroup satisfying
the local Kummer condition at every place. -/
theorem selmerGroup_eq_comap_restrictedKerLocalization :
    φ.selmerGroup τ =
      (integralAddSubgroup fun v : GlobalNumberFields.Place K ↦
        (φ.baseChange v.Completion).localKummerCondition).comap
          (φ.restrictedKerLocalization τ) := by
  have hcond := funext (selmerStructure_localCondition φ τ)
  rw [selmerGroup_def, restrictedKerLocalization, ← integralAddSubgroupOf_self]
  have h := (φ.selmerStructure τ).selmerGroup_eq_comap_addRationalDiagonal _
    (eventually_localization_mem_localKummerCondition φ τ)
  rw [hcond] at h
  exact h

end TauCeti.Isogeny
