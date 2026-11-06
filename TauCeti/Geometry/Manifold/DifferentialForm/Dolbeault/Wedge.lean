/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Complex
public import TauCeti.Geometry.Manifold.DifferentialForm.Dolbeault.Leibniz
public import Mathlib.LinearAlgebra.Quotient.Bilinear

/-!
# Paired wedge products in Dolbeault cohomology

A continuous complex-bilinear coefficient pairing induces a complex-bilinear product of
Dolbeault classes. The product adds both type degrees. The graded Leibniz rule makes the
product of closed forms closed and makes its class independent of both representatives.
All forms use the generic real-manifold form carrier with complex coefficients. Taking the
pairing to be `ContinuousLinearMap.mul ℂ ℂ` gives the scalar wedge product. Neither finite
dimensionality nor completeness is required.

The descent uses Mathlib's `LinearMap.liftQ₂` and the existing `dolbeaultCohomology.quotientEquiv`;
the result lives in native categorical cohomology. The right-exactness primitive has the sign
`(-1)^(p+q)`, determined by the total degree of the left factor.

## References

* Daniel Huybrechts, *Complex Geometry: An Introduction*, Sections 1.3 and 2.6.
-/

public section

noncomputable section

open scoped Manifold ContDiff TauCeti.ComplexManifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]
  {F G H : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedAddCommGroup H] [NormedSpace ℂ H]

open SmoothAlmostComplexStructure

-- Pin the coefficient ring before synthesizing the additive group of nested submodules.
/-- The additive group of type forms with complex coefficients fixed. -/
local instance wedgeTypeFormsAddCommGroup (p q : ℕ) :
    AddCommGroup ((ofComplexManifold E M).typeForms (F := F) p q) :=
  Submodule.addCommGroup _

/-- The additive group of closed type forms with complex coefficients fixed. -/
local instance wedgeClosedFormsAddCommGroup (p q : ℕ) :
    AddCommGroup (Dolbeault.closedForms E M F p q) :=
  Submodule.addCommGroup _

namespace Dolbeault

namespace closedForms

/-- The paired wedge of closed type forms, as a complex-bilinear map. -/
def wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ) :
    closedForms E M F p q →ₗ[ℂ] closedForms E M G r s →ₗ[ℂ]
      closedForms E M H (p + r) (q + s) :=
  LinearMap.mk₂ ℂ (fun φ ψ ↦ ⟨(ofComplexManifold E M).wedgeWithType μ p q r s φ.1 ψ.1, by
    rw [mem_closedForms, delBar_wedgeWithType,
      (mem_closedForms p q φ.1).mp φ.2, (mem_closedForms r s ψ.1).mp ψ.2]
    simp only [map_zero, LinearMap.zero_apply, smul_zero, add_zero]⟩)
    (fun _ _ _ ↦ Subtype.ext <| by simp only [Submodule.coe_add, map_add, LinearMap.add_apply])
    (fun _ _ _ ↦ Subtype.ext <| by simp only [Submodule.coe_smul, map_smul, LinearMap.smul_apply])
    (fun _ _ _ ↦ Subtype.ext <| map_add _ _ _)
    (fun _ _ _ ↦ Subtype.ext <| map_smul _ _ _)

/-- The underlying type form of the closed-form product is the type-form product. -/
@[simp]
theorem coe_wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E M F p q) (ψ : closedForms E M G r s) :
    (wedgeWith μ p q r s φ ψ).1 = (ofComplexManifold E M).wedgeWithType μ p q r s φ.1 ψ.1 := (rfl)

/-- Multiplying an exact left factor by a closed right factor gives an exact form. -/
theorem wedgeWith_mem_exactForms_of_left_mem (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E M F p q) (ψ : closedForms E M G r s)
    (hφ : φ.1 ∈ exactForms E M F p q) :
    (wedgeWith μ p q r s φ ψ).1 ∈ exactForms E M H (p + r) (q + s) := by
  cases q with
  | zero =>
    have hzero : φ.1 = 0 := by simpa using hφ
    rw [coe_wedgeWith, hzero, LinearMap.map_zero₂]
    exact zero_mem _
  | succ q =>
    obtain ⟨α, hα⟩ := (mem_exactForms_succ p q φ.1).mp hφ
    refine mem_exactForms_of_eq_delBar (by omega) _
      ((ofComplexManifold E M).wedgeWithType μ p q r s α ψ.1) ?_
    rw [delBar_wedgeWithType, (mem_closedForms r s ψ.1).mp ψ.2, hα]
    simp only [map_zero, smul_zero, add_zero,
      coe_wedgeWith, coe_wedgeWithType, SmoothForm.cast_cast]

/-- Multiplying a closed left factor by an exact right factor gives an exact form. -/
theorem wedgeWith_mem_exactForms_of_right_mem (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E M F p q) (ψ : closedForms E M G r s)
    (hψ : ψ.1 ∈ exactForms E M G r s) :
    (wedgeWith μ p q r s φ ψ).1 ∈ exactForms E M H (p + r) (q + s) := by
  cases s with
  | zero =>
    have hzero : ψ.1 = 0 := by simpa using hψ
    rw [coe_wedgeWith, hzero, map_zero]
    exact zero_mem _
  | succ s =>
    obtain ⟨β, hβ⟩ := (mem_exactForms_succ r s ψ.1).mp hψ
    refine mem_exactForms_of_eq_delBar rfl _
      ((-1 : ℂ) ^ (p + q) • (ofComplexManifold E M).wedgeWithType μ p q r s φ.1 β) ?_
    rw [Submodule.coe_smul, map_smul, delBar_wedgeWithType,
      (mem_closedForms p q φ.1).mp φ.2, hβ]
    simp only [LinearMap.zero_apply, map_zero, zero_add,
      coe_wedgeWith, coe_wedgeWithType]
    -- The complex sign from the primitive cancels the real sign in the Leibniz rule.
    rw [← IsScalarTower.algebraMap_smul ℂ ((-1 : ℝ) ^ (p + q))]
    simp [smul_smul, ← mul_pow]

end closedForms

end Dolbeault

namespace dolbeaultCohomology

open Dolbeault

-- The quotient carrier otherwise leaves synthesis to infer the scalar ring from nested submodules.
/-- The native quotient instance for closed forms with complex scalars fixed. -/
local instance wedgeClosedFormsHasQuotient (p q : ℕ) : HasQuotient ↥(closedForms E M F p q)
    (Submodule ℂ ↥(closedForms E M F p q)) :=
  Submodule.hasQuotient (R := ℂ) (M := ↥(closedForms E M F p q))

/-- A continuous complex-bilinear coefficient pairing induces a product on Dolbeault cohomology,
adding both holomorphic and antiholomorphic degrees. -/
def wedgeWith (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ) :
    dolbeaultCohomology E M F p q →ₗ[ℂ] dolbeaultCohomology E M G r s →ₗ[ℂ]
      dolbeaultCohomology E M H (p + r) (q + s) := by
  let B := (closedForms.wedgeWith μ p q r s).compr₂ₛₗ
    (mk (E := E) (M := M) (F := H) (p + r) (q + s))
  have hleft : (exactForms E M F p q).comap (closedForms E M F p q).subtype ≤ B.ker := by
    intro φ hφ
    apply LinearMap.ext
    intro ψ
    exact (mk_eq_zero_iff _ _ _).mpr
      (closedForms.wedgeWith_mem_exactForms_of_left_mem μ p q r s φ ψ hφ)
  have hright : (exactForms E M G r s).comap (closedForms E M G r s).subtype ≤ B.flip.ker := by
    intro ψ hψ
    apply LinearMap.ext
    intro φ
    exact (mk_eq_zero_iff _ _ _).mpr
      (closedForms.wedgeWith_mem_exactForms_of_right_mem μ p q r s φ ψ hψ)
  exact (B.liftQ₂ _ _ hleft hright).compl₁₂
    (quotientEquiv (E := E) (M := M) (F := F) p q).symm.toLinearMap
    (quotientEquiv (E := E) (M := M) (F := G) r s).symm.toLinearMap

/-- The product of classes of closed forms is the class of their paired wedge. -/
@[simp]
theorem wedgeWith_mk (μ : F →L[ℂ] G →L[ℂ] H) (p q r s : ℕ)
    (φ : closedForms E M F p q) (ψ : closedForms E M G r s) :
    wedgeWith μ p q r s (mk p q φ) (mk r s ψ) =
      mk (p + r) (q + s) (closedForms.wedgeWith μ p q r s φ ψ) := by
  rw [← quotientEquiv_mk p q φ, ← quotientEquiv_mk r s ψ]
  simp only [wedgeWith, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply]
  exact LinearMap.liftQ₂_mk _ _ φ ψ

end dolbeaultCohomology

end TauCeti
