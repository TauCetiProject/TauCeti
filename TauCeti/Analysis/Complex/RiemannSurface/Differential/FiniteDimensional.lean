/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.IdentityTheorem
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Sheaf
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.Meromorphic
import TauCeti.Analysis.Complex.RiemannSurface.Divisor.FiniteDimensional

/-!
# Finite-dimensionality of holomorphic differentials

The holomorphic differentials on a compact connected Riemann surface form a finite-dimensional
complex vector space. This is the space of global sections of the holomorphic cotangent sheaf,
whose dimension is compared with the genus by Serre duality.

If there is a nonzero holomorphic differential `ω`, division by `ω` embeds this space into
meromorphic functions with poles bounded by `div ω`. These are precisely the image of the
finite-dimensional divisor-section space `𝒪_(div ω)(X)`. Unique continuation ensures that
`ω` has finite order everywhere. If there is no nonzero differential, the conclusion is
immediate. No existence of a nonzero differential or meromorphic map is assumed.

## References

* O. Forster, *Lectures on Riemann Surfaces*, §§16–17, for divisor section spaces and
  holomorphic differentials.
-/

public noncomputable section

open Filter Function Set Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [IsManifold 𝓘(ℂ) 1 X] [ConnectedSpace X]

namespace OneForm

/-- Division of holomorphic differentials by an everywhere meromorphic differential,
as a linear map into the meromorphic function field. -/
def ratioLinearMap (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x) :
    holomorphicOneForms X →ₗ[ℂ] MeromorphicFunction X where
  toFun η := ratioFunction η.1 ω (holomorphicOneForms.meromorphicAt η) hω
  map_add' η θ := ratioFunction_add
    (holomorphicOneForms.meromorphicAt η) (holomorphicOneForms.meromorphicAt θ) hω
  map_smul' c η := ratioFunction_smul c (holomorphicOneForms.meromorphicAt η) hω

@[simp]
theorem ratioLinearMap_apply (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    (η : holomorphicOneForms X) :
    ratioLinearMap ω hω η =
      ratioFunction η.1 ω (holomorphicOneForms.meromorphicAt η) hω :=
  (rfl)

/-- Division by a meromorphic differential of finite order at one point loses no holomorphic
differential. -/
theorem ratioLinearMap_injective (ω : OneForm X) (hω : ∀ x, ω.MeromorphicAt x)
    {x : X} (hx : ω.order x ≠ ⊤) : Injective (ratioLinearMap ω hω) := by
  intro η θ h
  apply sub_eq_zero.1
  apply Subtype.ext
  have hzero : ratioLinearMap ω hω (η - θ) = 0 := by
    rw [LinearMap.map_sub (M := holomorphicOneForms X) (ratioLinearMap ω hω), h, sub_self]
  apply (order_eq_top_iff (mem_holomorphicOneForms.1 (η - θ).2) x).1
  have ho := order_ratioFunction_add_order (holomorphicOneForms.meromorphicAt (η - θ)) hω hx
  rw [← ratioLinearMap_apply, hzero, AddValuation.map_zero, WithTop.top_add] at ho
  exact ho.symm

/-- The quotient of a holomorphic differential by `ω` lies in the image of the divisor-section
space with pole bound `div ω`. -/
theorem ratioLinearMap_mem_range_toMeromorphic [CompactSpace X] (ω : OneForm X)
    (hω : ∀ x, ω.MeromorphicAt x) (hω₀ : ∀ x, ω.order x ≠ ⊤)
    (η : holomorphicOneForms X) :
    ratioLinearMap ω hω η ∈ (divisorSections.toMeromorphic ω.divisor).range := by
  rw [divisorSections.mem_range_toMeromorphic_iff]
  intro x
  have ho := order_ratioFunction_add_order (holomorphicOneForms.meromorphicAt η) hω (hω₀ x)
  rw [← ratioLinearMap_apply, ← coe_coeff_divisor hω (hω₀ x)] at ho
  simp only [AlgebraicGeometry.WeilDivisor.coeff] at ho
  have hn := (mem_holomorphicOneForms.1 η.2 x).order_nonneg
  rw [← ho] at hn
  by_cases hq : MeromorphicFunction.order x (ratioLinearMap ω hω η) = ⊤
  · rw [hq]
    exact le_top
  · lift MeromorphicFunction.order x (ratioLinearMap ω hω η) to ℤ using hq with q
    norm_cast at hn ⊢
    omega

end OneForm

/-- Holomorphic differentials on a compact connected Riemann surface form a finite-dimensional
complex vector space. This does not require Riemann–Roch or the existence of a nonzero form. -/
instance finiteDimensional_holomorphicOneForms [CompactSpace X] :
    FiniteDimensional ℂ (holomorphicOneForms X) := by
  classical
  rcases subsingleton_or_nontrivial (holomorphicOneForms X) with h | h
  · let := h
    infer_instance
  obtain ⟨ω, hωne⟩ := exists_ne (0 : holomorphicOneForms X)
  have hω := mem_holomorphicOneForms.1 ω.2
  have hω₀ (x : X) : (ω : OneForm X).order x ≠ ⊤ := by
    exact fun hx ↦ hωne (Subtype.ext ((OneForm.order_eq_top_iff hω x).1 hx))
  let F := OneForm.ratioLinearMap (ω : OneForm X) (holomorphicOneForms.meromorphicAt ω)
  let F' := F.codRestrict (divisorSections.toMeromorphic (ω : OneForm X).divisor).range
    (OneForm.ratioLinearMap_mem_range_toMeromorphic (ω : OneForm X)
      (holomorphicOneForms.meromorphicAt ω) hω₀)
  exact FiniteDimensional.of_injective F' fun η θ heq ↦
    OneForm.ratioLinearMap_injective (ω : OneForm X) (holomorphicOneForms.meromorphicAt ω)
      (hω₀ (Classical.arbitrary X)) (congrArg Subtype.val heq)

/-- The global section space of the native holomorphic differential sheaf is finite-dimensional.
This is the `H⁰(Ω)` space appearing in Serre duality. -/
instance finiteDimensional_differentialSheaf_zero_globalSections [CompactSpace X] :
    FiniteDimensional ℂ ((differentialSheaf (0 : AlgebraicGeometry.WeilDivisor X)).obj.obj
      (Opposite.op ⊤)) :=
  Module.Finite.equiv
    ((differentialSheafSectionsEquiv (0 : AlgebraicGeometry.WeilDivisor X) ⊤).trans
      (differentialSectionsZeroEquiv (X := X))).symm

end TauCeti.RiemannSurface
