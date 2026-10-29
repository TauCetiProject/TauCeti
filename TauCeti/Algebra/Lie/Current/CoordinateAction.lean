/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Current.Substitution
public import TauCeti.Algebra.Lie.Extension

/-!
# Coordinate changes on residue central extensions

Substitution by a formal coordinate preserves the residue cocycle, so it lifts to a Lie
automorphism of the native `LieAlgebra.ofTwoCocycle` extension, acting by substitution on
currents and fixing the central coordinate. This includes the zero form and needs no
finite-dimensionality or characteristic assumption.

Formal coordinates compose contravariantly under substitution. The actual algebra
automorphisms of `K⟦X⟧`, with their usual multiplication by composition, therefore act
covariantly on the extension. The constructions here are algebraic.

The lift uses `LieAlgebra.ofTwoCocycle.mapEquiv` with the current substitution equivalence
and the identity on the trivial coefficient module.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., Chapter 7, for the
  coordinate-invariant residue extension of current algebras.
-/

public section

noncomputable section

open scoped LaurentSeries
open PowerSeries

namespace TauCeti.CurrentAlgebra

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
variable (Φ : LinearMap.BilinForm K L) (hΦ : Φ.lieInvariant L) (hΦs : Φ.IsSymm)

local notation "cΦ" => twoCocycleOfBilinear K L Φ hΦ hΦs
local notation "EΦ" => _root_.LieAlgebra.ofTwoCocycle cΦ

/-- The lift of a power-series algebra automorphism to the residue central extension.
It fixes the central coordinate and substitutes the image of `X` in the current. -/
def coordinateExtensionLieEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) : EΦ ≃ₗ⁅K⁆ EΦ :=
  _root_.LieAlgebra.ofTwoCocycle.mapEquiv cΦ (substLieEquiv (FormalCoordinate.ofAlgEquiv σ))
    (LinearEquiv.refl K _) cΦ fun u v ↦ by simp

/-- In product coordinates the lift substitutes the current and fixes the scalar. -/
@[simp]
theorem coordinateExtensionLieEquiv_ofProd (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧)
    (u : currentAlgebra K L) (a : TrivialLieModule K (currentAlgebra K L) K) :
    coordinateExtensionLieEquiv Φ hΦ hΦs σ (_root_.LieAlgebra.ofProd cΦ (u, a)) =
      _root_.LieAlgebra.ofProd cΦ (substLieEquiv (FormalCoordinate.ofAlgEquiv σ) u, a) := by
  simp [coordinateExtensionLieEquiv]

/-- Product coordinates of a transformed extension element. -/
@[simp]
theorem ofProd_symm_coordinateExtensionLieEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) (z : EΦ) :
    (_root_.LieAlgebra.ofProd cΦ).symm (coordinateExtensionLieEquiv Φ hΦ hΦs σ z) =
      (substLieEquiv (FormalCoordinate.ofAlgEquiv σ) ((_root_.LieAlgebra.ofProd cΦ).symm z).1,
        ((_root_.LieAlgebra.ofProd cΦ).symm z).2) := by
  simp [coordinateExtensionLieEquiv]

/-- The lifted coordinate change lies over substitution on currents. -/
theorem proj_coordinateExtensionLieEquiv (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) (z : EΦ) :
    _root_.LieAlgebra.ofTwoCocycle.proj cΦ (coordinateExtensionLieEquiv Φ hΦ hΦs σ z) =
      substLieEquiv (FormalCoordinate.ofAlgEquiv σ)
        (_root_.LieAlgebra.ofTwoCocycle.proj cΦ z) := by
  simp

/-- Every element of the distinguished central summand, in particular its generator, is fixed. -/
theorem coordinateExtensionLieEquiv_central (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧)
    (a : TrivialLieModule K (currentAlgebra K L) K) :
    coordinateExtensionLieEquiv Φ hΦ hΦs σ (_root_.LieAlgebra.ofProd cΦ (0, a)) =
      _root_.LieAlgebra.ofProd cΦ (0, a) := by
  simp

/-- The identity power-series automorphism acts identically on the residue extension. -/
@[simp]
theorem coordinateExtensionLieEquiv_one (z : EΦ) :
    coordinateExtensionLieEquiv Φ hΦ hΦs (1 : K⟦X⟧ ≃ₐ[K] K⟦X⟧) z = z := by
  have h := (FormalCoordinate.substAlgEquivMulEquiv K).symm.map_one
  apply (_root_.LieAlgebra.ofProd cΦ).symm.injective
  simp only [FormalCoordinate.substAlgEquivMulEquiv_symm_apply, MulOpposite.unop_one] at h
  simp [h]

/-- With the usual product `σ * τ = σ ∘ τ`, lifted coordinate changes compose in that order.
-/
theorem coordinateExtensionLieEquiv_mul_apply (σ τ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) (z : EΦ) :
    coordinateExtensionLieEquiv Φ hΦ hΦs (σ * τ) z =
      coordinateExtensionLieEquiv Φ hΦ hΦs σ
        (coordinateExtensionLieEquiv Φ hΦ hΦs τ z) := by
  have h := (FormalCoordinate.substAlgEquivMulEquiv K).symm.map_mul
    (MulOpposite.op τ) (MulOpposite.op σ)
  simp only [FormalCoordinate.substAlgEquivMulEquiv_symm_apply, MulOpposite.unop_mul,
    MulOpposite.unop_op] at h
  apply (_root_.LieAlgebra.ofProd cΦ).symm.injective
  simp [h, substLieEquiv_mul_apply]

/-- The inverse power-series automorphism induces the inverse automorphism of the extension. -/
theorem coordinateExtensionLieEquiv_symm (σ : K⟦X⟧ ≃ₐ[K] K⟦X⟧) :
    (coordinateExtensionLieEquiv Φ hΦ hΦs σ).symm =
      coordinateExtensionLieEquiv Φ hΦ hΦs σ⁻¹ := by
  apply LieEquiv.ext
  intro z
  apply (coordinateExtensionLieEquiv Φ hΦ hΦs σ).injective
  simp only [LieEquiv.coe_toLieHom]
  rw [LieEquiv.apply_symm_apply, ← coordinateExtensionLieEquiv_mul_apply, mul_inv_cancel,
    coordinateExtensionLieEquiv_one]

end TauCeti.CurrentAlgebra
