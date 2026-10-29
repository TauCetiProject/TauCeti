/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.MFDeriv.Graph
public import TauCeti.Geometry.Symplectic.Lagrangian.Manifold
public import TauCeti.Geometry.Symplectic.Manifold.Prod

/-!
# Products of isotropic, coisotropic and Lagrangian maps

Let `σ₁` and `σ₂` be nondegenerate two-forms on `M₁` and `M₂`, and give `M₁ × M₂` the product form
`pr₁*σ₁ + pr₂*σ₂` (`TauCeti.SmoothTwoForm.prod`). For maps `f₁ : N₁ → M₁` and `f₂ : N₂ → M₂`, the
tangent image of the product map `f₁ × f₂` at `(x₁, x₂)` is the product of the tangent images of
`f₁` at `x₁` and of `f₂` at `x₂`, and the tangent-space form of the product is the direct sum of
those of the factors. The linear product formulas of
`TauCeti.Geometry.Symplectic.Lagrangian.Constructions` then show that `f₁ × f₂` is isotropic,
coisotropic or Lagrangian exactly when both factors are. This needs the factors to be
differentiable, since the tangent image of a map is taken with `mfderiv`, and the sources to be
nonempty for the converse: a product with an empty source has empty source and satisfies every
predicate vacuously. In particular a product of Lagrangian immersions is a Lagrangian immersion.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.isIsotropicMap_prodMap_iff`,
  `isCoisotropicMap_prodMap_iff`, `isLagrangianMap_prodMap_iff`: a product of differentiable maps
  from nonempty manifolds is isotropic, coisotropic or Lagrangian exactly when both factors are.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsIsotropicMap.prodMap`, `IsCoisotropicMap.prodMap`,
  `IsLagrangianMap.prodMap`: the forward directions, which need no nonempty sources.
* `TauCeti.SmoothTwoForm.IsNondegenerate.IsLagrangianImmersion.prodMap`: a product of Lagrangian
  immersions is a Lagrangian immersion.

## References

* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 3.
* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.4.
-/

public section

noncomputable section

open Module
open scoped Manifold ContDiff

namespace TauCeti.SmoothTwoForm.IsNondegenerate

variable {E₁ H₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [TopologicalSpace H₁]
  {I₁ : ModelWithCorners ℝ E₁ H₁} {M₁ : Type*} [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [IsManifold I₁ ∞ M₁]
  {E₂ H₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [TopologicalSpace H₂]
  {I₂ : ModelWithCorners ℝ E₂ H₂} {M₂ : Type*} [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [IsManifold I₂ ∞ M₂]
  {F₁ G₁ : Type*} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [TopologicalSpace G₁]
  {J₁ : ModelWithCorners ℝ F₁ G₁} {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace G₁ N₁]
  {F₂ G₂ : Type*} [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [TopologicalSpace G₂]
  {J₂ : ModelWithCorners ℝ F₂ G₂} {N₂ : Type*} [TopologicalSpace N₂] [ChartedSpace G₂ N₂]
  {σ₁ : SmoothTwoForm I₁ M₁} {σ₂ : SmoothTwoForm I₂ M₂}
  {hσ₁ : σ₁.IsNondegenerate} {hσ₂ : σ₂.IsNondegenerate} {f₁ : N₁ → M₁} {f₂ : N₂ → M₂}

/-! ### Tangent images of a product map -/

variable (hσ₁ hσ₂) in
/-- The tangent image of a product of differentiable maps is isotropic for the product form exactly
when the tangent images of both factors are isotropic. -/
private theorem isIsotropic_range_mfderiv_prodMap_iff {p : N₁ × N₂}
    (hf₁ : MDifferentiableAt J₁ I₁ f₁ p.1) (hf₂ : MDifferentiableAt J₂ I₂ f₂ p.2) :
    ((hσ₁.prod hσ₂).symplecticFormAt (Prod.map f₁ f₂ p)).IsIsotropic
        (LinearMap.range (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map f₁ f₂) p).toLinearMap) ↔
      (hσ₁.symplecticFormAt (f₁ p.1)).IsIsotropic
          (LinearMap.range (mfderiv J₁ I₁ f₁ p.1).toLinearMap) ∧
        (hσ₂.symplecticFormAt (f₂ p.2)).IsIsotropic
          (LinearMap.range (mfderiv J₂ I₂ f₂ p.2).toLinearMap) := by
  rw [← SymplecticForm.isIsotropic_map_transport_iff
      (e := (Manifold.tangentSpaceProdEquiv (Prod.map f₁ f₂ p)).toLinearEquiv),
    symplecticFormAt_prod, Manifold.map_range_mfderiv_prodMap hf₁ hf₂,
    SymplecticForm.isIsotropic_prod_iff]
  -- The points `(Prod.map f₁ f₂ p).1` and `f₁ p.1` agree definitionally.
  rfl

variable (hσ₁ hσ₂) in
/-- The tangent image of a product of differentiable maps is coisotropic for the product form
exactly when the tangent images of both factors are coisotropic. -/
private theorem isCoisotropic_range_mfderiv_prodMap_iff {p : N₁ × N₂}
    (hf₁ : MDifferentiableAt J₁ I₁ f₁ p.1) (hf₂ : MDifferentiableAt J₂ I₂ f₂ p.2) :
    ((hσ₁.prod hσ₂).symplecticFormAt (Prod.map f₁ f₂ p)).IsCoisotropic
        (LinearMap.range (mfderiv (J₁.prod J₂) (I₁.prod I₂) (Prod.map f₁ f₂) p).toLinearMap) ↔
      (hσ₁.symplecticFormAt (f₁ p.1)).IsCoisotropic
          (LinearMap.range (mfderiv J₁ I₁ f₁ p.1).toLinearMap) ∧
        (hσ₂.symplecticFormAt (f₂ p.2)).IsCoisotropic
          (LinearMap.range (mfderiv J₂ I₂ f₂ p.2).toLinearMap) := by
  rw [← SymplecticForm.isCoisotropic_map_transport_iff
      (e := (Manifold.tangentSpaceProdEquiv (Prod.map f₁ f₂ p)).toLinearEquiv),
    symplecticFormAt_prod, Manifold.map_range_mfderiv_prodMap hf₁ hf₂,
    SymplecticForm.isCoisotropic_prod_iff]
  -- The points `(Prod.map f₁ f₂ p).1` and `f₁ p.1` agree definitionally.
  rfl

/-! ### Products of isotropic, coisotropic and Lagrangian maps -/

/-- A product of differentiable maps from nonempty manifolds is isotropic for the product form
exactly when both factors are isotropic. -/
theorem isIsotropicMap_prodMap_iff [Nonempty N₁] [Nonempty N₂] (hf₁ : MDifferentiable J₁ I₁ f₁)
    (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsIsotropicMap (J₁.prod J₂) (Prod.map f₁ f₂) ↔
      hσ₁.IsIsotropicMap J₁ f₁ ∧ hσ₂.IsIsotropicMap J₂ f₂ := by
  simp only [isIsotropicMap_iff_forall, Prod.forall]
  rw [forall₂_congr fun x y ↦
    isIsotropic_range_mfderiv_prodMap_iff hσ₁ hσ₂ (p := (x, y)) (hf₁ x) (hf₂ y)]
  exact ⟨fun h ↦ ⟨fun x ↦ (h x (Classical.arbitrary N₂)).1,
    fun y ↦ (h (Classical.arbitrary N₁) y).2⟩, fun h x y ↦ ⟨h.1 x, h.2 y⟩⟩

/-- A product of differentiable maps from nonempty manifolds is coisotropic for the product form
exactly when both factors are coisotropic. -/
theorem isCoisotropicMap_prodMap_iff [Nonempty N₁] [Nonempty N₂] (hf₁ : MDifferentiable J₁ I₁ f₁)
    (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsCoisotropicMap (J₁.prod J₂) (Prod.map f₁ f₂) ↔
      hσ₁.IsCoisotropicMap J₁ f₁ ∧ hσ₂.IsCoisotropicMap J₂ f₂ := by
  simp only [isCoisotropicMap_iff, Prod.forall]
  rw [forall₂_congr fun x y ↦
    isCoisotropic_range_mfderiv_prodMap_iff hσ₁ hσ₂ (p := (x, y)) (hf₁ x) (hf₂ y)]
  exact ⟨fun h ↦ ⟨fun x ↦ (h x (Classical.arbitrary N₂)).1,
    fun y ↦ (h (Classical.arbitrary N₁) y).2⟩, fun h x y ↦ ⟨h.1 x, h.2 y⟩⟩

/-- A product of differentiable maps from nonempty manifolds is Lagrangian for the product form
exactly when both factors are Lagrangian. -/
theorem isLagrangianMap_prodMap_iff [Nonempty N₁] [Nonempty N₂] (hf₁ : MDifferentiable J₁ I₁ f₁)
    (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsLagrangianMap (J₁.prod J₂) (Prod.map f₁ f₂) ↔
      hσ₁.IsLagrangianMap J₁ f₁ ∧ hσ₂.IsLagrangianMap J₂ f₂ := by
  rw [isLagrangianMap_iff, isIsotropicMap_prodMap_iff hf₁ hf₂, isCoisotropicMap_prodMap_iff hf₁ hf₂,
    isLagrangianMap_iff, isLagrangianMap_iff]
  tauto

/-- A product of differentiable isotropic maps is isotropic for the product form. -/
theorem IsIsotropicMap.prodMap (h₁ : hσ₁.IsIsotropicMap J₁ f₁) (h₂ : hσ₂.IsIsotropicMap J₂ f₂)
    (hf₁ : MDifferentiable J₁ I₁ f₁) (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsIsotropicMap (J₁.prod J₂) (Prod.map f₁ f₂) :=
  isIsotropicMap_iff_forall.2 fun p ↦
    (isIsotropic_range_mfderiv_prodMap_iff hσ₁ hσ₂ (hf₁ p.1) (hf₂ p.2)).2
      ⟨isIsotropicMap_iff_forall.1 h₁ p.1, isIsotropicMap_iff_forall.1 h₂ p.2⟩

/-- A product of differentiable coisotropic maps is coisotropic for the product form. -/
theorem IsCoisotropicMap.prodMap (h₁ : hσ₁.IsCoisotropicMap J₁ f₁)
    (h₂ : hσ₂.IsCoisotropicMap J₂ f₂) (hf₁ : MDifferentiable J₁ I₁ f₁)
    (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsCoisotropicMap (J₁.prod J₂) (Prod.map f₁ f₂) :=
  isCoisotropicMap_iff.2 fun p ↦
    (isCoisotropic_range_mfderiv_prodMap_iff hσ₁ hσ₂ (hf₁ p.1) (hf₂ p.2)).2
      ⟨isCoisotropicMap_iff.1 h₁ p.1, isCoisotropicMap_iff.1 h₂ p.2⟩

/-- A product of differentiable Lagrangian maps is Lagrangian for the product form. -/
theorem IsLagrangianMap.prodMap (h₁ : hσ₁.IsLagrangianMap J₁ f₁) (h₂ : hσ₂.IsLagrangianMap J₂ f₂)
    (hf₁ : MDifferentiable J₁ I₁ f₁) (hf₂ : MDifferentiable J₂ I₂ f₂) :
    (hσ₁.prod hσ₂).IsLagrangianMap (J₁.prod J₂) (Prod.map f₁ f₂) :=
  isLagrangianMap_iff.2 ⟨h₁.isIsotropicMap.prodMap h₂.isIsotropicMap hf₁ hf₂,
    h₁.isCoisotropicMap.prodMap h₂.isCoisotropicMap hf₁ hf₂⟩

/-- A product of Lagrangian immersions is a Lagrangian immersion for the product form. -/
theorem IsLagrangianImmersion.prodMap [FiniteDimensional ℝ E₁] [FiniteDimensional ℝ E₂]
    [FiniteDimensional ℝ F₁] [FiniteDimensional ℝ F₂]
    [IsManifold J₁ ∞ N₁] [IsManifold J₂ ∞ N₂]
    (h₁ : hσ₁.IsLagrangianImmersion J₁ f₁) (h₂ : hσ₂.IsLagrangianImmersion J₂ f₂) :
    (hσ₁.prod hσ₂).IsLagrangianImmersion (J₁.prod J₂) (Prod.map f₁ f₂) where
  isImmersion := h₁.isImmersion.prodMap h₂.isImmersion
  isIsotropicMap := h₁.isIsotropicMap.prodMap h₂.isIsotropicMap
    (h₁.isImmersion.contMDiff.mdifferentiable (by simp))
    (h₂.isImmersion.contMDiff.mdifferentiable (by simp))
  two_mul_finrank := by
    rw [finrank_prod, finrank_prod, mul_add, h₁.two_mul_finrank, h₂.two_mul_finrank]

end TauCeti.SmoothTwoForm.IsNondegenerate
