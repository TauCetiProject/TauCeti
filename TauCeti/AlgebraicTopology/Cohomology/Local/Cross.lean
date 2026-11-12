/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cohomology.Cup.Relative
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv

/-!
# The cross product of local classes at the origin

For spaces `V₁` and `V₂` with a zero and closed points, such as finite-dimensional real vector
spaces, a vector of `V₁ × V₂` is nonzero only if one of its components is, so the pair
`(V₁ × V₂, (V₁ × V₂) ∖ {0})` receives the relative cup product
(`TopCat.singularRelativeCupPullback`) of classes pulled back along the two projections:

`Hᵖ(V₁, V₁ ∖ {0}) × H^q(V₂, V₂ ∖ {0}) ⟶ Hᵖ⁺^q(V₁ × V₂, (V₁ × V₂) ∖ {0})`

(`TauCeti.complZeroPairCross`). It is natural under products of continuous linear equivalences
(`TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`). On fibres of vector
bundles it is the fibre value of the product of Thom pair classes.

## Main definitions

* `TauCeti.complZeroPairCross`: the product of classes of the pairs `(V₁, V₁ ∖ {0})` and
  `(V₂, V₂ ∖ {0})`, a class of `(V₁ × V₂, (V₁ × V₂) ∖ {0})`.

## Main results

* `TauCeti.compl_zero_prod_subset`: a nonzero vector of `V₁ × V₂` has a nonzero component.
* `TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`: naturality of the
  product under products of continuous linear equivalences.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2 (relative cross products).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set

universe w v u

namespace TauCeti

/-- If a vector of a product of two spaces with zero is nonzero, then one of its components is
nonzero. -/
theorem compl_zero_prod_subset (V₁ V₂ : Type w) [TopologicalSpace V₁] [TopologicalSpace V₂]
    [Zero V₁] [Zero V₂] :
    ({0}ᶜ : Set (TopCat.of (V₁ × V₂))) ⊆
      (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁))) ⁻¹' {0}ᶜ ∪
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) ⁻¹' {0}ᶜ := by
  intro v hv
  by_contra hc
  simp only [mem_union, mem_preimage, mem_compl_singleton_iff, not_or, not_not] at hc
  exact hv (Prod.ext hc.1 hc.2)

section ComplZeroPairCross

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]

/-- **The product of classes of the pairs `(V, V ∖ {0})`.** For spaces `V₁` and `V₂` with a zero
and closed points, such as finite-dimensional real vector spaces, this is the pairing
`Hᵖ(V₁, V₁ ∖ {0}; R, M) × H^q(V₂, V₂ ∖ {0}; S, N) ⟶ Hⁿ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T, L)`,
`p + q = n`, sending `(g₁, g₂)` to the relative cup product of their pull-backs along the two
projections (`TopCat.singularRelativeCupPullback`). -/
def complZeroPairCross (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularCohomology T
          k L n :=
  TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
    (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
    isOpen_compl_singleton (compl_zero_prod_subset V₁ V₂) p q n h

theorem complZeroPairCross_def (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    complZeroPairCross k V₁ V₂ u μ p q n h =
      TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
        isOpen_compl_singleton (compl_zero_prod_subset V₁ V₂) p q n h :=
  (rfl)

end ComplZeroPairCross

section LinearEquiv

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]
  {𝕜 : Type*} [Semiring 𝕜] {V₁ V₂ W₁ W₂ : Type w}
  [TopologicalSpace V₁] [AddCommMonoid V₁] [Module 𝕜 V₁]
  [TopologicalSpace V₂] [AddCommMonoid V₂] [Module 𝕜 V₂]
  [TopologicalSpace W₁] [AddCommMonoid W₁] [Module 𝕜 W₁]
  [TopologicalSpace W₂] [AddCommMonoid W₂] [Module 𝕜 W₂]
  [T1Space V₁] [T1Space V₂] [T1Space W₁] [T1Space W₂]

/-- **Naturality of the product of local classes under product equivalences.** For continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`, the product, for `V₁ × V₂`, of the
pull-backs along `f₁` and `f₂` of classes `g₁ ∈ Hᵖ(W₁, W₁ ∖ {0})` and `g₂ ∈ H^q(W₂, W₂ ∖ {0})` is
the pull-back along `f₁ × f₂` of their product for `W₁ × W₂`. -/
theorem complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ L) (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (p q n : ℕ) (h : p + q = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({0}ᶜ : Set W₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({0}ᶜ : Set W₂)).singularCohomology S k N q) :
    complZeroPairCross k V₁ V₂ u μ p q n h
        (TopPair.singularCohomologyMap f₁.complZeroPairIso.hom p g₁)
        (TopPair.singularCohomologyMap f₂.complZeroPairIso.hom q g₂) =
      TopPair.singularCohomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom n
        (complZeroPairCross k W₁ W₂ u μ p q n h g₁ g₂) := by
  -- A nonzero vector of `V₁ × V₂` has a component with nonzero image.
  have hZ (x : V₁ × V₂) (hx : x ≠ 0) : f₁ x.1 ≠ 0 ∨ f₂ x.2 ≠ 0 := by
    rcases compl_zero_prod_subset V₁ V₂ hx with h | h
    exacts [Or.inl ((map_ne_zero_iff _ f₁.injective).2 h),
      Or.inr ((map_ne_zero_iff _ f₂.injective).2 h)]
  rw [complZeroPairCross_def, complZeroPairCross_def, ContinuousLinearEquiv.complZeroPairIso_hom,
    ContinuousLinearEquiv.complZeroPairIso_hom, ContinuousLinearEquiv.complZeroPairIso_hom]
  refine (TopCat.singularRelativeCupPullback_singularCohomologyMap k u μ _ _ _ _
    isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton
    _ _ _ ?hZ₁ p q n h g₁ g₂).trans ?_
  case hZ₁ => exact fun x hx ↦ hZ x hx
  refine Eq.trans ?_ (TopCat.singularCohomologyMap_singularRelativeCupPullback k u μ _ _ _ _ _ _
    _ ?hZ₂ p q n h g₁ g₂).symm
  case hZ₂ => exact fun x hx ↦ hZ x hx
  have h₁ : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) ≫
      TopCat.ofHom ((f₁ : V₁ →L[𝕜] W₁) : C(V₁, W₁)) =
      TopCat.ofHom (((f₁.prodCongr f₂ : (V₁ × V₂) ≃L[𝕜] (W₁ × W₂)) : (V₁ × V₂) →L[𝕜] (W₁ × W₂)) :
        C(V₁ × V₂, W₁ × W₂)) ≫ TopCat.ofHom (ContinuousMap.fst : C(W₁ × W₂, W₁)) :=
    TopCat.ext fun _ ↦ rfl
  have h₂ : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) ≫
      TopCat.ofHom ((f₂ : V₂ →L[𝕜] W₂) : C(V₂, W₂)) =
      TopCat.ofHom (((f₁.prodCongr f₂ : (V₁ × V₂) ≃L[𝕜] (W₁ × W₂)) : (V₁ × V₂) →L[𝕜] (W₁ × W₂)) :
        C(V₁ × V₂, W₁ × W₂)) ≫ TopCat.ofHom (ContinuousMap.snd : C(W₁ × W₂, W₂)) :=
    TopCat.ext fun _ ↦ rfl
  simp only [h₁, h₂]

end LinearEquiv

end TauCeti
