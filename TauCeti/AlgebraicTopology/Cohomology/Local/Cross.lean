/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.Topology.Category.TopPair.ContinuousLinearEquiv
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The cross product of local classes at the origin

For spaces `V₁` and `V₂` with a zero and closed points, such as finite-dimensional real vector
spaces, a vector of `V₁ × V₂` is nonzero if and only if one of its components is
(`TauCeti.compl_zero_prod_eq`), so the pair `(V₁ × V₂, (V₁ × V₂) ∖ {0})` receives the relative cup
product (`TopCat.singularRelativeCupPullback`) of classes pulled back along the two projections:

`Hᵖ(V₁, V₁ ∖ {0}) × H^q(V₂, V₂ ∖ {0}) ⟶ Hᵖ⁺^q(V₁ × V₂, (V₁ × V₂) ∖ {0})`

(`TauCeti.complZeroPairCross`). Dually, the pair `(V₁ × V₂, (V₁ × V₂) ∖ {0})` receives the relative
homology cross product (`TauCeti.complZeroPairHomologyCross`), intertwined with
`TauCeti.complZeroPairCross` by the relative Kronecker pairing
(`TauCeti.complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross`).

At points with Euclidean charts around the origin, in particular on finite-dimensional real normed
spaces, pairing with the homology cross product of local generators shows that
`TauCeti.complZeroPairCross` sends a pair of classes to a generator of the top-degree local
cohomology over any commutative ring `k` if and only if each factor is a generator
(`TauCeti.span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph`,
`TauCeti.span_complZeroPairCross_eq_top_iff`). On fibres of vector bundles it is the fibre value of
the product of Thom pair classes, which therefore carries Thom classes to Thom classes.

## Main definitions

* `TauCeti.complZeroPairCross`: the product of cohomology classes of the pairs `(V₁, V₁ ∖ {0})` and
  `(V₂, V₂ ∖ {0})`, a class of `(V₁ × V₂, (V₁ × V₂) ∖ {0})`.
* `TauCeti.complZeroPairHomologyCross`: the relative homology cross product of `(V₁, V₁ ∖ {0})` and
  `(V₂, V₂ ∖ {0})` into `(V₁ × V₂, (V₁ × V₂) ∖ {0})`.

## Main results

* `TauCeti.compl_zero_prod_subset`, `TauCeti.compl_zero_prod_superset` and
  `TauCeti.compl_zero_prod_eq`: a vector of `V₁ × V₂` is nonzero if and only if one of its
  components is nonzero.
* `TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`: naturality of the
  product under products of continuous linear equivalences.
* `TauCeti.complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross`: Kronecker
  multiplicativity `⟨g₁ × g₂, x₁ × x₂⟩ = μ (⟨g₁, x₁⟩ ⊗ ⟨g₂, x₂⟩)` at the origin.
* `TauCeti.span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph` and
  `TauCeti.span_complZeroPairCross_eq_top_iff`: over any commutative ring `k`, the product of two
  top-degree local cohomology classes generates if and only if both factors generate.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2 (relative cross products) and Section 3.B (the
  relative Künneth formula).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §10 (local model of the product of Thom classes).
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

/-- If a vector of a product of two spaces with zero has a nonzero component, then it is
nonzero. -/
theorem compl_zero_prod_superset (V₁ V₂ : Type w) [TopologicalSpace V₁] [TopologicalSpace V₂]
    [Zero V₁] [Zero V₂] :
    (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁))) ⁻¹' {0}ᶜ ∪
      (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) ⁻¹' {0}ᶜ ⊆
        ({0}ᶜ : Set (TopCat.of (V₁ × V₂))) := by
  rintro v (hv | hv) h0
  · exact mem_compl_singleton_iff.1 hv (congrArg Prod.fst h0)
  · exact mem_compl_singleton_iff.1 hv (congrArg Prod.snd h0)

/-- A vector of a product of two spaces with zero is nonzero if and only if one of its components
is nonzero. -/
theorem compl_zero_prod_eq (V₁ V₂ : Type w) [TopologicalSpace V₁] [TopologicalSpace V₂]
    [Zero V₁] [Zero V₂] :
    ({0}ᶜ : Set (TopCat.of (V₁ × V₂))) =
      (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁))) ⁻¹' {0}ᶜ ∪
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) ⁻¹' {0}ᶜ :=
  Subset.antisymm (compl_zero_prod_subset V₁ V₂) (compl_zero_prod_superset V₁ V₂)

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

section ComplZeroPairHomologyCross

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T M N L : C}

/-- **The relative homology cross product on complements of the origin.** For spaces `V₁` and `V₂`
with a zero and a morphism `v : R ⊗ S ⟶ T`, this is the pairing
`Hₚ(V₁, V₁ ∖ {0}; R) ⊗ H_q(V₂, V₂ ∖ {0}; S) ⟶ Hₙ(V₁ × V₂, (V₁ × V₂) ∖ {0}; T)`, `p + q = n`,
built from `TopCat.singularRelativeHomologyCross` by pushing forward along `v` and identifying
`V₁ × (V₂ ∖ {0}) ∪ (V₁ ∖ {0}) × V₂` with `(V₁ × V₂) ∖ {0}`. -/
def complZeroPairHomologyCross (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁]
    [TopologicalSpace V₂] [Zero V₂] (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularHomology R p ⊗
      (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularHomology S q ⟶
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂)) ({0}ᶜ : Set (V₁ × V₂))).singularHomology T n :=
  TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
      ({0}ᶜ : Set (TopCat.of V₁)) ({0}ᶜ : Set (TopCat.of V₂)) p q n h ≫
    HomologicalComplex.homologyMap
      (K := (TopPair.ofSubset
        (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
          CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
            ({0}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
      (L := (TopPair.ofSubset
        (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
          CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
            ({0}ᶜ : Set V₂))).singularChainComplex T)
      (((SSetPair.chainComplexFunctor C).map v).app
        (TopPair.toSSetPair.obj (TopPair.ofSubset
          (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
            CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
              ({0}ᶜ : Set V₂))))) n ≫
    TopPair.singularHomologyMap
      (TopPair.ofSubsetMap
        (B := CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
          CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))
        (B' := ({(0 : V₁ × V₂)}ᶜ : Set (V₁ × V₂)))
        (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) fun _ hx ↦ compl_zero_prod_superset V₁ V₂ hx) T n

/-- Definitional unfolding of `TauCeti.complZeroPairHomologyCross`. -/
theorem complZeroPairHomologyCross_def (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁]
    [TopologicalSpace V₂] [Zero V₂] (v : R ⊗ S ⟶ T) (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))] :
    complZeroPairHomologyCross V₁ V₂ v p q n h =
      TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R S
          ({0}ᶜ : Set (TopCat.of V₁)) ({0}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        HomologicalComplex.homologyMap
          (K := (TopPair.ofSubset
            (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
              CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
                ({0}ᶜ : Set V₂))).singularChainComplex (R ⊗ S))
          (L := (TopPair.ofSubset
            (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
              CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
                ({0}ᶜ : Set V₂))).singularChainComplex T)
          (((SSetPair.chainComplexFunctor C).map v).app
            (TopPair.toSSetPair.obj (TopPair.ofSubset
              (CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
                CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
                  ({0}ᶜ : Set V₂))))) n ≫
        TopPair.singularHomologyMap
          (TopPair.ofSubsetMap
            (B := CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₁) ∪
              CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({0}ᶜ : Set V₂))
            (B' := ({(0 : V₁ × V₂)}ᶜ : Set (V₁ × V₂)))
            (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂)) fun _ hx ↦ compl_zero_prod_superset V₁ V₂ hx) T n :=
  (rfl)

variable (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- **Kronecker multiplicativity of local cross products at the origin**: when
`v ≫ u = 𝟙 (R ⊗ S)`, evaluating `complZeroPairCross` on `complZeroPairHomologyCross` gives the
tensor product of the relative Kronecker evaluations followed by `μ`. -/
theorem complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross
    (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology S k N q) :
    complZeroPairHomologyCross V₁ V₂ v p q n h ≫
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker (R := T) (M := L)
          k n (complZeroPairCross k V₁ V₂ u μ p q n h g₁ g₂) =
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularKronecker (R := R) (M := M) k p g₁ ⊗ₘ
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularKronecker (R := S) (M := N) k q
          g₂) ≫ μ := by
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) =
      CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  have hsnd : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) =
      CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  simp only [complZeroPairHomologyCross_def, complZeroPairCross_def, hfst, hsnd]
  refine (Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans ?_)
  exact TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback
    (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton isOpen_compl_singleton
    (compl_zero_prod_subset V₁ V₂) (compl_zero_prod_superset V₁ V₂) hu μ p q n h g₁ g₂

/-- **Off-diagonal vanishing for local cross products at the origin**: when `p ≠ p'` and
`v ≫ u = 𝟙 (R ⊗ S)`, `complZeroPairCross` in bidegree `(p', q')` evaluates to zero on
`complZeroPairHomologyCross` in bidegree `(p, q)`. -/
theorem complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross_of_ne
    (V₁ V₂ : Type w) [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology R k M p')
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology S k N q') :
    complZeroPairHomologyCross V₁ V₂ v p q n h ≫
        (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker (R := T) (M := L)
          k n (complZeroPairCross k V₁ V₂ u μ p' q' n h' g₁ g₂) = 0 := by
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) =
      CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  have hsnd : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) =
      CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  simp only [complZeroPairHomologyCross_def, complZeroPairCross_def, hfst, hsnd]
  refine (Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans ?_)
  exact
    TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne
      (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton isOpen_compl_singleton
      (compl_zero_prod_subset V₁ V₂) (compl_zero_prod_superset V₁ V₂) hu μ h h' hp g₁ g₂

end ComplZeroPairHomologyCross

section SpanEqTop

/-- **Local cross products preserve and reflect generators at Euclidean chart origins.** Let `V₁`
and `V₂` be T1 spaces with charts around `0` to finite-dimensional real normed spaces `E₁` and
`E₂`, and let `v : k ⊗ k ⟶ k`, `u : k ⟶ k ⊗ k` and `μ : k ⊗ k ⟶ k` satisfy `v ≫ u = 𝟙 _` and
`IsUnit (μ (1 ⊗ₜ 1))`. Over any commutative ring `k`, the local cross product of
`g₁ ∈ H^{dim E₁}(V₁, V₁ ∖ {0}; k, k)` and `g₂ ∈ H^{dim E₂}(V₂, V₂ ∖ {0}; k, k)` generates
`H^{dim E₁ + dim E₂}(V₁ × V₂, (V₁ × V₂) ∖ {0}; k, k)` if and only if both `g₁` and `g₂` generate
their respective local cohomology modules. -/
theorem span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    (φ₁ : OpenPartialHomeomorph V₁ E₁) (h0₁ : (0 : V₁) ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) (h0₂ : (0 : V₂) ∈ φ₂.source)
    {v : ModuleCat.of k k ⊗ ModuleCat.of k k ⟶ ModuleCat.of k k}
    {u : ModuleCat.of k k ⟶ ModuleCat.of k k ⊗ ModuleCat.of k k}
    (hu : v ≫ u = 𝟙 (ModuleCat.of k k ⊗ ModuleCat.of k k))
    {μ : ModuleCat.of k k ⊗ ModuleCat.of k k ⟶ ModuleCat.of k k}
    (hμ : IsUnit (μ.hom ((1 : k) ⊗ₜ[k] (1 : k))))
    {n : ℕ} (h : Module.finrank ℝ E₁ + Module.finrank ℝ E₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ E₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ E₂)) :
    Submodule.span k {complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ := by
  have hn : n = Module.finrank ℝ (E₁ × E₂) := h.symm.trans Module.finrank_prod.symm
  subst hn
  have h0₁₂ : (0 : V₁ × V₂) ∈ (φ₁.prod φ₂).source := by
    rw [OpenPartialHomeomorph.prod_source]
    exact ⟨h0₁, h0₂⟩
  let e₁ := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of k k) φ₁ h0₁
  let e₂ := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of k k) φ₂ h0₂
  let e₁₂ := singularCohomologyComplSingletonFinrankEquivSelf (ModuleCat.of k k) (φ₁.prod φ₂) h0₁₂
  -- Pair the product of the dual generators with the homology cross product of the local
  -- homology generators.
  let x₁ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of k k) φ₁ h0₁).inv.hom (1 : k)
  let x₂ := (singularHomologyComplSingletonFinrankIso (ModuleCat.of k k) φ₂ h0₂).inv.hom (1 : k)
  let z := (complZeroPairHomologyCross V₁ V₂ v (Module.finrank ℝ E₁) (Module.finrank ℝ E₂)
    (Module.finrank ℝ (E₁ × E₂)) h).hom (x₁ ⊗ₜ[k] x₂)
  have hx₁ : ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₁))).singularKronecker
      (R := ModuleCat.of k k) (M := ModuleCat.of k k) k (Module.finrank ℝ E₁)
      (e₁.symm (1 : k))).hom x₁ = (1 : k) := by
    have h₁ := singularCohomologyComplSingletonFinrankEquivSelf_apply (ModuleCat.of k k) φ₁ h0₁
      (e₁.symm (1 : k))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
    exact h₁.symm.trans (e₁.apply_symm_apply (1 : k))
  have hx₂ : ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of V₂))).singularKronecker
      (R := ModuleCat.of k k) (M := ModuleCat.of k k) k (Module.finrank ℝ E₂)
      (e₂.symm (1 : k))).hom x₂ = (1 : k) := by
    have h₂ := singularCohomologyComplSingletonFinrankEquivSelf_apply (ModuleCat.of k k) φ₂ h0₂
      (e₂.symm (1 : k))
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at h₂
    exact h₂.symm.trans (e₂.apply_symm_apply (1 : k))
  let g₀ := complZeroPairCross k V₁ V₂ u μ _ _ _ h (e₁.symm (1 : k)) (e₂.symm (1 : k))
  have hpair : ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
      (R := ModuleCat.of k k) (M := ModuleCat.of k k) k (Module.finrank ℝ (E₁ × E₂))
      g₀).hom z = μ.hom ((1 : k) ⊗ₜ[k] (1 : k)) := by
    have hk := congrArg (fun f ↦ f.hom (x₁ ⊗ₜ[k] x₂))
      (complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross k V₁ V₂ hu μ _ _ _ h
        (e₁.symm (1 : k)) (e₂.symm (1 : k)))
    dsimp only [g₀, z] at hk ⊢
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hk
    rw [hk, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom,
      TensorProduct.map_tmul, hx₁, hx₂]
  let Ψ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ (E₁ × E₂)) →ₗ[k] k :=
    { toFun α := (↑hμ.unit⁻¹ : k) *
        ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := ModuleCat.of k k) (M := ModuleCat.of k k) k (Module.finrank ℝ (E₁ × E₂)) α).hom z
      map_add' α β := by rw [map_add, ModuleCat.hom_add, LinearMap.add_apply, mul_add]
      map_smul' c α := by
        rw [map_smul, ModuleCat.hom_smul, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
          smul_eq_mul, mul_left_comm] }
  have hΨ : Ψ g₀ = 1 := by
    dsimp only [Ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [hpair]
    exact (congrArg ((↑hμ.unit⁻¹ : k) * ·) hμ.unit_spec.symm).trans hμ.unit.inv_mul
  have hunit₀ : IsUnit (e₁₂ g₀) := e₁₂.isUnit_apply_of_apply_eq_one Ψ hΨ
  -- Express arbitrary classes as scalar multiples of the dual generators.
  have hg₁ : g₁ = e₁ g₁ • e₁.symm (1 : k) := by
    rw [← map_smul, smul_eq_mul, mul_one, e₁.symm_apply_apply]
  have hg₂ : g₂ = e₂ g₂ • e₂.symm (1 : k) := by
    rw [← map_smul, smul_eq_mul, mul_one, e₂.symm_apply_apply]
  have he₁₂ : e₁₂ (complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂) = (e₁ g₁ * e₂ g₂) * e₁₂ g₀ := by
    have hcross : complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂ = (e₁ g₁ * e₂ g₂) • g₀ := by
      conv_lhs => rw [hg₁, hg₂]
      simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm (e₂ g₂), g₀]
    rw [hcross, map_smul, smul_eq_mul]
  rw [e₁₂.span_singleton_eq_top_iff_isUnit, e₁.span_singleton_eq_top_iff_isUnit,
    e₂.span_singleton_eq_top_iff_isUnit, he₁₂, ← hunit₀.unit_spec, Units.isUnit_mul_units]
  exact ⟨fun h' ↦ ⟨isUnit_of_mul_isUnit_left h', isUnit_of_mul_isUnit_right h'⟩,
    fun ⟨ha, hb⟩ ↦ ha.mul hb⟩

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators**, for any diagonal `u` with left inverse `v` and unit-valued pairing `μ`. -/
theorem span_complZeroPairCross_eq_top_iff_of_isUnit {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {v : ModuleCat.of k k ⊗ ModuleCat.of k k ⟶ ModuleCat.of k k}
    {u : ModuleCat.of k k ⟶ ModuleCat.of k k ⊗ ModuleCat.of k k}
    (hu : v ≫ u = 𝟙 (ModuleCat.of k k ⊗ ModuleCat.of k k))
    {μ : ModuleCat.of k k ⊗ ModuleCat.of k k ⟶ ModuleCat.of k k}
    (hμ : IsUnit (μ.hom ((1 : k) ⊗ₜ[k] (1 : k))))
    {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)) :
    Submodule.span k {(complZeroPairCross k F₁ F₂ u μ _ _ _ h g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph (OpenPartialHomeomorph.refl F₁)
    (mem_univ 0) (OpenPartialHomeomorph.refl F₂) (mem_univ 0) hu hμ h g₁ g₂

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators** for the standard unitor pairings of `ModuleCat k` over any commutative ring `k`. -/
theorem span_complZeroPairCross_eq_top_iff {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)) :
    Submodule.span k {(complZeroPairCross k F₁ F₂ (λ_ (ModuleCat.of k k)).inv
        (λ_ (ModuleCat.of k k)).hom _ _ _ h g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ := by
  refine span_complZeroPairCross_eq_top_iff_of_isUnit (Iso.hom_inv_id (λ_ (ModuleCat.of k k))) ?_
    h g₁ g₂
  rw [ModuleCat.hom_hom_leftUnitor, LinearEquiv.coe_coe, TensorProduct.lid_tmul, one_smul]
  exact isUnit_one

/-- Over any commutative ring `k`, the local cross product of generators of
`H^{dim F₁}(F₁, F₁ ∖ {0})` and `H^{dim F₂}(F₂, F₂ ∖ {0})` generates
`H^{dim F₁ + dim F₂}(F₁ × F₂, (F₁ × F₂) ∖ {0})`. -/
theorem span_complZeroPairCross_eq_top {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    {g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁)}
    {g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)}
    (hg₁ : Submodule.span k {g₁} = ⊤) (hg₂ : Submodule.span k {g₂} = ⊤) :
    Submodule.span k {(complZeroPairCross k F₁ F₂ (λ_ (ModuleCat.of k k)).inv
      (λ_ (ModuleCat.of k k)).hom _ _ _ h g₁ g₂)} = ⊤ :=
  (span_complZeroPairCross_eq_top_iff h g₁ g₂).2 ⟨hg₁, hg₂⟩

end SpanEqTop

end TauCeti
