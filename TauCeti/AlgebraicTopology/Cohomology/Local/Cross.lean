/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Closed.Braided

/-!
# The cross product of local classes at the origin

For spaces `V₁` and `V₂` with a zero and closed points, such as finite-dimensional real vector
spaces, a vector of `V₁ × V₂` is nonzero only if one of its components is, so the pair
`(V₁ × V₂, (V₁ × V₂) ∖ {0})` receives the relative cup product
(`TopCat.singularRelativeCupPullback`) of classes pulled back along the two projections:

`Hᵖ(V₁, V₁ ∖ {0}) × H^q(V₂, V₂ ∖ {0}) ⟶ Hᵖ⁺^q(V₁ × V₂, (V₁ × V₂) ∖ {0})`

(`TauCeti.complZeroPairCross`). It is natural under products of continuous linear equivalences
(`TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`), and pairs
multiplicatively with `TauCeti.complZeroPairHomologyCross`
(`TauCeti.complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross`). At Euclidean
chart origins, when the chain and value modules over a commutative ring `k` are isomorphic to `k`
(`Rᵢ ≃ₗ[k] k`, `Mᵢ ≃ₗ[k] k`) and `u : R₃ ⟶ R₁ ⊗ R₂`, `μ : M₁ ⊗ M₂ ⟶ M₃` are isomorphisms — in
particular for scalar coefficients `ModuleCat.of k k` with the standard unitor pairings —
`TauCeti.complZeroPairCross` produces a top-degree generator if and only if both factors generate.

## Main definitions

* `TauCeti.complZeroPairCross`: the product of classes of the pairs `(V₁, V₁ ∖ {0})` and
  `(V₂, V₂ ∖ {0})`, a class of `(V₁ × V₂, (V₁ × V₂) ∖ {0})`.

## Main results

* `TauCeti.complZeroPairCross_singularCohomologyMap_complZeroPairIso_hom`: naturality of the
  product under products of continuous linear equivalences.
* `TauCeti.complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross`: Kronecker
  multiplicativity `⟨g₁ × g₂, x₁ × x₂⟩ = μ (⟨g₁, x₁⟩ ⊗ ⟨g₂, x₂⟩)` at the origin.
* `TauCeti.span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph`,
  `TauCeti.span_complZeroPairCross_eq_top_iff_of_isIso`,
  `TauCeti.span_complZeroPairCross_eq_top_iff`: generator preservation and reflection for
  coefficient modules isomorphic to `k` and isomorphism pairings `u`, `μ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2 (relative cross products).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set

universe w v u

namespace TauCeti

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
  {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

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
    (compl_zero_prod_subset V₁ V₂) (subset_compl_zero_prod V₁ V₂) hu μ p q n h g₁ g₂

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
      (compl_zero_prod_subset V₁ V₂) (subset_compl_zero_prod V₁ V₂) hu μ h h' hp g₁ g₂

end ComplZeroPairHomologyCross

section SpanEqTop

/-- Top-degree local cohomology `Hᵈ(V, V ∖ {x}; R, M)` at a Euclidean chart point identified with
`k` via `eR : R ≃ₗ[k] k` and `eM : M ≃ₗ[k] k`. -/
private def singularCohomologyComplSingletonFinrankEquivOfLinearEquiv {k : Type w} [CommRing k]
    {R M : ModuleCat.{w} k} (eR : R ≃ₗ[k] k) (eM : M ≃ₗ[k] k)
    {V : Type w} [TopologicalSpace V] [T1Space V] {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : OpenPartialHomeomorph V E) {x : V}
    (hx : x ∈ φ.source) :
    (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of V))).singularCohomology R k M
        (Module.finrank ℝ E) ≃ₗ[k] k :=
  haveI : Module.Projective k R := Module.Projective.of_equiv eR.symm
  singularCohomologyComplSingletonFinrankEquiv R M φ hx ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
    eR.arrowCongr eM ≪≫ₗ LinearMap.ringLmapEquivSelf k k k

/-- Kronecker pairing of `(singularCohomologyComplSingletonFinrankEquivOfLinearEquiv ...).symm r`
with the local homology generator `(singularHomologyComplSingletonFinrankIso R φ hx).inv` gives
`eM.symm r`. -/
private lemma singularKronecker_singularCohomologyComplSingletonFinrankEquivOfLinearEquiv_symm
    {k : Type w} [CommRing k] {R M : ModuleCat.{w} k} (eR : R ≃ₗ[k] k) (eM : M ≃ₗ[k] k)
    {V : Type w} [TopologicalSpace V] [T1Space V] {E : Type w} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] (φ : OpenPartialHomeomorph V E) {x : V}
    (hx : x ∈ φ.source) (r : k) :
    haveI : Module.Projective k R := Module.Projective.of_equiv eR.symm
    ((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of V))).singularKronecker k (Module.finrank ℝ E)
      ((singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR eM φ hx).symm r)).hom
        ((singularHomologyComplSingletonFinrankIso R φ hx).inv.hom (eR.symm 1)) =
      eM.symm r := by
  have : Module.Projective k R := Module.Projective.of_equiv eR.symm
  let e := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR eM φ hx
  have he : e (e.symm r) = eM (((TopPair.ofSubset ({x}ᶜ : Set (TopCat.of V))).singularKronecker k
      (Module.finrank ℝ E) (e.symm r)).hom
        ((singularHomologyComplSingletonFinrankIso R φ hx).inv.hom (eR.symm 1))) := by
    change (singularCohomologyComplSingletonFinrankEquiv R M φ hx ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
      eR.arrowCongr eM ≪≫ₗ LinearMap.ringLmapEquivSelf k k k) (e.symm r) = _
    rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
      singularCohomologyComplSingletonFinrankEquiv_apply, ModuleCat.homLinearEquiv_apply,
      LinearMap.ringLmapEquivSelf_apply]
    change (eR.arrowCongr eM) ((singularHomologyComplSingletonFinrankIso R φ hx).inv ≫
      (TopPair.ofSubset ({x}ᶜ : Set (TopCat.of V))).singularKronecker k (Module.finrank ℝ E)
        (e.symm r)).hom (1 : k) = _
    rw [LinearEquiv.arrowCongr_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  apply eM.injective
  rw [eM.apply_symm_apply, ← he, e.apply_symm_apply]

/-- The local cross product of dual chart generators maps to a unit under the product chart. -/
private lemma isUnit_complZeroPairCross_symm_one {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) (h0₁ : (0 : V₁) ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) (h0₂ : (0 : V₂) ∈ φ₂.source)
    (h0₁₂ : (0 : V₁ × V₂) ∈ (φ₁.prod φ₂).source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ] :
    let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₁ eM₁ φ₁ h0₁
    let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₂ eM₂ φ₂ h0₂
    let e₁₂ :=
      singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₃ eM₃ (φ₁.prod φ₂) h0₁₂
    IsUnit (e₁₂ (complZeroPairCross k V₁ V₂ u μ _ _ _ Module.finrank_prod.symm
      (e₁.symm 1) (e₂.symm 1))) := by
  have : Module.Projective k R₁ := Module.Projective.of_equiv eR₁.symm
  have : Module.Projective k R₂ := Module.Projective.of_equiv eR₂.symm
  let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₁ eM₁ φ₁ h0₁
  let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₂ eM₂ φ₂ h0₂
  let e₁₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₃ eM₃ (φ₁.prod φ₂) h0₁₂
  let x₁ := (singularHomologyComplSingletonFinrankIso R₁ φ₁ h0₁).inv.hom (eR₁.symm 1)
  let x₂ := (singularHomologyComplSingletonFinrankIso R₂ φ₂ h0₂).inv.hom (eR₂.symm 1)
  let z := (complZeroPairHomologyCross V₁ V₂ (inv u) (Module.finrank ℝ E₁) (Module.finrank ℝ E₂)
    (Module.finrank ℝ (E₁ × E₂)) Module.finrank_prod.symm).hom (x₁ ⊗ₜ[k] x₂)
  let g₀ := complZeroPairCross k V₁ V₂ u μ _ _ _ Module.finrank_prod.symm (e₁.symm 1) (e₂.symm 1)
  have hpair : ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
      (Module.finrank ℝ (E₁ × E₂)) g₀).hom z = μ.hom (eM₁.symm 1 ⊗ₜ[k] eM₂.symm 1) := by
    have hk := congrArg (fun f ↦ f.hom (x₁ ⊗ₜ[k] x₂))
      (complZeroPairHomologyCross_comp_singularKronecker_complZeroPairCross k V₁ V₂
        (IsIso.inv_hom_id u) μ _ _ _ Module.finrank_prod.symm (e₁.symm 1) (e₂.symm 1))
    dsimp only [g₀, z] at hk ⊢
    rw [ModuleCat.hom_comp, LinearMap.comp_apply] at hk
    rw [hk, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom,
      TensorProduct.map_tmul,
      singularKronecker_singularCohomologyComplSingletonFinrankEquivOfLinearEquiv_symm,
      singularKronecker_singularCohomologyComplSingletonFinrankEquivOfLinearEquiv_symm]
  let ψ : M₃ →ₗ[k] k :=
    (TensorProduct.lid k k).toLinearMap.comp
      ((TensorProduct.map eM₁.toLinearMap eM₂.toLinearMap).comp (inv μ).hom)
  let Ψ : (TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularCohomology R₃ k M₃
      (Module.finrank ℝ (E₁ × E₂)) →ₗ[k] k :=
    ψ.comp ((LinearMap.applyₗ z).comp (ModuleCat.homLinearEquiv.toLinearMap.comp
      ((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
        (Module.finrank ℝ (E₁ × E₂)))))
  refine e₁₂.isUnit_apply_of_apply_eq_one Ψ ?_
  change (TensorProduct.lid k k) ((TensorProduct.map eM₁.toLinearMap eM₂.toLinearMap)
    ((inv μ).hom (((TopPair.ofSubset ({0}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
      (Module.finrank ℝ (E₁ × E₂)) g₀).hom z))) = 1
  rw [hpair, ← LinearMap.comp_apply (inv μ).hom μ.hom, ← ModuleCat.hom_comp,
    IsIso.hom_inv_id, ModuleCat.hom_id, LinearMap.id_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, eM₁.apply_symm_apply, LinearEquiv.coe_coe, eM₂.apply_symm_apply,
    TensorProduct.lid_tmul, one_smul]

/-- **Local cross products preserve and reflect generators at Euclidean chart origins** for
coefficient modules isomorphic to `k` (`Rᵢ ≃ₗ[k] k`, `Mᵢ ≃ₗ[k] k`) and isomorphism pairings
`u : R₃ ⟶ R₁ ⊗ R₂`, `μ : M₁ ⊗ M₂ ⟶ M₃`. -/
theorem span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [Zero V₁] [T1Space V₁]
    [TopologicalSpace V₂] [Zero V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) (h0₁ : (0 : V₁) ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) (h0₂ : (0 : V₂) ∈ φ₂.source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {n : ℕ} (h : Module.finrank ℝ E₁ + Module.finrank ℝ E₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({0}ᶜ : Set V₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ E₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({0}ᶜ : Set V₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ E₂)) :
    Submodule.span k {complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ := by
  have hn : n = Module.finrank ℝ (E₁ × E₂) := h.symm.trans Module.finrank_prod.symm
  subst hn
  have h0₁₂ : (0 : V₁ × V₂) ∈ (φ₁.prod φ₂).source := by
    rw [OpenPartialHomeomorph.prod_source]
    exact ⟨h0₁, h0₂⟩
  let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₁ eM₁ φ₁ h0₁
  let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₂ eM₂ φ₂ h0₂
  let e₁₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv eR₃ eM₃ (φ₁.prod φ₂) h0₁₂
  let g₀ := complZeroPairCross k V₁ V₂ u μ _ _ _ Module.finrank_prod.symm (e₁.symm 1) (e₂.symm 1)
  have hunit₀ : IsUnit (e₁₂ g₀) :=
    isUnit_complZeroPairCross_symm_one eR₁ eR₂ eR₃ eM₁ eM₂ eM₃ φ₁ h0₁ φ₂ h0₂ h0₁₂
  have hg₁ : g₁ = e₁ g₁ • e₁.symm 1 := by simp [← map_smul]
  have hg₂ : g₂ = e₂ g₂ • e₂.symm 1 := by simp [← map_smul]
  have he₁₂ : e₁₂ (complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂) = (e₁ g₁ * e₂ g₂) * e₁₂ g₀ := by
    have hcross : complZeroPairCross k V₁ V₂ u μ _ _ _ h g₁ g₂ = (e₁ g₁ * e₂ g₂) • g₀ := by
      conv_lhs => rw [hg₁, hg₂]
      simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm (e₂ g₂), g₀]
    rw [hcross, map_smul, smul_eq_mul]
  simp only [e₁₂.span_singleton_eq_top_iff_isUnit, e₁.span_singleton_eq_top_iff_isUnit,
    e₂.span_singleton_eq_top_iff_isUnit, he₁₂, IsUnit.mul_iff, hunit₀, and_true]

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators**, for coefficient modules isomorphic to `k` and isomorphism pairings `u` and `μ`. -/
theorem span_complZeroPairCross_eq_top_iff_of_isIso {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({0}ᶜ : Set F₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({0}ᶜ : Set F₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ F₂)) :
    Submodule.span k {(complZeroPairCross k F₁ F₂ u μ _ _ _ h g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_complZeroPairCross_eq_top_iff_of_openPartialHomeomorph eR₁ eR₂ eR₃ eM₁ eM₂ eM₃
    (OpenPartialHomeomorph.refl F₁) (mem_univ 0) (OpenPartialHomeomorph.refl F₂) (mem_univ 0)
    h g₁ g₂

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators** for scalar coefficients `ModuleCat.of k k` with the standard unitor pairings. -/
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
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_complZeroPairCross_eq_top_iff_of_isIso (.refl k k) (.refl k k) (.refl k k)
    (.refl k k) (.refl k k) (.refl k k) h g₁ g₂

/-- Over any commutative ring `k`, `complZeroPairCross` of top-degree local generators generates. -/
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
