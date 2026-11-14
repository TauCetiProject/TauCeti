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
# The cross product of local cohomology classes

For `T₁` topological spaces `V₁` and `V₂` and points `x₁ : V₁` and `x₂ : V₂`, a point of `V₁ × V₂`
is distinct from `(x₁, x₂)` if and only if it differs from `x₁` in its first component or from `x₂`
in its second component (`TauCeti.compl_singleton_prod_eq`), so the pair
`(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)})` receives the relative cup product
(`TopCat.singularRelativeCupPullback`) of classes pulled back along the two projections:

`Hᵖ(V₁, V₁ ∖ {x₁}) × H^q(V₂, V₂ ∖ {x₂}) ⟶ Hᵖ⁺^q(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)})`

(`TauCeti.complSingletonPairCross`). It is natural in continuous maps carrying `{x₁}ᶜ` into `{y₁}ᶜ`
and `{x₂}ᶜ` into `{y₂}ᶜ` (`TauCeti.complSingletonPairCross_naturality`) — in particular under
products of continuous linear equivalences at `0`
(`TauCeti.complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom`) — and pairs
multiplicatively with `TauCeti.complSingletonPairHomologyCross`
(`TauCeti.complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross`).

At Euclidean chart points `x₁ ∈ φ₁.source` and `x₂ ∈ φ₂.source`, when the chain and value modules
over a commutative ring `k` are isomorphic to `k` (`Rᵢ ≃ₗ[k] k`, `Mᵢ ≃ₗ[k] k`) and
`u : R₃ ⟶ R₁ ⊗ R₂`, `μ : M₁ ⊗ M₂ ⟶ M₃` are isomorphisms — in particular for scalar coefficients
`ModuleCat.of k k` with the standard unitor pairings — `TauCeti.complSingletonPairCross` produces a
top-degree generator if and only if both factors generate.

## Main definitions

* `TauCeti.complSingletonPairCross`: the product of local classes of the pairs `(V₁, V₁ ∖ {x₁})` and
  `(V₂, V₂ ∖ {x₂})`, a class of `(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)})`.

## Main results

* `TauCeti.complSingletonPairCross_naturality` and
  `TauCeti.complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom`: naturality of the
  product under singleton-complement maps and products of continuous linear equivalences.
* `TauCeti.complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross`:
  Kronecker multiplicativity `⟨g₁ × g₂, z₁ × z₂⟩ = μ (⟨g₁, z₁⟩ ⊗ ⟨g₂, z₂⟩)`.
* `TauCeti.span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso`
  and `TauCeti.span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso` (with ring-valued
  specialization `TauCeti.span_complSingletonPairCross_eq_top_iff`): generator preservation and
  reflection for coefficient modules isomorphic to `k` and isomorphism pairings `u`, `μ`.

## References

* A. Hatcher, *Algebraic Topology*, Section 3.2 (relative cross products).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Princeton (1974), §10.
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Set

universe w v u

namespace TauCeti

section ComplSingletonPairCross

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C]
  [MonoidalLinear k C]

/-- **The product of local classes of the pairs `(V, V ∖ {x})`.** For `T₁` spaces `V₁` and `V₂` and
points `x₁ : V₁` and `x₂ : V₂`, this is the pairing
`Hᵖ(V₁, V₁ ∖ {x₁}; R, M) × H^q(V₂, V₂ ∖ {x₂}; S, N) ⟶ Hⁿ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T, L)`,
`p + q = n`, sending `(g₁, g₂)` to the relative cup product of their pull-backs along the two
projections (`TopCat.singularRelativeCupPullback`). -/
def complSingletonPairCross {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂] (x₁ : V₁) (x₂ : V₂) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂))
          ({(x₁, x₂)}ᶜ : Set (V₁ × V₂))).singularCohomology T k L n :=
  TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
    (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
    isOpen_compl_singleton (compl_singleton_prod_subset x₁ x₂) p q n h

theorem complSingletonPairCross_def {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂] (x₁ : V₁) (x₂ : V₂) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n) :
    complSingletonPairCross k x₁ x₂ u μ p q n h =
      TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) isOpen_compl_singleton
        isOpen_compl_singleton (compl_singleton_prod_subset x₁ x₂) p q n h :=
  (rfl)

/-- **Naturality of `complSingletonPairCross`** in continuous maps `g₁ : V₁ ⟶ W₁` and `g₂ : V₂ ⟶ W₂`
carrying `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`. -/
theorem complSingletonPairCross_naturality {V₁ V₂ W₁ W₂ : Type w}
    [TopologicalSpace V₁] [T1Space V₁] [TopologicalSpace V₂] [T1Space V₂]
    [TopologicalSpace W₁] [T1Space W₁] [TopologicalSpace W₂] [T1Space W₂]
    {x₁ : V₁} {x₂ : V₂} {y₁ : W₁} {y₂ : W₂}
    (g₁ : TopCat.of V₁ ⟶ TopCat.of W₁) (g₂ : TopCat.of V₂ ⟶ TopCat.of W₂)
    (hg₁ : Set.MapsTo g₁ ({x₁}ᶜ : Set V₁) ({y₁}ᶜ : Set W₁))
    (hg₂ : Set.MapsTo g₂ ({x₂}ᶜ : Set V₂) ({y₂}ᶜ : Set W₂))
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (a₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({y₁}ᶜ : Set W₁)).singularCohomology R k M p)
    (a₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({y₂}ᶜ : Set W₂)).singularCohomology S k N q) :
    complSingletonPairCross k x₁ x₂ u μ p q n h
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap g₁ hg₁) p a₁)
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap g₂ hg₂) q a₂) =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
          (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) n
        (complSingletonPairCross k y₁ y₂ u μ p q n h a₁ a₂) := by
  have hZ (x : V₁ × V₂) (hx : x ∈ ({(x₁, x₂)}ᶜ : Set (V₁ × V₂))) :
      g₁ x.1 ∈ ({y₁}ᶜ : Set W₁) ∨ g₂ x.2 ∈ ({y₂}ᶜ : Set W₂) :=
    (compl_singleton_prod_subset x₁ x₂ hx).imp (fun h ↦ hg₁ h) (fun h ↦ hg₂ h)
  rw [complSingletonPairCross_def, complSingletonPairCross_def]
  refine (TopCat.singularRelativeCupPullback_singularCohomologyMap k u μ _ _ _ _
    isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton isOpen_compl_singleton
    _ _ _ ?hZ₁ p q n h a₁ a₂).trans ?_
  case hZ₁ => exact fun x hx ↦ hZ x hx
  refine Eq.trans ?_ (TopCat.singularCohomologyMap_singularRelativeCupPullback k u μ _ _ _ _ _ _
    _ ?hZ₂ p q n h a₁ a₂).symm
  case hZ₂ => exact fun x hx ↦ hZ x hx
  have h₁ : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) ≫ g₁ =
      (g₁ ⊗ₘ g₂) ≫ TopCat.ofHom (ContinuousMap.fst : C(W₁ × W₂, W₁)) :=
    TopCat.ext fun _ ↦ rfl
  have h₂ : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) ≫ g₂ =
      (g₁ ⊗ₘ g₂) ≫ TopCat.ofHom (ContinuousMap.snd : C(W₁ × W₂, W₂)) :=
    TopCat.ext fun _ ↦ rfl
  simp only [h₁, h₂]
  rfl

end ComplSingletonPairCross

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

/-- **Naturality of the product of local classes at `0` under product equivalences.** For continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`, the product, for `V₁ × V₂`, of the
pull-backs along `f₁` and `f₂` of classes `g₁ ∈ Hᵖ(W₁, W₁ ∖ {0})` and `g₂ ∈ H^q(W₂, W₂ ∖ {0})` is
the pull-back along `f₁ × f₂` of their product for `W₁ × W₂`. -/
theorem complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom (u : T ⟶ R ⊗ S)
    (μ : M ⊗ N ⟶ L) (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (p q n : ℕ) (h : p + q = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({0}ᶜ : Set W₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({0}ᶜ : Set W₂)).singularCohomology S k N q) :
    complSingletonPairCross k (0 : V₁) (0 : V₂) u μ p q n h
        (TopPair.singularCohomologyMap f₁.complZeroPairIso.hom p g₁)
        (TopPair.singularCohomologyMap f₂.complZeroPairIso.hom q g₂) =
      TopPair.singularCohomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom n
        (complSingletonPairCross k (0 : W₁) (0 : W₂) u μ p q n h g₁ g₂) := by
  let φ₁ : TopCat.of V₁ ⟶ TopCat.of W₁ := TopCat.ofHom ((f₁ : V₁ →L[𝕜] W₁) : C(V₁, W₁))
  let φ₂ : TopCat.of V₂ ⟶ TopCat.of W₂ := TopCat.ofHom ((f₂ : V₂ →L[𝕜] W₂) : C(V₂, W₂))
  have hprod : TopPair.ofSubsetMap (φ₁ ⊗ₘ φ₂)
      (TopCat.mapsTo_tensorHom_compl_singleton φ₁ φ₂ f₁.mapsTo_compl_zero f₂.mapsTo_compl_zero) =
      (f₁.prodCongr f₂).complZeroPairIso.hom := by
    rw [(f₁.prodCongr f₂).complZeroPairIso_hom]
    exact TopPair.hom_ext_of_fst _ (TopCat.ext fun _ ↦ rfl)
  rw [f₁.complZeroPairIso_hom, f₂.complZeroPairIso_hom, ← hprod]
  exact complSingletonPairCross_naturality k φ₁ φ₂ f₁.mapsTo_compl_zero f₂.mapsTo_compl_zero
    u μ p q n h g₁ g₂

end LinearEquiv

section ComplSingletonPairHomologyCross

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R S T M N L : C} (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

/-- **Kronecker multiplicativity of local cross products**: when `v ≫ u = 𝟙 (R ⊗ S)`, evaluating
`complSingletonPairCross` via `TopPair.singularKronecker` on `complSingletonPairHomologyCross` gives
the tensor product of the relative Kronecker evaluations followed by `μ`. -/
theorem complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂] (x₁ : V₁) (x₂ : V₂)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    (p q n : ℕ) (h : p + q = n)
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q) :
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := T) (M := L) k n (complSingletonPairCross k x₁ x₂ u μ p q n h g₁ g₂) =
      ((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularKronecker (R := R) (M := M) k p g₁ ⊗ₘ
        (TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularKronecker (R := S) (M := N) k q
          g₂) ≫ μ := by
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) =
      CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  have hsnd : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) =
      CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  simp only [complSingletonPairHomologyCross_def, complSingletonPairCross_def, hfst, hsnd]
  refine (Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans ?_)
  exact TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback
    (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton isOpen_compl_singleton
    (compl_singleton_prod_subset x₁ x₂) (subset_compl_singleton_prod x₁ x₂) hu μ p q n h g₁ g₂

/-- **Off-diagonal vanishing for local cross products**: when `p ≠ p'` and `v ≫ u = 𝟙 (R ⊗ S)`,
`complSingletonPairCross` in bidegree `(p', q')` evaluates to zero under `TopPair.singularKronecker`
on `complSingletonPairHomologyCross` in bidegree `(p, q)`. -/
theorem complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross_of_ne
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂] (x₁ : V₁) (x₂ : V₂)
    {v : R ⊗ S ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = 𝟙 (R ⊗ S)) (μ : M ⊗ N ⟶ L)
    {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R).homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S).cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S).X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p')
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q') :
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := T) (M := L) k n (complSingletonPairCross k x₁ x₂ u μ p' q' n h' g₁ g₂) = 0 := by
  have hfst : TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)) =
      CartesianMonoidalCategory.fst (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  have hsnd : TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)) =
      CartesianMonoidalCategory.snd (TopCat.of V₁) (TopCat.of V₂) := TopCat.ext fun _ ↦ rfl
  simp only [complSingletonPairHomologyCross_def, complSingletonPairCross_def, hfst, hsnd]
  refine (Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans ?_)
  exact
    TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne
      (TopCat.of V₁) (TopCat.of V₂) isOpen_compl_singleton isOpen_compl_singleton
      (compl_singleton_prod_subset x₁ x₂) (subset_compl_singleton_prod x₁ x₂) hu μ h h' hp g₁ g₂

end ComplSingletonPairHomologyCross

section SpanEqTop

/-- The local cross product of dual chart generators maps to a unit under the product chart. -/
private lemma isUnit_complSingletonPairCross_symm_one {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) {x₁ : V₁} (hx₁ : x₁ ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) {x₂ : V₂} (hx₂ : x₂ ∈ φ₂.source)
    (hx₁₂ : (x₁, x₂) ∈ (φ₁.prod φ₂).source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ] :
    let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₁ hx₁ eR₁ eM₁
    let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₂ hx₂ eR₂ eM₂
    let e₁₂ :=
      singularCohomologyComplSingletonFinrankEquivOfLinearEquiv (φ₁.prod φ₂) hx₁₂ eR₃ eM₃
    IsUnit (e₁₂ (complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
      (e₁.symm 1) (e₂.symm 1))) := by
  have : Module.Projective k R₁ := Module.Projective.of_equiv eR₁.symm
  have : Module.Projective k R₂ := Module.Projective.of_equiv eR₂.symm
  let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₁ hx₁ eR₁ eM₁
  let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₂ hx₂ eR₂ eM₂
  let e₁₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv (φ₁.prod φ₂) hx₁₂ eR₃ eM₃
  let z₁ := (singularHomologyComplSingletonFinrankIso R₁ φ₁ hx₁).inv.hom (eR₁.symm 1)
  let z₂ := (singularHomologyComplSingletonFinrankIso R₂ φ₂ hx₂).inv.hom (eR₂.symm 1)
  let z := (complSingletonPairHomologyCross x₁ x₂ (inv u) (Module.finrank ℝ E₁)
    (Module.finrank ℝ E₂) (Module.finrank ℝ (E₁ × E₂)) Module.finrank_prod.symm).hom (z₁ ⊗ₜ[k] z₂)
  let g₀ := complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
    (e₁.symm 1) (e₂.symm 1)
  have hpair : ((TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
      (Module.finrank ℝ (E₁ × E₂)) g₀).hom z = μ.hom (eM₁.symm 1 ⊗ₜ[k] eM₂.symm 1) := by
    have hk := congrArg (fun f ↦ f.hom (z₁ ⊗ₜ[k] z₂))
      (complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross k x₁ x₂
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
  let Ψ : (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularCohomology R₃ k M₃
      (Module.finrank ℝ (E₁ × E₂)) →ₗ[k] k :=
    ψ.comp ((LinearMap.applyₗ z).comp (ModuleCat.homLinearEquiv.toLinearMap.comp
      ((TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
        (Module.finrank ℝ (E₁ × E₂)))))
  refine e₁₂.isUnit_apply_of_apply_eq_one Ψ ?_
  simp only [Ψ, ψ, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.applyₗ_apply_apply,
    ModuleCat.homLinearEquiv_apply, AddEquiv.toFun_eq_coe, ModuleCat.homAddEquiv_apply]
  rw [hpair, ← LinearMap.comp_apply (inv μ).hom μ.hom, ← ModuleCat.hom_comp,
    IsIso.hom_inv_id, ModuleCat.hom_id, LinearMap.id_apply, TensorProduct.map_tmul,
    LinearEquiv.coe_coe, eM₁.apply_symm_apply, LinearEquiv.coe_coe, eM₂.apply_symm_apply,
    TensorProduct.lid_tmul, one_smul]

/-- **Local cross products preserve and reflect generators at Euclidean chart points** for
coefficient modules isomorphic to `k` (`Rᵢ ≃ₗ[k] k`, `Mᵢ ≃ₗ[k] k`) and isomorphism pairings
`u : R₃ ⟶ R₁ ⊗ R₂`, `μ : M₁ ⊗ M₂ ⟶ M₃`. -/
theorem span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso
    {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) {x₁ : V₁} (hx₁ : x₁ ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) {x₂ : V₂} (hx₂ : x₂ ∈ φ₂.source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {n : ℕ} (h : Module.finrank ℝ E₁ + Module.finrank ℝ E₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ E₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ E₂)) :
    Submodule.span k {complSingletonPairCross k x₁ x₂ u μ _ _ _ h g₁ g₂} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ := by
  have hn : n = Module.finrank ℝ (E₁ × E₂) := h.symm.trans Module.finrank_prod.symm
  subst hn
  have hx₁₂ : (x₁, x₂) ∈ (φ₁.prod φ₂).source := by
    rw [OpenPartialHomeomorph.prod_source]
    exact ⟨hx₁, hx₂⟩
  let e₁ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₁ hx₁ eR₁ eM₁
  let e₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv φ₂ hx₂ eR₂ eM₂
  let e₁₂ := singularCohomologyComplSingletonFinrankEquivOfLinearEquiv (φ₁.prod φ₂) hx₁₂ eR₃ eM₃
  let g₀ := complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
    (e₁.symm 1) (e₂.symm 1)
  have hunit₀ : IsUnit (e₁₂ g₀) :=
    isUnit_complSingletonPairCross_symm_one eR₁ eR₂ eR₃ eM₁ eM₂ eM₃ φ₁ hx₁ φ₂ hx₂ hx₁₂
  have hg₁ : g₁ = e₁ g₁ • e₁.symm 1 := by simp [← map_smul]
  have hg₂ : g₂ = e₂ g₂ • e₂.symm 1 := by simp [← map_smul]
  have he₁₂ : e₁₂ (complSingletonPairCross k x₁ x₂ u μ _ _ _ h g₁ g₂) =
      (e₁ g₁ * e₂ g₂) * e₁₂ g₀ := by
    have hcross : complSingletonPairCross k x₁ x₂ u μ _ _ _ h g₁ g₂ = (e₁ g₁ * e₂ g₂) • g₀ := by
      conv_lhs => rw [hg₁, hg₂]
      simp only [map_smul, LinearMap.smul_apply, smul_smul, mul_comm (e₂ g₂), g₀]
    rw [hcross, map_smul, smul_eq_mul]
  simp only [e₁₂.span_singleton_eq_top_iff_isUnit, e₁.span_singleton_eq_top_iff_isUnit,
    e₂.span_singleton_eq_top_iff_isUnit, he₁₂, IsUnit.mul_iff, hunit₀, and_true]

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators**, for coefficient modules isomorphic to `k` and isomorphism pairings `u` and `μ`. -/
theorem span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eR₃ : R₃ ≃ₗ[k] k)
    (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k) (eM₃ : M₃ ≃ₗ[k] k)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ F₂)) :
    Submodule.span k {complSingletonPairCross k x₁ x₂ u μ _ _ _ h g₁ g₂} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso
    eR₁ eR₂ eR₃ eM₁ eM₂ eM₃
    (OpenPartialHomeomorph.refl F₁) (mem_univ x₁) (OpenPartialHomeomorph.refl F₂) (mem_univ x₂)
    h g₁ g₂

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators** for scalar coefficients `ModuleCat.of k k` with the standard unitor pairings. -/
theorem span_complSingletonPairCross_eq_top_iff {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ (λ_ (ModuleCat.of k k)).inv
        (λ_ (ModuleCat.of k k)).hom _ _ _ h g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso
    (.refl k k) (.refl k k) (.refl k k) (.refl k k) (.refl k k) (.refl k k) h g₁ g₂

/-- Over any commutative ring `k`, `complSingletonPairCross` of top-degree local generators
generates. -/
theorem span_complSingletonPairCross_eq_top {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    {g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁)}
    {g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)}
    (hg₁ : Submodule.span k {g₁} = ⊤) (hg₂ : Submodule.span k {g₂} = ⊤) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ (λ_ (ModuleCat.of k k)).inv
      (λ_ (ModuleCat.of k k)).hom _ _ _ h g₁ g₂)} = ⊤ :=
  (span_complSingletonPairCross_eq_top_iff h g₁ g₂).2 ⟨hg₁, hg₂⟩

end SpanEqTop

end TauCeti
