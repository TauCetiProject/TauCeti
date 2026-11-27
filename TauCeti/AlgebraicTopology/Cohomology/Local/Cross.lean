/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Equiv.SpanSingleton
public import TauCeti.AlgebraicTopology.Cohomology.Cup.Kronecker
public import TauCeti.AlgebraicTopology.Cohomology.Local.Basic
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.Cross

/-!
# The cross product of local cohomology classes

For spaces `V₁` and `V₂` and points `x₁ : V₁`, `x₂ : V₂` with `{x₁}ᶜ` and `{x₂}ᶜ` open (in
particular in `T₁` spaces), `p : V₁ × V₂` is distinct from `(x₁, x₂)` iff `p.1 ≠ x₁` or
`p.2 ≠ x₂` (`Set.compl_singleton_prodMk_eq_union`), so `(V₁ × V₂, {(x₁, x₂)}ᶜ)` receives the
relative cup product (`TopCat.singularRelativeCupPullback`) of classes pulled back along the two
projections:

`Hᵖ(V₁, V₁ ∖ {x₁}) × H^q(V₂, V₂ ∖ {x₂}) ⟶ Hᵖ⁺^q(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)})`

(`TauCeti.complSingletonPairCross`). It is natural in singleton-complement maps
(`TauCeti.complSingletonPairCross_naturality`) and continuous linear equivalences at `0`
(`ContinuousLinearEquiv.complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom`), and
when `v ≫ u = φ ⊗ₘ ψ` (`v : R' ⊗ S' ⟶ T`, `u : T ⟶ R ⊗ S`, `φ : R' ⟶ R`, `ψ : S' ⟶ S`) it pairs
multiplicatively with `TauCeti.complSingletonPairHomologyCross`
(`TauCeti.complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross`). For
open partial homeomorphisms `φ₁ : OpenPartialHomeomorph V₁ E₁` and
`φ₂ : OpenPartialHomeomorph V₂ E₂` from `T₁` spaces `V₁`, `V₂` into finite-dimensional real normed
spaces `E₁`, `E₂`, at chart points `xᵢ ∈ φᵢ.source` with `R₁, R₂, M₁, M₂ ≃ₗ[k] k`, isomorphisms
`u, μ`, and input classes in the chart-target dimensions `Module.finrank ℝ E₁` and
`Module.finrank ℝ E₂`, it produces a generator in degree
`n = Module.finrank ℝ E₁ + Module.finrank ℝ E₂` iff both factors generate.

## Main definitions

* `TauCeti.complSingletonPairCross`: local cross product of `(V₁, {x₁}ᶜ)` and `(V₂, {x₂}ᶜ)`.

## Main results

* `TauCeti.complSingletonPairCross_naturality`,
  `ContinuousLinearEquiv.complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom`:
  naturality.
* `TauCeti.complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross`:
  Kronecker multiplicativity when `v ≫ u = φ ⊗ₘ ψ`.
* Generator preservation and reflection:
`span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso`
  and its corollaries
  `TauCeti.span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso`
  and `TauCeti.span_singleton_complSingletonPairCross_eq_top_iff`.

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

/-- **The product of local classes of the pairs `(V, V ∖ {x})`.** For spaces `V₁` and `V₂` and
points `x₁ : V₁` and `x₂ : V₂` with open complements `{x₁}ᶜ` and `{x₂}ᶜ`, this is the pairing
`Hᵖ(V₁, V₁ ∖ {x₁}; R, M) × H^q(V₂, V₂ ∖ {x₂}; S, N) ⟶ Hⁿ(V₁ × V₂, (V₁ × V₂) ∖ {(x₁, x₂)}; T, L)`,
`p + q = n`, sending `(g₁, g₂)` to the relative cup product of their pull-backs along the two
projections (`TopCat.singularRelativeCupPullback`). -/
def complSingletonPairCross {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂]
    (x₁ : V₁) (x₂ : V₂) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (hx₁ : IsOpen ({x₁}ᶜ : Set V₁)) (hx₂ : IsOpen ({x₂}ᶜ : Set V₂)) :
    (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p →ₗ[k]
      (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q →ₗ[k]
        (TopPair.ofSubset (X := TopCat.of (V₁ × V₂))
          ({(x₁, x₂)}ᶜ : Set (V₁ × V₂))).singularCohomology T k L n :=
  TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
    (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) hx₁ hx₂
    (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset p q n h

theorem complSingletonPairCross_def {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂]
    (x₁ : V₁) (x₂ : V₂) (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (hx₁ : IsOpen ({x₁}ᶜ : Set V₁)) (hx₂ : IsOpen ({x₂}ᶜ : Set V₂)) :
    complSingletonPairCross k x₁ x₂ u μ p q n h hx₁ hx₂ =
      TopCat.singularRelativeCupPullback k u μ (TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
        (TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂))) hx₁ hx₂
        (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset p q n h :=
  (rfl)

/-- **Naturality of `complSingletonPairCross`** in continuous maps `g₁ : V₁ ⟶ W₁` and `g₂ : V₂ ⟶ W₂`
carrying `{x₁}ᶜ` into `{y₁}ᶜ` and `{x₂}ᶜ` into `{y₂}ᶜ`. -/
theorem complSingletonPairCross_naturality {V₁ V₂ W₁ W₂ : Type w}
    [TopologicalSpace V₁] [TopologicalSpace V₂] [TopologicalSpace W₁] [TopologicalSpace W₂]
    {x₁ : V₁} {x₂ : V₂} {y₁ : W₁} {y₂ : W₂}
    (g₁ : TopCat.of V₁ ⟶ TopCat.of W₁) (g₂ : TopCat.of V₂ ⟶ TopCat.of W₂)
    (hg₁ : Set.MapsTo g₁ ({x₁}ᶜ : Set V₁) ({y₁}ᶜ : Set W₁))
    (hg₂ : Set.MapsTo g₂ ({x₂}ᶜ : Set V₂) ({y₂}ᶜ : Set W₂))
    (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (hx₁ : IsOpen ({x₁}ᶜ : Set V₁)) (hx₂ : IsOpen ({x₂}ᶜ : Set V₂))
    (hy₁ : IsOpen ({y₁}ᶜ : Set W₁)) (hy₂ : IsOpen ({y₂}ᶜ : Set W₂))
    (a₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({y₁}ᶜ : Set W₁)).singularCohomology R k M p)
    (a₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({y₂}ᶜ : Set W₂)).singularCohomology S k N q) :
    complSingletonPairCross k x₁ x₂ u μ p q n h hx₁ hx₂
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap g₁ hg₁) p a₁)
        (TopPair.singularCohomologyMap (TopPair.ofSubsetMap g₂ hg₂) q a₂) =
      TopPair.singularCohomologyMap
        (TopPair.ofSubsetMap (g₁ ⊗ₘ g₂)
          (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)) n
        (complSingletonPairCross k y₁ y₂ u μ p q n h hy₁ hy₂ a₁ a₂) := by
  rw [complSingletonPairCross_def, complSingletonPairCross_def]
  exact TopCat.singularRelativeCupPullback_naturality k u μ
    (f₁ := TopCat.ofHom (ContinuousMap.fst : C(V₁ × V₂, V₁)))
    (f₂ := TopCat.ofHom (ContinuousMap.snd : C(V₁ × V₂, V₂)))
    (f₁' := TopCat.ofHom (ContinuousMap.fst : C(W₁ × W₂, W₁)))
    (f₂' := TopCat.ofHom (ContinuousMap.snd : C(W₁ × W₂, W₂)))
    (g₁ ⊗ₘ g₂) g₁ g₂
    (TopCat.ext fun _ ↦ rfl) (TopCat.ext fun _ ↦ rfl) hx₁ hx₂ hy₁ hy₂
    (TopCat.mapsTo_tensorHom_compl_singleton g₁ g₂ hg₁ hg₂)
    (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset
    (Set.compl_singleton_prodMk_eq_union y₁ y₂).subset p q n h a₁ a₂

end ComplSingletonPairCross

section ComplSingletonPairHomologyCross

open CartesianMonoidalCategory

attribute [local instance] hasFiniteCoproducts_of_hasCoproducts
attribute [local instance] HasFiniteBiproducts.of_hasFiniteCoproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorLeft X)]
  [∀ (X : C) (J : Type w), PreservesColimitsOfShape (Discrete J) (tensorRight X)]
  {R' S' R S T M N L : C} (k : Type*) [CommRing k] [Linear k C] [MonoidalLinear k C]

private lemma complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross_eq
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂] (x₁ : V₁) (x₂ : V₂)
    {v : R' ⊗ S' ⟶ T} {u : T ⟶ R ⊗ S} (μ : M ⊗ N ⟶ L)
    {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n)
    (hx₁ : IsOpen ({x₁}ᶜ : Set V₁)) (hx₂ : IsOpen ({x₂}ᶜ : Set V₂))
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S').X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p')
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q')
    {rhs : (TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularHomology R' p ⊗
        (TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularHomology S' q ⟶ L}
    (hrhs : TopCat.singularRelativeHomologyCross (TopCat.of V₁) (TopCat.of V₂) R' S'
          ({x₁}ᶜ : Set (TopCat.of V₁)) ({x₂}ᶜ : Set (TopCat.of V₂)) p q n h ≫
        (TopPair.ofSubset (fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
          snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹'
            ({x₂}ᶜ : Set V₂))).singularHomologyCoefficientMap v n ≫
        TopPair.singularHomologyMap (TopPair.ofSubsetMap (𝟙 (TopCat.of V₁ ⊗ TopCat.of V₂))
          (B := fst (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₁}ᶜ : Set V₁) ∪
            snd (TopCat.of V₁) (TopCat.of V₂) ⁻¹' ({x₂}ᶜ : Set V₂))
          (B' := ({(x₁, x₂)}ᶜ : Set _))
          (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset) T n ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set ↥(TopCat.of V₁ ⊗ TopCat.of V₂))).singularKronecker
          (R := T) (M := L) k n
          (TopCat.singularRelativeCupPullback k u μ
            (fst (TopCat.of V₁) (TopCat.of V₂))
            (snd (TopCat.of V₁) (TopCat.of V₂)) hx₁ hx₂
            (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset p' q' n h' g₁ g₂) = rhs) :
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := T) (M := L) k n (complSingletonPairCross k x₁ x₂ u μ p' q' n h' hx₁ hx₂ g₁ g₂) =
      rhs := by
  simp only [complSingletonPairHomologyCross_def, complSingletonPairCross_def,
    TopCat.ofHom_fst, TopCat.ofHom_snd]
  exact (Category.assoc _ _ _).trans ((whisker_eq _ (Category.assoc _ _ _)).trans hrhs)

/-- **Kronecker multiplicativity of local cross products**: when `v : R' ⊗ S' ⟶ T` and
`u : T ⟶ R ⊗ S` satisfy `v ≫ u = φ ⊗ₘ ψ` (`φ : R' ⟶ R`, `ψ : S' ⟶ S`) and `{x₁}ᶜ`, `{x₂}ᶜ` are
open, evaluating `complSingletonPairCross` via `TopPair.singularKronecker` on
`complSingletonPairHomologyCross` precomposes the factor Kronecker evaluations with the homology
coefficient maps induced by `φ` and `ψ` and composes with `μ`. -/
theorem complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂] (x₁ : V₁) (x₂ : V₂)
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {v : R' ⊗ S' ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = φ ⊗ₘ ψ)
    (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n) (hx₁ : IsOpen ({x₁}ᶜ : Set V₁))
    (hx₂ : IsOpen ({x₂}ᶜ : Set V₂))
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S').X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q) :
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := T) (M := L) k n (complSingletonPairCross k x₁ x₂ u μ p q n h hx₁ hx₂ g₁ g₂) =
      (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularHomologyCoefficientMap φ p ≫
          (TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularKronecker (R := R) (M := M) k p
            g₁) ⊗ₘ
        ((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularHomologyCoefficientMap ψ q ≫
          (TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularKronecker (R := S) (M := N) k q
            g₂)) ≫ μ := by
  refine complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross_eq
    k x₁ x₂ μ h h hx₁ hx₂ g₁ g₂ ?_
  rw [TopPair.singularHomologyCoefficientMap_def]
  exact TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback
    (TopCat.of V₁) (TopCat.of V₂) hx₁ hx₂
    (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset
    (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset hu μ p q n h g₁ g₂

/-- **Off-diagonal vanishing for local cross products**: when `p ≠ p'`, `v ≫ u = φ ⊗ₘ ψ`, and
`{x₁}ᶜ`, `{x₂}ᶜ` are open, `complSingletonPairCross` in bidegree `(p', q')` evaluates to zero under
`TopPair.singularKronecker` on `complSingletonPairHomologyCross` in bidegree `(p, q)`. -/
theorem complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross_of_ne
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [TopologicalSpace V₂] (x₁ : V₁) (x₂ : V₂)
    {φ : R' ⟶ R} {ψ : S' ⟶ S} {v : R' ⊗ S' ⟶ T} {u : T ⟶ R ⊗ S} (hu : v ≫ u = φ ⊗ₘ ψ)
    (μ : M ⊗ N ⟶ L) {p q p' q' n : ℕ} (h : p + q = n) (h' : p' + q' = n) (hp : p ≠ p')
    (hx₁ : IsOpen ({x₁}ᶜ : Set V₁)) (hx₂ : IsOpen ({x₂}ᶜ : Set V₂))
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorLeft (((TopPair.ofSubset ({x₁}ᶜ : Set (TopCat.of V₁))).singularChainComplex
        R').homology p))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex
        S').cycles q))]
    [PreservesColimitsOfShape WalkingParallelPair
      (tensorRight (((TopPair.ofSubset ({x₂}ᶜ : Set (TopCat.of V₂))).singularChainComplex S').X
        ((ComplexShape.down ℕ).prev q)))]
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology R k M p')
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology S k N q') :
    complSingletonPairHomologyCross x₁ x₂ v p q n h ≫
        (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker
          (R := T) (M := L) k n
          (complSingletonPairCross k x₁ x₂ u μ p' q' n h' hx₁ hx₂ g₁ g₂) = 0 := by
  refine complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross_eq
    k x₁ x₂ μ h h' hx₁ hx₂ g₁ g₂ ?_
  rw [TopPair.singularHomologyCoefficientMap_def]
  exact
    TopCat.singularRelativeHomologyCross_comp_singularKronecker_singularRelativeCupPullback_of_ne
      (TopCat.of V₁) (TopCat.of V₂) hx₁ hx₂
      (Set.compl_singleton_prodMk_eq_union x₁ x₂).subset
      (Set.compl_singleton_prodMk_eq_union x₁ x₂).superset hu μ h h' hp g₁ g₂

end ComplSingletonPairHomologyCross

section SpanEqTop

private lemma kronecker_eval_comp_apply
    {k : Type w} [CommRing k] {R₃ M₃ : ModuleCat.{w} k}
    (P : TopPair.{w}) (n : ℕ) (z : ↑(P.singularHomology R₃ n)) (vM : M₃ →ₗ[k] k)
    (g : P.singularCohomology R₃ k M₃ n) :
    (vM.comp ((LinearMap.applyₗ z).comp
      (ModuleCat.homLinearEquiv.toLinearMap.comp (P.singularKronecker k n)))) g =
      vM ((P.singularKronecker k n g).hom z) := by
  simp [LinearMap.comp_apply, LinearMap.applyₗ_apply_apply]

private lemma span_singleton_complSingletonPairCross_symm_one_eq_top
    {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) {x₁ : V₁} (hx₁ : x₁ ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) {x₂ : V₂} (hx₂ : x₂ ∈ φ₂.source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    (e₁₂ : (TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularCohomology
      R₃ k M₃ (Module.finrank ℝ (E₁ × E₂)) ≃ₗ[k] k) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
      isOpen_compl_singleton isOpen_compl_singleton
      ((φ₁.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₁ eR₁ eM₁).symm 1)
      ((φ₂.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₂ eR₂ eM₂).symm
        1))} = ⊤ := by
  rw [e₁₂.span_singleton_eq_top_iff_isUnit]
  let z₁ := (singularHomologyComplSingletonFinrankIso R₁ φ₁ hx₁).inv.hom (eR₁.symm 1)
  let z₂ := (singularHomologyComplSingletonFinrankIso R₂ φ₂ hx₂).inv.hom (eR₂.symm 1)
  let z := (complSingletonPairHomologyCross x₁ x₂ (inv u) (Module.finrank ℝ E₁)
    (Module.finrank ℝ E₂) (Module.finrank ℝ (E₁ × E₂)) Module.finrank_prod.symm).hom
    (z₁ ⊗ₜ[k] z₂)
  let g₀ := complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
    isOpen_compl_singleton isOpen_compl_singleton
    ((φ₁.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₁ eR₁ eM₁).symm 1)
    ((φ₂.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₂ eR₂ eM₂).symm 1)
  have hpair : ((TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
      (Module.finrank ℝ (E₁ × E₂)) g₀).hom z = μ.hom (eM₁.symm 1 ⊗ₜ[k] eM₂.symm 1) := by
    have hk := congrArg (fun f ↦ f.hom (z₁ ⊗ₜ[k] z₂))
      (complSingletonPairHomologyCross_comp_singularKronecker_complSingletonPairCross k x₁ x₂
        ((IsIso.inv_hom_id u).trans (MonoidalCategory.id_tensorHom_id R₁ R₂).symm) μ _ _ _
        Module.finrank_prod.symm isOpen_compl_singleton isOpen_compl_singleton
        ((φ₁.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₁ eR₁ eM₁).symm 1)
        ((φ₂.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₂ eR₂ eM₂).symm 1))
    simp only [z₁, z₂, TopPair.singularHomologyCoefficientMap_id, Category.id_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_tensorHom] at hk
    open OpenPartialHomeomorph in
    rw [TensorProduct.map_tmul,
      singularKronecker_singularCohomologyComplSingletonFinrankEquivOfLinearEquiv_symm,
      singularKronecker_singularCohomologyComplSingletonFinrankEquivOfLinearEquiv_symm] at hk
    exact hk
  let vM : M₃ →ₗ[k] k :=
    (TensorProduct.congr eM₁ eM₂ ≪≫ₗ TensorProduct.lid k k).toLinearMap ∘ₗ (inv μ).hom
  refine e₁₂.isUnit_apply_of_apply_eq_one (vM.comp ((LinearMap.applyₗ z).comp
    (ModuleCat.homLinearEquiv.toLinearMap.comp
      ((TopPair.ofSubset ({(x₁, x₂)}ᶜ : Set (TopCat.of (V₁ × V₂)))).singularKronecker k
        (Module.finrank ℝ (E₁ × E₂)))))) ?_
  rw [kronecker_eval_comp_apply, hpair]
  have hinv : (inv μ).hom (μ.hom (eM₁.symm 1 ⊗ₜ[k] eM₂.symm 1)) = eM₁.symm 1 ⊗ₜ[k] eM₂.symm 1 :=
    ConcreteCategory.congr_hom (IsIso.hom_inv_id μ) _
  simp [vM, hinv]

/-- **Local cross products preserve and reflect generators at chart points in `T₁` spaces** for
open partial homeomorphisms `φ₁ : OpenPartialHomeomorph V₁ E₁`,
`φ₂ : OpenPartialHomeomorph V₂ E₂` into finite-dimensional real normed spaces `E₁`, `E₂`, with
input classes in the chart-target dimensions `Module.finrank ℝ E₁` and `Module.finrank ℝ E₂`
(summing to `n`), equivalences `R₁, R₂, M₁, M₂ ≃ₗ[k] k`, and isomorphism pairings
`u : R₃ ⟶ R₁ ⊗ R₂`, `μ : M₁ ⊗ M₂ ⟶ M₃`. -/
theorem
  span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso
    {k : Type w} [CommRing k]
    {V₁ V₂ : Type w} [TopologicalSpace V₁] [T1Space V₁]
    [TopologicalSpace V₂] [T1Space V₂]
    {E₁ E₂ : Type w} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k)
    (φ₁ : OpenPartialHomeomorph V₁ E₁) {x₁ : V₁} (hx₁ : x₁ ∈ φ₁.source)
    (φ₂ : OpenPartialHomeomorph V₂ E₂) {x₂ : V₂} (hx₂ : x₂ ∈ φ₂.source)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {n : ℕ} (h : Module.finrank ℝ E₁ + Module.finrank ℝ E₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of V₁) ({x₁}ᶜ : Set V₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ E₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of V₂) ({x₂}ᶜ : Set V₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ E₂)) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ u μ _ _ _ h
        isOpen_compl_singleton isOpen_compl_singleton g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ := by
  have hn : n = Module.finrank ℝ (E₁ × E₂) := h.symm.trans Module.finrank_prod.symm
  subst hn
  have hx₁₂ : (x₁, x₂) ∈ (φ₁.prod φ₂).source := by
    rw [OpenPartialHomeomorph.prod_source]; exact ⟨hx₁, hx₂⟩
  let eR₃ : R₃ ≃ₗ[k] k :=
    (asIso u).toLinearEquiv ≪≫ₗ TensorProduct.congr eR₁ eR₂ ≪≫ₗ TensorProduct.lid k k
  let eM₃ : M₃ ≃ₗ[k] k :=
    (asIso μ).symm.toLinearEquiv ≪≫ₗ TensorProduct.congr eM₁ eM₂ ≪≫ₗ TensorProduct.lid k k
  let e₁₂ := (φ₁.prod φ₂).singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₁₂ eR₃ eM₃
  exact LinearEquiv.span_singleton_bilinear_eq_top_iff_of_span_eq_top
    (φ₁.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₁ eR₁ eM₁)
    (φ₂.singularCohomologyComplSingletonFinrankEquivOfLinearEquiv hx₂ eR₂ eM₂)
    e₁₂
    (complSingletonPairCross k x₁ x₂ u μ _ _ _ Module.finrank_prod.symm
      isOpen_compl_singleton isOpen_compl_singleton)
    (span_singleton_complSingletonPairCross_symm_one_eq_top eR₁ eR₂ eM₁ eM₂ φ₁ hx₁ φ₂ hx₂ e₁₂)
    g₁ g₂

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators** for `R₁, R₂, M₁, M₂ ≃ₗ[k] k` and isomorphism pairings `u` and `μ`. -/
theorem span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso
    {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {R₁ R₂ R₃ M₁ M₂ M₃ : ModuleCat.{w} k}
    (eR₁ : R₁ ≃ₗ[k] k) (eR₂ : R₂ ≃ₗ[k] k) (eM₁ : M₁ ≃ₗ[k] k) (eM₂ : M₂ ≃ₗ[k] k)
    {u : R₃ ⟶ R₁ ⊗ R₂} [IsIso u] {μ : M₁ ⊗ M₂ ⟶ M₃} [IsIso μ]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      R₁ k M₁ (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      R₂ k M₂ (Module.finrank ℝ F₂)) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ u μ _ _ _ h
        isOpen_compl_singleton isOpen_compl_singleton g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_openPartialHomeomorph_of_isIso
    eR₁ eR₂ eM₁ eM₂ (OpenPartialHomeomorph.refl F₁) (mem_univ x₁)
    (OpenPartialHomeomorph.refl F₂) (mem_univ x₂) h g₁ g₂

/-- **Local cross products on finite-dimensional real normed spaces preserve and reflect
generators** for `ModuleCat.of k k` with standard unitors. -/
@[simp]
theorem span_singleton_complSingletonPairCross_eq_top_iff {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    (g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁))
    (g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ (λ_ (ModuleCat.of k k)).inv
        (λ_ (ModuleCat.of k k)).hom _ _ _ h
        isOpen_compl_singleton isOpen_compl_singleton g₁ g₂)} = ⊤ ↔
      Submodule.span k {g₁} = ⊤ ∧ Submodule.span k {g₂} = ⊤ :=
  span_singleton_complSingletonPairCross_eq_top_iff_of_linearEquiv_of_isIso
    (.refl k k) (.refl k k) (.refl k k) (.refl k k) h g₁ g₂

/-- On finite-dimensional real normed spaces, `complSingletonPairCross` of top-degree local
generators generates over any `CommRing k`. -/
theorem span_singleton_complSingletonPairCross_eq_top {k : Type w} [CommRing k]
    {F₁ F₂ : Type w} [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [FiniteDimensional ℝ F₁]
    [NormedAddCommGroup F₂] [NormedSpace ℝ F₂] [FiniteDimensional ℝ F₂]
    {x₁ : F₁} {x₂ : F₂} {n : ℕ} (h : Module.finrank ℝ F₁ + Module.finrank ℝ F₂ = n)
    {g₁ : (TopPair.ofSubset (X := TopCat.of F₁) ({x₁}ᶜ : Set F₁)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₁)}
    {g₂ : (TopPair.ofSubset (X := TopCat.of F₂) ({x₂}ᶜ : Set F₂)).singularCohomology
      (ModuleCat.of k k) k (ModuleCat.of k k) (Module.finrank ℝ F₂)}
    (hg₁ : Submodule.span k {g₁} = ⊤) (hg₂ : Submodule.span k {g₂} = ⊤) :
    Submodule.span k {(complSingletonPairCross k x₁ x₂ (λ_ (ModuleCat.of k k)).inv
      (λ_ (ModuleCat.of k k)).hom _ _ _ h
      isOpen_compl_singleton isOpen_compl_singleton g₁ g₂)} = ⊤ :=
  (span_singleton_complSingletonPairCross_eq_top_iff h g₁ g₂).2 ⟨hg₁, hg₂⟩

end SpanEqTop

end TauCeti

namespace ContinuousLinearEquiv

open TauCeti (complSingletonPairCross complSingletonPairCross_naturality)

variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{w} C] [MonoidalCategory C]
  [MonoidalPreadditive C] {R S T M N L : C}
  {𝕜 : Type*} [Semiring 𝕜] {V₁ V₂ W₁ W₂ : Type w}
  [TopologicalSpace V₁] [AddCommMonoid V₁] [Module 𝕜 V₁]
  [TopologicalSpace V₂] [AddCommMonoid V₂] [Module 𝕜 V₂]
  [TopologicalSpace W₁] [AddCommMonoid W₁] [Module 𝕜 W₁]
  [TopologicalSpace W₂] [AddCommMonoid W₂] [Module 𝕜 W₂]

/-- **Naturality of the product of local classes at `0` under product equivalences.** For continuous
linear equivalences `f₁ : V₁ ≃L W₁` and `f₂ : V₂ ≃L W₂`, the product, for `V₁ × V₂`, of the
pull-backs along `f₁` and `f₂` of classes `g₁ ∈ Hᵖ(W₁, W₁ ∖ {0})` and `g₂ ∈ H^q(W₂, W₂ ∖ {0})` is
the pull-back along `f₁ × f₂` of their product for `W₁ × W₂`. -/
theorem complSingletonPairCross_singularCohomologyMap_complZeroPairIso_hom
    (f₁ : V₁ ≃L[𝕜] W₁) (f₂ : V₂ ≃L[𝕜] W₂) (k : Type*) [CommRing k] [Linear k C]
    [MonoidalLinear k C] (u : T ⟶ R ⊗ S) (μ : M ⊗ N ⟶ L) (p q n : ℕ) (h : p + q = n)
    (hxV₁ : IsOpen ({0}ᶜ : Set V₁)) (hxV₂ : IsOpen ({0}ᶜ : Set V₂))
    (hxW₁ : IsOpen ({0}ᶜ : Set W₁)) (hxW₂ : IsOpen ({0}ᶜ : Set W₂))
    (g₁ : (TopPair.ofSubset (X := TopCat.of W₁) ({0}ᶜ : Set W₁)).singularCohomology R k M p)
    (g₂ : (TopPair.ofSubset (X := TopCat.of W₂) ({0}ᶜ : Set W₂)).singularCohomology S k N q) :
    complSingletonPairCross k (0 : V₁) (0 : V₂) u μ p q n h hxV₁ hxV₂
        (TopPair.singularCohomologyMap f₁.complZeroPairIso.hom p g₁)
        (TopPair.singularCohomologyMap f₂.complZeroPairIso.hom q g₂) =
      TopPair.singularCohomologyMap (f₁.prodCongr f₂).complZeroPairIso.hom n
        (complSingletonPairCross k (0 : W₁) (0 : W₂) u μ p q n h hxW₁ hxW₂ g₁ g₂) := by
  rw [f₁.complZeroPairIso_hom, f₂.complZeroPairIso_hom, f₁.prodCongr_complZeroPairIso_hom f₂]
  exact complSingletonPairCross_naturality k _ _ f₁.mapsTo_compl_zero f₂.mapsTo_compl_zero
    u μ p q n h hxV₁ hxV₂ hxW₁ hxW₂ g₁ g₂

end ContinuousLinearEquiv
