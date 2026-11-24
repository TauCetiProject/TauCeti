/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.BoundaryFundamentalClass
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton

/-!
# Generators of local cubical homology

The local homology of a manifold is computed by singular chains, while relative cycles such as the
fundamental chains of compactified trajectory spaces are cubical. This file reads two facts about
generators of local singular homology through the comparison isomorphisms between relative cubical
and relative singular homology
(`TopPair.singularCubicalHomologyIso`).

## Main results

* `TauCeti.span_homologyMap_cubicalHomologyδ_eq_top`: the boundary of a relative class generating
  at the interior points generates the local cubical homology of a collared boundary, the cubical
  form of `TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`.
* `TauCeti.eq_of_span_cubicalHomology_eq_top`: the local cubical homology of a manifold in top
  degree has a single generator when `1` is the only unit of the coefficients, the cubical form of
  `TauCeti.eq_of_span_localHomology_eq_top`.
-/

public section

noncomputable section

open CategoryTheory Limits Module Set Topology TopPair HomologicalComplex

universe u

namespace TauCeti

variable {k : Type u} [Ring k]

/-- **The boundary of a class generating at the interior points generates the local homology of
the boundary.** Let `j : N → X` have collared complement `∂X = X ∖ j(N)` in a Hausdorff space `X`,
and let `μ` be a class of the relative cubical homology `Hₙ(X, ∂X; k)` whose image in the local
homology `Hₙ(X, X ∖ {j q}; k)` generates it at every point `q` of `N`. Then for `m + 1 = n` the
image of the boundary `∂ μ ∈ Hₘ(∂X; k)` in the local cubical homology `Hₘ(∂X, ∂X ∖ {a}; k)`
generates it at every point `a` of `∂X`. This is the cubical form of
`TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`. -/
theorem span_homologyMap_cubicalHomologyδ_eq_top {X : TopCat.{u}} [T2Space X] {N : Type u}
    {j : N → X} (hcol : IsCollared (Subtype.val : ↥(range j)ᶜ → X))
    {n m : ℕ} (hnm : m + 1 = n)
    (μ : ((TopPair.ofSubset (range j)ᶜ).cubicalChainComplex k).homology n)
    (hμ : ∀ q : N, (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self q)) n
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) n).inv.hom μ)) = ⊤)
    (a : ↥(range j)ᶜ) :
    (k ∙ (HomologicalComplex.homologyMap (cokernel.π
      ((normalizedCubicalChainComplex k).map (TopPair.ofSubset ({a}ᶜ : Set ↥(range j)ᶜ)).map))
        m).hom (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k n m hnm).hom μ)) = ⊤ := by
  subst hnm
  have hδ := isFundamentalClass_singularHomologyδ_of_forall_span_eq_top (ModuleCat.of k k)
    (ι := j) (f := Subtype.val) (by rw [Subtype.range_coe, compl_compl]) hcol (n := m)
    (γ := (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) (m + 1)).inv.hom μ)
    (by rintro _ ⟨q, rfl⟩; exact hμ q)
  -- Read through the cubical–singular comparisons, the image of `∂ μ` at `a` is the image at `a`
  -- of the singular boundary, a fundamental class of `∂X`.
  refine (ModuleCat.span_singleton_apply_eq_top_iff (TopPair.singularCubicalHomologyIso k
    (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ) m).inv).1 ?_
  have e₁ : HomologicalComplex.homologyMap (cokernel.π ((normalizedCubicalChainComplex k).map
        (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ).map)) m ≫
        (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ)
          m).inv = (singularCubicalHomologyIso k (TopCat.of ↥(range j)ᶜ) m).inv ≫
        (TopPair.ofSubset (X := TopCat.of ↥(range j)ᶜ) {a}ᶜ).singularHomologyπ
          (ModuleCat.of k k) m :=
      TopPair.homologyMap_π_comp_singularCubicalHomologyIso_inv k _ m
  have e₂ : (TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k (m + 1) m rfl ≫
        (singularCubicalHomologyIso k (TopCat.of ↥(range j)ᶜ) m).inv =
        (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) (m + 1)).inv ≫
          (TopPair.ofSubset (range j)ᶜ).singularHomologyδ (ModuleCat.of k k) (m + 1) m rfl :=
      (TopPair.singularCubicalHomologyIso_inv_singularHomologyδ k _ (m + 1) m rfl).symm
  have h₁ := congr(($e₁).hom
    (((TopPair.ofSubset (range j)ᶜ).cubicalHomologyδ k (m + 1) m rfl).hom μ))
  have h₂ := congr(($e₂).hom μ)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h₁ h₂
  -- The two images of `∂ μ` agree only up to unfolding the ambient spaces of the pairs, so they
  -- are identified by a term rather than by `rw`.
  refine (congrArg (k ∙ ·) ?_).trans ((isFundamentalClass_iff _).1 hδ a)
  exact h₁.trans ((congrArg _ h₂).trans
    (singularHomologyToLocalHomology_eq_singularHomologyπ _ a _).symm)

/-- **The local cubical homology of a manifold has a single generator when `1` is the only unit
of the coefficients.** On a manifold `Y` of dimension `m`, with coefficients in a ring `k` whose
only unit is `1` and in which one-sided inverses are inverses, two generators of the local cubical
homology `Hₘ(Y, Y ∖ {a}; k) ≅ k` are equal. This is the cubical form of
`TauCeti.eq_of_span_localHomology_eq_top`. -/
theorem eq_of_span_cubicalHomology_eq_top [IsDedekindFiniteMonoid k] [Subsingleton kˣ] {Y : Type u}
    [TopologicalSpace Y]
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [ChartedSpace E Y] {m : ℕ} (hm : finrank ℝ E = m) (a : Y)
    {v w : ((TopPair.ofSubset (X := TopCat.of Y) {a}ᶜ).cubicalChainComplex k).homology m}
    (hv : k ∙ v = ⊤) (hw : k ∙ w = ⊤) : v = w := by
  have hinj := (ModuleCat.mono_iff_injective
    (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of Y) {a}ᶜ) m).inv).1
      inferInstance
  exact hinj (eq_of_span_localHomology_eq_top k hm
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hv)
    ((ModuleCat.span_singleton_apply_eq_top_iff _).2 hw))

end TauCeti
