/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Comparison.Excision
public import TauCeti.AlgebraicTopology.Singular.LocalHomology.BoundaryFundamentalClass
import TauCeti.Algebra.Category.ModuleCat.SpanSingleton
import TauCeti.AlgebraicTopology.Singular.LocalHomology.Dense

/-!
# Generators of local cubical homology

The local homology of a manifold is computed by singular chains, while relative cycles such as the
fundamental chains of compactified trajectory spaces are cubical. This file reads three facts about
generators of local singular homology through the comparison isomorphisms between relative cubical
and relative singular homology
(`TopPair.singularCubicalHomologyIso`).

## Main results

* `TauCeti.span_homologyMap_cubicalHomologyδ_eq_top`: the boundary of a relative class generating
  at the interior points generates the local cubical homology of a collared boundary, the cubical
  form of `TauCeti.isFundamentalClass_singularHomologyδ_of_forall_span_eq_top`.
* `TauCeti.span_homologyMap_cubicalChainComplexMap_eq_top`: a class generating at an interior
  point, carried along a map that is an open embedding on the interior and sends the boundary off
  the image of that point, generates the local cubical homology there.
* `TauCeti.eq_of_span_cubicalHomology_eq_top`: the local cubical homology of a manifold in top
  degree has a single generator when `1` is the only unit of the coefficients, the cubical form of
  `TauCeti.eq_of_span_localHomology_eq_top`.
* `TauCeti.homologyMap_cubicalChainComplexMap_eq_zero_of_isPreconnected`: the local classes of a
  relative cubical class along an open set vanish on a preconnected subset as soon as they vanish
  at one of its points, the cubical form of
  `TauCeti.localHomologyRestriction_eq_zero_of_isPreconnected`.
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
    (S := range j) hcol (n := m)
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

/-- **A class generating at an interior point, carried along a map that is an open embedding
there, generates.** Let `j : N → X` be an open embedding into a `T₁` space and let `μ` be a class
of the relative cubical homology `Hₙ(X, X ∖ j(N); k)` whose image in the local homology
`Hₙ(X, X ∖ {j r}; k)` generates it. Let `g : X → Y` be a map into a `T₁` space such that `g ∘ j`
is an open embedding and `g` sends `X ∖ j(N)` off `g (j r)`. Then the image of `μ` under `g` in
the local cubical homology `Hₙ(Y, Y ∖ {g (j r)}; k)` generates it. -/
theorem span_homologyMap_cubicalChainComplexMap_eq_top {X : TopCat.{u}} [T1Space X] {N : Type u}
    [TopologicalSpace N] {j : N → X} (hj : IsOpenEmbedding j) {Y : Type u} [TopologicalSpace Y]
    [T1Space Y] {n : ℕ} (μ : ((TopPair.ofSubset (range j)ᶜ).cubicalChainComplex k).homology n)
    (g : C(X, Y)) (hg : IsOpenEmbedding (g ∘ j)) (r : N)
    (hμ : (k ∙ localHomologyRestriction (ModuleCat.of k k)
      (singleton_subset_iff.2 (mem_range_self r)) n
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (range j)ᶜ) n).inv.hom μ)) = ⊤)
    (h : MapsTo (TopCat.ofHom (X := X) g) (range j)ᶜ {g (j r)}ᶜ) :
    (k ∙ (HomologicalComplex.homologyMap (cubicalChainComplexMap k (ofSubsetMap _ h)) n).hom μ) =
      ⊤ := by
  -- `g` sends every point other than `j r` off `g (j r)`: the points off the image of `j` by `h`,
  -- the other points of the image by injectivity of `g ∘ j`.
  have h' : g ⁻¹' {g (j r)} ⊆ {j r} := by
    intro x hx
    by_cases hxj : x ∈ range j
    · obtain ⟨s, rfl⟩ := hxj
      exact congrArg j (hg.injective hx)
    · exact (h hxj hx).elim
  -- The local homology of `X` at `j r` maps isomorphically to that of `Y` at `g (j r)`.
  have hiso := isIso_localHomologyMap_singleton_of_isOpenEmbedding_comp (ModuleCat.of k k)
    (j := ⟨j, hj.continuous⟩) hj g hg r h' n
  rw [localHomologyMap_def] at hiso
  have hx : MapsTo (𝟙 X) (range j)ᶜ ({j r}ᶜ : Set X) :=
    compl_subset_compl.2 (singleton_subset_iff.2 (mem_range_self r))
  -- The map of pairs induced by `g` factors through the local pair of `X` at `j r`.
  have hfac : ofSubsetMap (TopCat.ofHom (X := X) g) h = ofSubsetMap (𝟙 X) hx ≫
      ofSubsetMap (X := TopCat.of X) (Y := TopCat.of Y) (B := ({j r} : Set X)ᶜ)
        (B' := ({g (j r)} : Set Y)ᶜ) (TopCat.ofHom g)
        ((mapsTo_preimage _ _).mono_left (compl_subset_compl.2 h')) :=
    (ofSubsetMap_comp_ofSubsetMap_of_comp_eq _ _ h (Category.id_comp _)).symm
  refine (ModuleCat.span_singleton_apply_eq_top_iff (TopPair.singularCubicalHomologyIso k
    (TopPair.ofSubset (X := TopCat.of Y) {g (j r)}ᶜ) n).inv).1 ?_
  rw [← ModuleCat.comp_apply, TopPair.singularCubicalHomologyIso_inv_naturality, hfac,
    TopPair.singularHomologyMap_comp, ModuleCat.comp_apply, ModuleCat.comp_apply,
    ModuleCat.span_singleton_apply_eq_top_iff]
  rw [localHomologyRestriction_def] at hμ
  exact hμ

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

/-- **The local classes of a cubical class along an open set vanish on whole preconnected sets.**
Let `Y` be a manifold, `U ⊆ Y` open, `θ` a class of the relative cubical homology
`Hₘ(Y, Y ∖ U; k)`, and `S ⊆ U` preconnected. If the image of `θ` in the local cubical homology
`Hₘ(Y, Y ∖ {x}; k)` vanishes at one point `x` of `S`, it vanishes at every point of `S`. This is the
cubical form of `TauCeti.localHomologyRestriction_eq_zero_of_isPreconnected`. -/
theorem homologyMap_cubicalChainComplexMap_eq_zero_of_isPreconnected {Y : Type u}
    [TopologicalSpace Y] [T2Space Y] {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [ChartedSpace E Y] {U S : Set Y} (hU : IsOpen U)
    (hS : IsPreconnected S) (hSU : S ⊆ U) {m : ℕ}
    {θ : ((TopPair.ofSubset (X := TopCat.of Y) Uᶜ).cubicalChainComplex k).homology m}
    {x y : Y} (hx : x ∈ S) (hy : y ∈ S)
    (hθ : (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
      (TopPair.ofSubsetMap (𝟙 (TopCat.of Y))
        (compl_subset_compl.2 (singleton_subset_iff.2 (hSU hx))))) m).hom θ = 0) :
    (HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
      (TopPair.ofSubsetMap (𝟙 (TopCat.of Y))
        (compl_subset_compl.2 (singleton_subset_iff.2 (hSU hy))))) m).hom θ = 0 := by
  -- Through the comparison with singular homology, the cubical local classes of `θ` are the
  -- singular local classes of its singular counterpart.
  have key (z : Y) (hz : z ∈ U) :
      (TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of Y) {z}ᶜ) m).inv.hom
        ((HomologicalComplex.homologyMap (TopPair.cubicalChainComplexMap k
          (TopPair.ofSubsetMap (𝟙 (TopCat.of Y))
            (compl_subset_compl.2 (singleton_subset_iff.2 hz)))) m).hom θ) =
      localHomologyRestriction (ModuleCat.of k k) (singleton_subset_iff.2 hz) m
        ((TopPair.singularCubicalHomologyIso k (TopPair.ofSubset (X := TopCat.of Y) Uᶜ) m).inv.hom
          θ) := by
    rw [localHomologyRestriction_def]
    exact congr(($(TopPair.singularCubicalHomologyIso_inv_naturality k
      (TopPair.ofSubsetMap (𝟙 (TopCat.of Y))
        (compl_subset_compl.2 (singleton_subset_iff.2 hz))) m)).hom θ)
  apply (ModuleCat.mono_iff_injective (TopPair.singularCubicalHomologyIso k
    (TopPair.ofSubset (X := TopCat.of Y) {y}ᶜ) m).inv).1 inferInstance
  refine ((key y (hSU hy)).trans ?_).trans (map_zero _).symm
  refine localHomologyRestriction_eq_zero_of_isPreconnected (E := E) _ hU hS hSU hx hy ?_
  rw [← key x (hSU hx), hθ, map_zero]

end TauCeti
