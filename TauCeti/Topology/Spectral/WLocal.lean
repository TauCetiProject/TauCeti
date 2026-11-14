/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Separation.DisjointCover
import TauCeti.Topology.Compactness.Compact
import TauCeti.Topology.Spectral.ConnectedComponents
import TauCeti.Topology.Spectral.PatchCriterion
import TauCeti.Topology.Spectral.ProConstructible

/-!
# Split open covers and w-local spectral spaces

In perfectoid and diamond geometry, disconnected covers replace arbitrary spectral spaces by spaces
whose connected components behave like single valuation rings parametrized by a profinite base.
Topologically, two conditions govern these covers:

1. `TauCeti.OpenCoversSplit`: every open cover `𝒰` of `X` admits a locally constant choice of a
   covering member `s x ∈ 𝒰` containing `x` (equivalently, the map `⨆_{U ∈ 𝒰} U → X` has a
   continuous section). On a spectral space `X`, Fargues' criterion (`TauCeti.openCoversSplit_iff`)
   characterizes this property purely in terms of connected components: every open cover splits if
   and only if every connected component of `X` contains a unique closed point. The backward
   implication pushes an open cover down to the profinite component quotient
   `ConnectedComponents X` (`TauCeti.t2Space_connectedComponents`) and refines the resulting cover
   there by pairwise disjoint clopens
   (`TopologicalSpace.IsOpenCover.exists_finite_nonempty_disjoint_clopen_cover`).
2. `TauCeti.IsWLocalSpace`: `X` is spectral, its open covers split, and the locus `closedPoints X`
   of closed points is closed in `X`. Under these conditions the closed points form a canonical
   profinite cross-section of the connected components: the restriction of `ConnectedComponents.mk`
   to `closedPoints X` is a homeomorphism onto `ConnectedComponents X`
   (`TauCeti.IsWLocalSpace.isHomeomorph_connectedComponentsMk`).

## Main definitions

* `TauCeti.OpenCoversSplit`: every open cover of `X` admits a locally constant member choice.
* `TauCeti.IsWLocalSpace`: `X` is spectral, `OpenCoversSplit X` holds, and `closedPoints X` is
  closed.
* `TauCeti.IsWLocalSpace.closedPointsHomeomorphConnectedComponents`: the canonical homeomorphism
  from `closedPoints X` to `ConnectedComponents X` for a w-local space.

## Main results

* `TauCeti.openCoversSplit_iff_isLocallyConstant`, `TauCeti.openCoversSplit_iff_iUnion`,
  `TauCeti.OpenCoversSplit.exists_isLocallyConstant_index`: set-cover and indexed-cover
  characterisations of `OpenCoversSplit` via `IsLocallyConstant`.
* `Topology.IsClosedEmbedding.openCoversSplit`, `IsClosed.openCoversSplit`,
  `Homeomorph.openCoversSplit`: splitting of open covers pulls back along closed embeddings (and in
  particular passes to closed subspaces and transfers along homeomorphisms).
* `TauCeti.OpenCoversSplit.of_zeroDimensionalSpace`: every compact zero-dimensional space (in
  particular, every profinite space) has split open covers.
* `TauCeti.OpenCoversSplit.eq_of_mem_connectedComponent`,
  `TauCeti.OpenCoversSplit.existsUnique_isClosed_singleton`: in a space whose open covers split, a
  connected component contains at most one closed point, and a unique closed point when the space is
  compact T₀.
* `TauCeti.openCoversSplit_iff`: Fargues' characterisation of `OpenCoversSplit X` on a spectral
  space `X` by existence of a unique closed point in each connected component.
* `TauCeti.IsWLocalSpace.of_zeroDimensionalSpace`: every compact T₀ zero-dimensional space (in
  particular, every profinite space) is w-local.
* `Topology.IsClosedEmbedding.isWLocalSpace`, `IsClosed.isWLocalSpace`, `Homeomorph.isWLocalSpace`:
  w-locality pulls back along closed embeddings (in particular passing to closed subspaces and
  transferring along homeomorphisms).
* `TauCeti.IsWLocalSpace.isHomeomorph_connectedComponentsMk`: in a w-local space, `closedPoints X`
  maps homeomorphically onto `ConnectedComponents X`.

## References

* P. Scholze, *Étale cohomology of diamonds*, arXiv:1709.07343, §7, Definition 7.1, Lemma 7.2, and
  Definition 7.4.
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015), §2.1,
  Definition 2.1.1 and Lemma 2.1.4.
-/

public section

open Function Set Topology TopologicalSpace

universe u v

namespace TauCeti

/-! ### Spaces whose open covers split -/

/-- Every open cover of `X` splits: for every family `𝒰` of open subsets covering `X`, there is a
locally constant choice `s : X → Set X` assigning to each `x : X` a member `s x ∈ 𝒰` with
`x ∈ s x`. -/
def OpenCoversSplit (X : Type u) [TopologicalSpace X] : Prop :=
  ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = Set.univ →
    ∃ s : X → Set X, (∀ x, s x ∈ 𝒰 ∧ x ∈ s x) ∧ ∀ U, IsOpen (s ⁻¹' {U})

/-- Unfolding characterization of `OpenCoversSplit`. -/
theorem openCoversSplit_def (X : Type u) [TopologicalSpace X] :
    OpenCoversSplit X ↔
      ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = Set.univ →
        ∃ s : X → Set X, (∀ x, s x ∈ 𝒰 ∧ x ∈ s x) ∧ ∀ U, IsOpen (s ⁻¹' {U}) :=
  Iff.rfl

/-- `OpenCoversSplit X` is equivalent to every open cover admitting a locally constant choice of
covering member. -/
theorem openCoversSplit_iff_isLocallyConstant (X : Type u) [TopologicalSpace X] :
    OpenCoversSplit X ↔
      ∀ 𝒰 : Set (Set X), (∀ U ∈ 𝒰, IsOpen U) → ⋃₀ 𝒰 = Set.univ →
        ∃ s : X → Set X, (∀ x, s x ∈ 𝒰 ∧ x ∈ s x) ∧ IsLocallyConstant s := by
  simp_rw [openCoversSplit_def, ← IsLocallyConstant.iff_isOpen_fiber]

/-- Dot-notation elimination of `OpenCoversSplit` producing a locally constant member choice on a
set-of-sets open cover. -/
theorem OpenCoversSplit.exists_isLocallyConstant {X : Type u} [TopologicalSpace X]
    (hX : OpenCoversSplit X) {𝒰 : Set (Set X)} (h𝒰o : ∀ U ∈ 𝒰, IsOpen U)
    (h𝒰c : ⋃₀ 𝒰 = Set.univ) :
    ∃ s : X → Set X, (∀ x, s x ∈ 𝒰 ∧ x ∈ s x) ∧ IsLocallyConstant s :=
  (openCoversSplit_iff_isLocallyConstant X).1 hX 𝒰 h𝒰o h𝒰c

/-- Dot-notation elimination of `OpenCoversSplit` for an arbitrary indexed open cover
`U : ι → Set X`, producing a locally constant index selection `g : X → ι`. -/
theorem OpenCoversSplit.exists_isLocallyConstant_index {X : Type u} [TopologicalSpace X]
    {ι : Type v} (hX : OpenCoversSplit X) {U : ι → Set X} (hUo : ∀ i, IsOpen (U i))
    (hUc : ⋃ i, U i = Set.univ) :
    ∃ g : X → ι, (∀ x, x ∈ U (g x)) ∧ IsLocallyConstant g := by
  obtain ⟨s, hs, hslc⟩ :=
    hX.exists_isLocallyConstant (𝒰 := Set.range U) (by rintro _ ⟨i, rfl⟩; exact hUo i)
      (by rw [sUnion_range]; exact hUc)
  let s' : X → Set.range U := fun x ↦ ⟨s x, (hs x).1⟩
  have hs'lc : IsLocallyConstant s' := IsLocallyConstant.iff_isOpen_fiber.2 fun W ↦ by
    have hEq : s' ⁻¹' {W} = s ⁻¹' {W.1} := by ext x; simp [s', Subtype.ext_iff]
    exact hEq ▸ hslc.isOpen_fiber W.1
  choose φ hφ using fun W : Set.range U ↦ W.2
  exact ⟨φ ∘ s', fun x ↦ by simpa only [Function.comp_apply, hφ] using (hs x).2, hs'lc.comp φ⟩

/-- Indexed-cover characterization of `OpenCoversSplit`. -/
theorem openCoversSplit_iff_iUnion (X : Type u) [TopologicalSpace X] :
    OpenCoversSplit X ↔
      ∀ (ι : Type u) (U : ι → Set X), (∀ i, IsOpen (U i)) → ⋃ i, U i = Set.univ →
        ∃ g : X → ι, (∀ x, x ∈ U (g x)) ∧ IsLocallyConstant g := by
  refine ⟨fun hX _ _ hUo hUc ↦ hX.exists_isLocallyConstant_index hUo hUc, fun h ↦ ?_⟩
  rw [openCoversSplit_iff_isLocallyConstant]
  intro 𝒰 h𝒰o h𝒰c
  obtain ⟨g, hg, hglc⟩ := h 𝒰 Subtype.val (fun U ↦ h𝒰o U.1 U.2)
    (by simpa only [sUnion_eq_iUnion] using h𝒰c)
  exact ⟨Subtype.val ∘ g, fun x ↦ ⟨(g x).2, hg x⟩, hglc.comp Subtype.val⟩

/-- If `f : Y → X` is continuous, `X` has split open covers, and each member `W` of an open cover
`𝒲` of `X` has preimage refining some member of `𝒰`, then `𝒰` admits a locally constant splitting on
`Y`. -/
theorem OpenCoversSplit.exists_isLocallyConstant_of_continuous {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] (hX : OpenCoversSplit X) {f : Y → X}
    (hf : Continuous f) {𝒲 : Set (Set X)} (h𝒲o : ∀ W ∈ 𝒲, IsOpen W)
    (h𝒲c : ⋃₀ 𝒲 = Set.univ) {𝒰 : Set (Set Y)}
    (href : ∀ W ∈ 𝒲, ∃ U ∈ 𝒰, f ⁻¹' W ⊆ U) :
    ∃ s : Y → Set Y, (∀ y, s y ∈ 𝒰 ∧ y ∈ s y) ∧ IsLocallyConstant s := by
  choose φ hφmem hφsub using fun W : 𝒲 ↦ href W.1 W.2
  obtain ⟨g, hg, hglc⟩ := hX.exists_isLocallyConstant_index (U := Subtype.val)
    (fun W : 𝒲 ↦ h𝒲o W.1 W.2) (by simpa only [sUnion_eq_iUnion] using h𝒲c)
  exact ⟨φ ∘ g ∘ f, fun y ↦ ⟨hφmem _, hφsub _ (hg (f y))⟩, (hglc.comp φ).comp_continuous hf⟩

/-- Every open cover of a discrete space splits. -/
theorem OpenCoversSplit.of_discreteTopology (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : OpenCoversSplit X := by
  intro 𝒰 _ h𝒰c
  choose s hs using fun x : X ↦ mem_sUnion.1 (h𝒰c.symm ▸ mem_univ x)
  exact ⟨s, hs, fun _ ↦ isOpen_discrete _⟩

/-- Every open cover of a subsingleton space (in particular, of an empty space) splits. -/
theorem OpenCoversSplit.of_subsingleton (X : Type u) [TopologicalSpace X] [Subsingleton X] :
    OpenCoversSplit X :=
  .of_discreteTopology X

/-- Splitting of open covers pulls back along a closed embedding. -/
theorem _root_.Topology.IsClosedEmbedding.openCoversSplit {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : IsClosedEmbedding f)
    (hY : OpenCoversSplit Y) : OpenCoversSplit X := by
  cases isEmpty_or_nonempty X with
  | inl => exact .of_subsingleton X
  | inr hne =>
  obtain ⟨x₀⟩ := hne
  rw [openCoversSplit_iff_isLocallyConstant]
  intro 𝒰 h𝒰o h𝒰c
  obtain ⟨U₀, hU₀, -⟩ := mem_sUnion.1 (h𝒰c.symm ▸ mem_univ x₀)
  choose V hVo hVpre using fun U : 𝒰 ↦ hf.isInducing.isOpen_iff.1 (h𝒰o U.1 U.2)
  let 𝒲 : Set (Set Y) := Set.range V ∪ {(Set.range f)ᶜ}
  have h𝒲o : ∀ W ∈ 𝒲, IsOpen W := by
    rintro W (⟨U, rfl⟩ | rfl)
    · exact hVo U
    · exact hf.isClosed_range.isOpen_compl
  have h𝒲c : ⋃₀ 𝒲 = Set.univ := eq_univ_iff_forall.2 fun y ↦ by
    by_cases hy : y ∈ Set.range f
    · rcases hy with ⟨x, rfl⟩
      obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 (h𝒰c.symm ▸ mem_univ x)
      exact mem_sUnion.2 ⟨V ⟨U, hU⟩, Or.inl ⟨⟨U, hU⟩, rfl⟩,
        mem_preimage.1 ((hVpre ⟨U, hU⟩).symm ▸ hxU)⟩
    · exact mem_sUnion.2 ⟨(Set.range f)ᶜ, Or.inr rfl, hy⟩
  refine hY.exists_isLocallyConstant_of_continuous hf.continuous h𝒲o h𝒲c ?_
  rintro W (⟨U, rfl⟩ | rfl)
  · exact ⟨U.1, U.2, (hVpre U).subset⟩
  · exact ⟨U₀, hU₀, fun x hx ↦ (hx ⟨x, rfl⟩).elim⟩

/-- Splitting of open covers passes to closed subspaces of any topological space. -/
theorem _root_.IsClosed.openCoversSplit {X : Type u} [TopologicalSpace X] {F : Set X}
    (hF : IsClosed F) (hX : OpenCoversSplit X) : OpenCoversSplit F :=
  hF.isClosedEmbedding_subtypeVal.openCoversSplit hX

/-- Splitting of open covers transfers along a homeomorphism. -/
theorem _root_.Homeomorph.openCoversSplit {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (hX : OpenCoversSplit X) : OpenCoversSplit Y :=
  e.symm.isClosedEmbedding.openCoversSplit hX

/-- Homeomorphic spaces have equivalent `OpenCoversSplit` predicates. -/
theorem _root_.Homeomorph.openCoversSplit_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    OpenCoversSplit X ↔ OpenCoversSplit Y :=
  ⟨e.openCoversSplit, e.symm.openCoversSplit⟩

/-- Every open cover of a compact zero-dimensional space (in particular, of any profinite space)
splits. -/
theorem OpenCoversSplit.of_zeroDimensionalSpace (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [ZeroDimensionalSpace X] : OpenCoversSplit X := by
  intro 𝒰 h𝒰o h𝒰c
  have hcov : IsOpenCover (fun i : 𝒰 ↦ (⟨i.1, h𝒰o i.1 i.2⟩ : Opens X)) :=
    IsOpenCover.of_sets _ (by simpa [iUnion_subtype, ← sUnion_eq_biUnion] using h𝒰c)
  obtain ⟨n, W, hW₁, hW₂, hW₃⟩ := hcov.exists_finite_nonempty_disjoint_clopen_cover
  choose u hu using fun j ↦ (hW₁ j).2
  have huniq (x : X) : ∃! j, x ∈ W j := by
    obtain ⟨j, hj⟩ := mem_iUnion.1 (hW₂ (mem_univ x))
    refine ⟨j, hj, fun k hk ↦ hW₃.eq ?_⟩
    exact not_disjoint_iff.2 ⟨x, hk, hj⟩ ∘ (Clopens.coe_disjoint.2 ·)
  choose g hg hg' using huniq
  have hgc : Continuous g := continuous_discrete_rng.2 fun j ↦ by
    convert (W j).isOpen
    exact Set.ext fun x ↦ ⟨fun hj ↦ hj ▸ hg x, fun hx ↦ (hg' x j hx).symm⟩
  exact ⟨fun x ↦ (u (g x)).1, fun x ↦ ⟨(u (g x)).2, hu (g x) (hg x)⟩,
    fun U ↦ (isOpen_discrete ((fun j ↦ (u j).1) ⁻¹' {U})).preimage hgc⟩

/-- In any topological space whose open covers split, each connected component contains at most one
closed point. -/
theorem OpenCoversSplit.eq_of_mem_connectedComponent {X : Type u} [TopologicalSpace X]
    (hX : OpenCoversSplit X) {x y : X} (hxy : x ∈ connectedComponent y)
    (hx : IsClosed ({x} : Set X)) (hy : IsClosed ({y} : Set X)) : x = y := by
  -- Two distinct closed points give an open cover `{x}ᶜ, {y}ᶜ` admitting no constant choice on the
  -- shared connected component.
  by_contra hne
  let 𝒰 : Set (Set X) := {({x} : Set X)ᶜ, ({y} : Set X)ᶜ}
  have h𝒰o : ∀ U ∈ 𝒰, IsOpen U := by
    rintro U (rfl | rfl)
    · exact hx.isOpen_compl
    · exact hy.isOpen_compl
  have h𝒰c : ⋃₀ 𝒰 = Set.univ := eq_univ_iff_forall.2 fun z ↦ by
    by_cases hzx : z = x
    · exact mem_sUnion.2 ⟨({y} : Set X)ᶜ, Or.inr rfl, hzx ▸ hne⟩
    · exact mem_sUnion.2 ⟨({x} : Set X)ᶜ, Or.inl rfl, hzx⟩
  obtain ⟨s, hs, hslc⟩ := hX.exists_isLocallyConstant h𝒰o h𝒰c
  have hsxy : s x = s y :=
    hslc.apply_eq_of_isPreconnected isPreconnected_connectedComponent hxy mem_connectedComponent
  rcases (hs x).1 with hsx | hsx
  · exact (hsx ▸ (hs x).2) rfl
  · exact ((hsxy.symm.trans hsx) ▸ (hs y).2) rfl

/-- In a compact T₀ space whose open covers split, every connected component contains a unique
closed point. -/
theorem OpenCoversSplit.existsUnique_isClosed_singleton {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T0Space X] (hX : OpenCoversSplit X) (x : X) :
    ∃! y : X, y ∈ connectedComponent x ∧ IsClosed ({y} : Set X) := by
  obtain ⟨y, hyc, hycl⟩ :=
    isClosed_connectedComponent.exists_closed_singleton ⟨x, mem_connectedComponent⟩
  exact ⟨y, ⟨hyc, hycl⟩, fun y' ⟨hy'c, hy'cl⟩ ↦
    hX.eq_of_mem_connectedComponent ((connectedComponent_eq hyc) ▸ hy'c) hy'cl hycl⟩

/-! ### Fargues' characterisation on spectral spaces -/

/-- **Fargues' characterisation** of spectral spaces whose open covers split: every open cover of a
spectral space `X` splits if and only if every connected component of `X` contains a unique closed
point. -/
theorem openCoversSplit_iff (X : Type u) [TopologicalSpace X] [SpectralSpace X] :
    OpenCoversSplit X ↔ ∀ x : X, ∃! y : X, y ∈ connectedComponent x ∧ IsClosed {y} := by
  refine ⟨fun hX ↦ hX.existsUnique_isClosed_singleton, fun h ↦ ?_⟩
  rw [openCoversSplit_iff_isLocallyConstant]
  intro 𝒰 h𝒰o h𝒰c
  have hclosedMap : IsClosedMap (ConnectedComponents.mk : X → ConnectedComponents X) :=
    ConnectedComponents.continuous_coe.isClosedMap
  let V : 𝒰 → Set (ConnectedComponents X) := fun U ↦ (ConnectedComponents.mk '' (U.1)ᶜ)ᶜ
  have hVo : ∀ W ∈ Set.range V, IsOpen W := by
    rintro _ ⟨U, rfl⟩
    exact (hclosedMap _ (h𝒰o U.1 U.2).isClosed_compl).isOpen_compl
  have hVc : ⋃₀ Set.range V = Set.univ := eq_univ_iff_forall.2 fun c ↦ by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, -, hyuniq⟩ := h x
    obtain ⟨U, hU, hyU⟩ := mem_sUnion.1 (h𝒰c.symm ▸ mem_univ y)
    refine mem_sUnion.2 ⟨V ⟨U, hU⟩, ⟨⟨U, hU⟩, rfl⟩, fun ⟨z, hzU, hzx⟩ ↦ hzU ?_⟩
    exact isClosed_connectedComponent.subset_of_forall_isClosed_singleton (h𝒰o U hU)
      (fun w hwc hwcl ↦ hyuniq w ⟨hwc, hwcl⟩ ▸ hyU) (ConnectedComponents.coe_eq_coe'.1 hzx)
  refine (OpenCoversSplit.of_zeroDimensionalSpace
      (ConnectedComponents X)).exists_isLocallyConstant_of_continuous
      ConnectedComponents.continuous_coe hVo hVc ?_
  rintro _ ⟨U, rfl⟩
  exact ⟨U.1, U.2, fun x hxV ↦ by_contra fun hxU ↦ hxV ⟨x, hxU, rfl⟩⟩

/-! ### w-local spectral spaces -/

/-- A *w-local* space is a spectral space all of whose open covers split and whose closed points
form a closed subset. -/
def IsWLocalSpace (X : Type u) [TopologicalSpace X] : Prop :=
  SpectralSpace X ∧ OpenCoversSplit X ∧ IsClosed (closedPoints X)

/-- Unfolding characterization of `IsWLocalSpace`. -/
theorem isWLocalSpace_def (X : Type u) [TopologicalSpace X] :
    IsWLocalSpace X ↔
      SpectralSpace X ∧ OpenCoversSplit X ∧ IsClosed (closedPoints X) :=
  Iff.rfl

/-- A w-local space is spectral. -/
theorem IsWLocalSpace.spectralSpace {X : Type u} [TopologicalSpace X] (hX : IsWLocalSpace X) :
    SpectralSpace X :=
  hX.1

/-- Every open cover of a w-local space splits. -/
theorem IsWLocalSpace.openCoversSplit {X : Type u} [TopologicalSpace X] (hX : IsWLocalSpace X) :
    OpenCoversSplit X :=
  hX.2.1

/-- The set of closed points of a w-local space is closed. -/
theorem IsWLocalSpace.isClosed_closedPoints {X : Type u} [TopologicalSpace X]
    (hX : IsWLocalSpace X) : IsClosed (closedPoints X) :=
  hX.2.2

/-- Every connected component of a w-local space contains a unique closed point. -/
theorem IsWLocalSpace.existsUnique_isClosed_singleton {X : Type u} [TopologicalSpace X]
    (hX : IsWLocalSpace X) (x : X) :
    ∃! y : X, y ∈ connectedComponent x ∧ IsClosed ({y} : Set X) := by
  have := hX.spectralSpace
  exact hX.openCoversSplit.existsUnique_isClosed_singleton x

/-- Every compact T₀ zero-dimensional space (in particular, every profinite space) is w-local. -/
theorem IsWLocalSpace.of_zeroDimensionalSpace (X : Type u) [TopologicalSpace X]
    [CompactSpace X] [T0Space X] [ZeroDimensionalSpace X] : IsWLocalSpace X := by
  refine ⟨spectralSpace_of_zeroDimensionalSpace X, .of_zeroDimensionalSpace X, ?_⟩
  rw [closedPoints_eq_univ]
  exact isClosed_univ

/-- Every subsingleton topological space (in particular, every empty space) is w-local. -/
theorem IsWLocalSpace.of_subsingleton (X : Type u) [TopologicalSpace X] [Subsingleton X] :
    IsWLocalSpace X :=
  .of_zeroDimensionalSpace X

/-- Being w-local pulls back along a closed embedding. -/
theorem _root_.Topology.IsClosedEmbedding.isWLocalSpace {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] {f : X → Y} (hf : IsClosedEmbedding f)
    (hY : IsWLocalSpace Y) : IsWLocalSpace X := by
  have := hY.spectralSpace
  have : SpectralSpace (Set.range f) := hf.isClosed_range.spectralSpace
  have : CompactSpace X := hf.compactSpace
  refine ⟨hf.toHomeomorph.isOpenEmbedding.spectralSpace, hf.openCoversSplit hY.openCoversSplit, ?_⟩
  rw [← hf.preimage_closedPoints]
  exact hY.isClosed_closedPoints.preimage hf.continuous

/-- Every closed subspace of a w-local space is w-local. -/
theorem _root_.IsClosed.isWLocalSpace {X : Type u} [TopologicalSpace X] {F : Set X}
    (hF : IsClosed F) (hX : IsWLocalSpace X) : IsWLocalSpace F :=
  hF.isClosedEmbedding_subtypeVal.isWLocalSpace hX

/-- Being w-local transfers along a homeomorphism. -/
theorem _root_.Homeomorph.isWLocalSpace {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (hX : IsWLocalSpace X) : IsWLocalSpace Y :=
  e.symm.isClosedEmbedding.isWLocalSpace hX

/-- Homeomorphic spaces have equivalent `IsWLocalSpace` predicates. -/
theorem _root_.Homeomorph.isWLocalSpace_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    IsWLocalSpace X ↔ IsWLocalSpace Y :=
  ⟨e.isWLocalSpace, e.symm.isWLocalSpace⟩

/-- In a w-local space the closed points map homeomorphically onto the space of connected
components. -/
theorem IsWLocalSpace.isHomeomorph_connectedComponentsMk {X : Type u} [TopologicalSpace X]
    (hX : IsWLocalSpace X) :
    IsHomeomorph fun x : closedPoints X ↦ ConnectedComponents.mk (x : X) := by
  have := hX.spectralSpace
  have : CompactSpace (closedPoints X) :=
    isCompact_iff_compactSpace.1 hX.isClosed_closedPoints.isCompact
  rw [isHomeomorph_iff_continuous_bijective]
  refine ⟨ConnectedComponents.continuous_coe.comp continuous_subtype_val, fun x₁ x₂ h12 ↦ ?_,
    fun c ↦ ?_⟩
  · exact Subtype.ext (hX.openCoversSplit.eq_of_mem_connectedComponent
      (ConnectedComponents.coe_eq_coe'.1 h12) x₁.2 x₂.2)
  · obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, ⟨hyc, hycl⟩, -⟩ := hX.existsUnique_isClosed_singleton x
    exact ⟨⟨y, hycl⟩, ConnectedComponents.coe_eq_coe'.2 hyc⟩

/-- The canonical homeomorphism from the closed points of a w-local space onto its space of
connected components. -/
noncomputable def IsWLocalSpace.closedPointsHomeomorphConnectedComponents {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) :
    closedPoints X ≃ₜ ConnectedComponents X :=
  hX.isHomeomorph_connectedComponentsMk.homeomorph _

/-- Applying `closedPointsHomeomorphConnectedComponents` sends a closed point to its connected
component. -/
@[simp]
theorem IsWLocalSpace.closedPointsHomeomorphConnectedComponents_apply {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) (x : closedPoints X) :
    hX.closedPointsHomeomorphConnectedComponents x = ConnectedComponents.mk (x : X) := by
  simp [closedPointsHomeomorphConnectedComponents]

/-- `closedPointsHomeomorphConnectedComponents.symm` sends the component of a closed point back to
that closed point. -/
@[simp]
theorem IsWLocalSpace.closedPointsHomeomorphConnectedComponents_symm_mk {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) (x : closedPoints X) :
    hX.closedPointsHomeomorphConnectedComponents.symm (ConnectedComponents.mk (x : X)) = x := by
  rw [← hX.closedPointsHomeomorphConnectedComponents_apply, Homeomorph.symm_apply_apply]

/-- The closed point selected for a component `c` projects back to `c` in
`ConnectedComponents X`. -/
@[simp]
theorem IsWLocalSpace.mk_closedPointsHomeomorphConnectedComponents_symm {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) (c : ConnectedComponents X) :
    ConnectedComponents.mk (hX.closedPointsHomeomorphConnectedComponents.symm c : X) = c := by
  rw [← hX.closedPointsHomeomorphConnectedComponents_apply, Homeomorph.apply_symm_apply]

/-- For any `x : X`, `closedPointsHomeomorphConnectedComponents.symm (ConnectedComponents.mk x)`
belongs to `connectedComponent x` (as the unique closed point of that component). -/
theorem IsWLocalSpace.closedPointsHomeomorphConnectedComponents_symm_mk_mem {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) (x : X) :
    (hX.closedPointsHomeomorphConnectedComponents.symm (ConnectedComponents.mk x) : X) ∈
      connectedComponent x :=
  ConnectedComponents.coe_eq_coe'.1 (hX.mk_closedPointsHomeomorphConnectedComponents_symm _)

end TauCeti
