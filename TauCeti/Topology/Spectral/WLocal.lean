/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.InductiveDimension.Classes
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.Spectral.Basic
import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Separation.DisjointCover
import TauCeti.Topology.Spectral.ConnectedComponents
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
2. `TauCeti.IsWLocalSpace`: `X` is spectral, its open covers split, and the locus
   `{x : X | IsClosed {x}}` of closed points is closed in `X`. Under these conditions the closed
   points form a canonical profinite cross-section of the connected components: the restriction of
   `ConnectedComponents.mk` to `{x : X | IsClosed {x}}` is a homeomorphism onto
   `ConnectedComponents X` (`TauCeti.IsWLocalSpace.isHomeomorph_connectedComponentsMk`).

## Main definitions

* `TauCeti.OpenCoversSplit`: every open cover of `X` admits a locally constant member choice.
* `TauCeti.IsWLocalSpace`: `X` is spectral, `OpenCoversSplit X` holds, and the set of closed points
  of `X` is closed.
* `TauCeti.IsWLocalSpace.closedPointsHomeomorphConnectedComponents`: the canonical homeomorphism
  from the closed points of a w-local space to `ConnectedComponents X`.

## Main results

* `TauCeti.openCoversSplit_iff_isLocallyConstant`: restatement of `OpenCoversSplit` via
  `IsLocallyConstant`.
* `TauCeti.OpenCoversSplit.isClosed`: splitting of open covers passes to closed subspaces of any
  topological space.
* `TauCeti.OpenCoversSplit.of_zeroDimensionalSpace`: every compact zero-dimensional space (in
  particular, every profinite space) has split open covers.
* `TauCeti.OpenCoversSplit.eq_of_mem_connectedComponent`,
  `TauCeti.OpenCoversSplit.existsUnique_isClosed_singleton`: in a space whose open covers split, a
  connected component contains at most one closed point, and a unique closed point when the space is
  compact T₀.
* `TauCeti.connectedComponent_subset_of_forall_isClosed_singleton`: in a compact T₀ space, any open
  neighbourhood of the unique closed point of a connected component contains the entire component.
* `TauCeti.openCoversSplit_iff`: Fargues' characterisation of `OpenCoversSplit X` on a spectral
  space `X` by existence of a unique closed point in each connected component.
* `TauCeti.IsWLocalSpace.of_zeroDimensionalSpace`: every compact T₀ zero-dimensional space (in
  particular, every profinite space) is w-local.
* `TauCeti.IsWLocalSpace.isClosed`: closed subspaces of a w-local space are w-local.
* `TauCeti.IsWLocalSpace.isHomeomorph_connectedComponentsMk`: in a w-local space, the closed points
  map homeomorphically onto `ConnectedComponents X`.

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

/-- Every open cover of an empty space splits. -/
theorem OpenCoversSplit.of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    OpenCoversSplit X :=
  fun _ _ _ ↦ ⟨isEmptyElim, isEmptyElim, fun _ ↦ isOpen_discrete _⟩

/-- Every open cover of a discrete space splits. -/
theorem OpenCoversSplit.of_discreteTopology (X : Type u) [TopologicalSpace X]
    [DiscreteTopology X] : OpenCoversSplit X := by
  intro 𝒰 _ h𝒰c
  choose s hs using fun x : X ↦ mem_sUnion.1 (h𝒰c.symm ▸ mem_univ x)
  exact ⟨s, hs, fun _ ↦ isOpen_discrete _⟩

/-- Splitting of open covers transfers along a homeomorphism. -/
theorem OpenCoversSplit.of_homeomorph {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) (hX : OpenCoversSplit X) : OpenCoversSplit Y := by
  rw [openCoversSplit_iff_isLocallyConstant] at hX ⊢
  intro 𝒰 h𝒰o h𝒰c
  let 𝒱 : Set (Set X) := (fun U ↦ e ⁻¹' U) '' 𝒰
  have h𝒱o : ∀ V ∈ 𝒱, IsOpen V := by
    rintro _ ⟨U, hU, rfl⟩
    exact (h𝒰o U hU).preimage e.continuous
  have h𝒱c : ⋃₀ 𝒱 = Set.univ := eq_univ_iff_forall.2 fun x ↦ by
    obtain ⟨U, hU, hxU⟩ := mem_sUnion.1 (h𝒰c.symm ▸ mem_univ (e x))
    exact mem_sUnion.2 ⟨e ⁻¹' U, ⟨U, hU, rfl⟩, hxU⟩
  obtain ⟨s, hs, hslc⟩ := hX 𝒱 h𝒱o h𝒱c
  refine ⟨(fun V ↦ e '' V) ∘ s ∘ e.symm, fun y ↦ ?_,
    (hslc.comp fun V ↦ e '' V).comp_continuous e.symm.continuous⟩
  obtain ⟨⟨W, hW, heq⟩, hy⟩ := hs (e.symm y)
  have hWs : e '' s (e.symm y) = W := by rw [← heq, e.image_preimage]
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_apply, hWs] using hW
  · rw [Function.comp_apply, Function.comp_apply, hWs]
    simpa only [← heq, mem_preimage, e.apply_symm_apply] using hy

end TauCeti

/-- Homeomorphic spaces have equivalent `OpenCoversSplit` predicates. -/
theorem Homeomorph.openCoversSplit_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.OpenCoversSplit X ↔ TauCeti.OpenCoversSplit Y :=
  ⟨TauCeti.OpenCoversSplit.of_homeomorph e, TauCeti.OpenCoversSplit.of_homeomorph e.symm⟩

namespace TauCeti

/-- Splitting of open covers passes to closed subspaces of any topological space. -/
theorem OpenCoversSplit.isClosed {X : Type u} [TopologicalSpace X] (hX : OpenCoversSplit X)
    {F : Set X} (hF : IsClosed F) : OpenCoversSplit F := by
  -- Extend an open cover of `F` by `Fᶜ`; a splitting on `X` cannot select `Fᶜ` at points of `F`.
  rw [openCoversSplit_iff_isLocallyConstant] at hX ⊢
  intro 𝒱 h𝒱o h𝒱c
  choose U hUo hUpre using fun V : 𝒱 ↦ isOpen_induced_iff.1 (h𝒱o V.1 V.2)
  let 𝒰 : Set (Set X) := Set.range U ∪ {Fᶜ}
  have h𝒰o : ∀ W ∈ 𝒰, IsOpen W := by
    rintro W (⟨V, rfl⟩ | rfl)
    · exact hUo V
    · exact hF.isOpen_compl
  have h𝒰c : ⋃₀ 𝒰 = Set.univ := eq_univ_iff_forall.2 fun x ↦ by
    by_cases hxF : x ∈ F
    · obtain ⟨V, hV, hxV⟩ := mem_sUnion.1 (h𝒱c.symm ▸ mem_univ (⟨x, hxF⟩ : F))
      have hxU : x ∈ U ⟨V, hV⟩ := mem_preimage.1 (by rw [hUpre ⟨V, hV⟩]; exact hxV)
      exact mem_sUnion.2 ⟨U ⟨V, hV⟩, Or.inl ⟨⟨V, hV⟩, rfl⟩, hxU⟩
    · exact mem_sUnion.2 ⟨Fᶜ, Or.inr rfl, hxF⟩
  obtain ⟨s, hs, hslc⟩ := hX 𝒰 h𝒰o h𝒰c
  classical
  let lift : Set X → Set F := fun W ↦ if hW : W ∈ Set.range U then (hW.choose).1 else ∅
  refine ⟨lift ∘ s ∘ Subtype.val, fun y ↦ ?_,
    (hslc.comp lift).comp_continuous continuous_subtype_val⟩
  have hmem : s y ∈ Set.range U := (hs y).1.resolve_right fun h ↦ (h ▸ (hs y).2) y.2
  have hly : lift (s y) = (hmem.choose).1 := by dsimp only [lift]; split_ifs; rfl
  refine ⟨by simpa only [Function.comp_apply, hly] using (hmem.choose).2, ?_⟩
  have hyU : (y : X) ∈ U hmem.choose := by
    rw [hmem.choose_spec]
    exact (hs y).2
  simpa only [Function.comp_apply, hly, ← hUpre hmem.choose, mem_preimage] using hyU

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
  rw [openCoversSplit_iff_isLocallyConstant] at hX
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
  obtain ⟨s, hs, hslc⟩ := hX 𝒰 h𝒰o h𝒰c
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

/-- In a compact T₀ space, if `y` is the only closed point of `connectedComponent x`, then every
open neighbourhood of `y` contains the entire connected component `connectedComponent x`. -/
theorem connectedComponent_subset_of_forall_isClosed_singleton {X : Type u} [TopologicalSpace X]
    [CompactSpace X] [T0Space X] {x y : X} {U : Set X} (hU : IsOpen U) (hyU : y ∈ U)
    (huniq : ∀ z ∈ connectedComponent x, IsClosed ({z} : Set X) → z = y) :
    connectedComponent x ⊆ U := by
  intro z hzc
  by_contra hzU
  obtain ⟨w, ⟨hwc, hwU⟩, hwcl⟩ :=
    (isClosed_connectedComponent.sdiff hU).exists_closed_singleton ⟨z, hzc, hzU⟩
  exact hwU (huniq w hwc hwcl ▸ hyU)

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
    exact connectedComponent_subset_of_forall_isClosed_singleton (h𝒰o U hU) hyU
      (fun w hwc hwcl ↦ hyuniq w ⟨hwc, hwcl⟩) (ConnectedComponents.coe_eq_coe'.1 hzx)
  obtain ⟨s₀, hs₀, hs₀lc⟩ :=
    (openCoversSplit_iff_isLocallyConstant (ConnectedComponents X)).1
      (OpenCoversSplit.of_zeroDimensionalSpace (ConnectedComponents X)) (Set.range V) hVo hVc
  classical
  let lift : Set (ConnectedComponents X) → Set X := fun W ↦
    if hW : W ∈ Set.range V then (hW.choose).1 else ∅
  refine ⟨lift ∘ s₀ ∘ ConnectedComponents.mk, fun x ↦ ?_,
    (hs₀lc.comp lift).comp_continuous ConnectedComponents.continuous_coe⟩
  have hmem : s₀ (ConnectedComponents.mk x) ∈ Set.range V := (hs₀ _).1
  have hlx : lift (s₀ (ConnectedComponents.mk x)) = (hmem.choose).1 := by
    dsimp only [lift]; split_ifs; rfl
  refine ⟨by simpa only [Function.comp_apply, hlx] using (hmem.choose).2, ?_⟩
  simp only [Function.comp_apply, hlx]
  by_contra hxU
  have hxV : ConnectedComponents.mk x ∈ V hmem.choose :=
    hmem.choose_spec.symm ▸ (hs₀ (ConnectedComponents.mk x)).2
  exact hxV ⟨x, hxU, rfl⟩

/-! ### w-local spectral spaces -/

/-- A *w-local* space is a spectral space all of whose open covers split and whose closed points
form a closed subset. -/
def IsWLocalSpace (X : Type u) [TopologicalSpace X] : Prop :=
  SpectralSpace X ∧ OpenCoversSplit X ∧ IsClosed {x : X | IsClosed ({x} : Set X)}

/-- Unfolding characterization of `IsWLocalSpace`. -/
theorem isWLocalSpace_def (X : Type u) [TopologicalSpace X] :
    IsWLocalSpace X ↔
      SpectralSpace X ∧ OpenCoversSplit X ∧ IsClosed {x : X | IsClosed ({x} : Set X)} :=
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
    (hX : IsWLocalSpace X) : IsClosed {x : X | IsClosed ({x} : Set X)} :=
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
  have heq : {x : X | IsClosed ({x} : Set X)} = Set.univ :=
    eq_univ_of_forall fun _ ↦ isClosed_singleton
  rw [heq]
  exact isClosed_univ

/-- Every empty topological space is w-local. -/
theorem IsWLocalSpace.of_isEmpty (X : Type u) [TopologicalSpace X] [IsEmpty X] :
    IsWLocalSpace X :=
  .of_zeroDimensionalSpace X

/-- Every closed subspace of a w-local space is w-local. -/
theorem IsWLocalSpace.isClosed {X : Type u} [TopologicalSpace X] (hX : IsWLocalSpace X)
    {F : Set X} (hF : IsClosed F) : IsWLocalSpace F := by
  have := hX.spectralSpace
  refine ⟨hF.spectralSpace, hX.openCoversSplit.isClosed hF, ?_⟩
  have heq : {y : F | IsClosed ({y} : Set F)} = Subtype.val ⁻¹' {x : X | IsClosed ({x} : Set X)} :=
    Set.ext fun y ↦ by
      simpa [image_singleton] using
        hF.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed (s := ({y} : Set F))
  rw [heq]
  exact hX.isClosed_closedPoints.preimage continuous_subtype_val

/-- In a w-local space the closed points map homeomorphically onto the space of connected
components. -/
theorem IsWLocalSpace.isHomeomorph_connectedComponentsMk {X : Type u} [TopologicalSpace X]
    (hX : IsWLocalSpace X) :
    IsHomeomorph fun x : {x : X | IsClosed ({x} : Set X)} ↦ ConnectedComponents.mk (x : X) := by
  have := hX.spectralSpace
  have : CompactSpace {x : X | IsClosed ({x} : Set X)} :=
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
    {x : X | IsClosed ({x} : Set X)} ≃ₜ ConnectedComponents X :=
  hX.isHomeomorph_connectedComponentsMk.homeomorph _

/-- Applying `closedPointsHomeomorphConnectedComponents` sends a closed point to its connected
component. -/
@[simp]
theorem IsWLocalSpace.closedPointsHomeomorphConnectedComponents_apply {X : Type u}
    [TopologicalSpace X] (hX : IsWLocalSpace X) (x : {x : X | IsClosed ({x} : Set X)}) :
    hX.closedPointsHomeomorphConnectedComponents x = ConnectedComponents.mk (x : X) :=
  (rfl)

end TauCeti

/-- Homeomorphic spaces have equivalent `IsWLocalSpace` predicates. -/
theorem Homeomorph.isWLocalSpace_iff {X : Type u} {Y : Type v} [TopologicalSpace X]
    [TopologicalSpace Y] (e : X ≃ₜ Y) :
    TauCeti.IsWLocalSpace X ↔ TauCeti.IsWLocalSpace Y := by
  refine and_congr
    ⟨fun _ ↦ by have := e.compactSpace; exact e.symm.isOpenEmbedding.spectralSpace,
     fun _ ↦ by have := e.symm.compactSpace; exact e.isOpenEmbedding.spectralSpace⟩
    (and_congr e.openCoversSplit_iff ?_)
  rw [← e.isClosed_image]
  convert Iff.rfl using 2
  ext y
  constructor
  · intro hy
    exact ⟨e.symm y, by simpa [image_singleton] using e.symm.isClosed_image.2 hy,
      e.apply_symm_apply y⟩
  · rintro ⟨x, hx, rfl⟩
    simpa [image_singleton] using e.isClosed_image.2 hx
