/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.TopologicalSpace

/-!
# The topology of a restricted product

General facts about the restricted-product topology, which Mathlib defines as the final
topology over the principal stages `Πʳ i, [R i, A i]_[𝓟 S]`. A set is open if and only if its
preimage in every principal stage is open: this is the `Prop`-valued form of Mathlib's universal
property `RestrictedProduct.continuous_dom`. Inserting a single factor is continuous, the analogue
of `continuous_mulSingle` (and, additively, `continuous_single`) for `Pi` types, and for Hausdorff
factors it is a closed embedding. Over the cofinite filter, evaluation at an index is an open map.
On a subspace lying in the reference sets at every index of some `T` with `𝓕 ≤ 𝓟 T` (over the
cofinite filter: outside finitely many indices), the restricted-product topology agrees with the
product topology.

Over the cofinite filter, boxes `{x | ∀ i, x i ∈ C i}` with open factors containing `A i` at all
but finitely many indices are open (`isOpen_restrictedProduct_box`). When every reference set
`A i` is open, boxes built from local bases (`isTopologicalBasis_restrictedProduct_boxes`) or
open factors eventually equal to `A i` (`isTopologicalBasis_restrictedProduct_open_boxes`) form a
topological basis; in particular, a restricted product of countably many second-countable spaces
relative to open reference sets is second countable (`secondCountableTopology_restrictedProduct`).

The restricted-product topology is finer than the topology induced from the full product
`Π i, R i`, and in general strictly finer. The clearest instance is a family of discrete spaces
with reference sets of at most one element: every principal stage indexed by a cofinite set, and
hence the restricted product itself, is discrete (`discreteTopology_restrictedProduct`), whereas
the full product of discrete groups with infinitely many nontrivial factors is not. So for
discrete groups with trivial reference subgroups, infinitely many of them nontrivial, the coercion
to the full product is not inducing (`not_isInducing_coe_bot`): the restricted-product topology is
not the induced one. This is the reason continuity of a map *into* a restricted product does not
follow from continuity of its coordinates.

## References

* N. Bourbaki, *General Topology*.
* A. Weil, *Basic Number Theory*.
-/
public section

namespace TauCeti

open Filter Topology
open scoped RestrictedProduct

universe u v w

variable {ι : Type u} {R : ι → Type v} {A : ∀ i, Set (R i)} {𝓕 : Filter ι}
variable [∀ i, TopologicalSpace (R i)]

/-- A subset of a restricted product is open if and only if its preimage in every principal
stage `Πʳ i, [R i, A i]_[𝓟 S]` with `𝓕 ≤ 𝓟 S` is open. -/
theorem isOpen_restrictedProduct_iff {s : Set (Πʳ i, [R i, A i]_[𝓕])} :
    IsOpen s ↔ ∀ (S : Set ι) (hS : 𝓕 ≤ 𝓟 S),
      IsOpen (RestrictedProduct.inclusion R A hS ⁻¹' s) := by
  simp only [isOpen_iff_continuous_mem]
  exact RestrictedProduct.continuous_dom

/-- Evaluation at any index is an open map from a restricted product over the cofinite filter to
that factor. -/
theorem isOpenMap_restrictedProduct_eval (i : ι) :
    IsOpenMap (fun x : Πʳ j, [R j, A j] ↦ x i) := by
  classical
  refine IsOpenMap.of_sections fun x ↦ ?_
  -- `Function.update x i y` lies in the principal stage of the cofinite set where `x` is in the
  -- reference sets, with `i` removed.
  set T : Set ι := {j | x j ∈ A j} \ {i}
  have hT : (cofinite : Filter ι) ≤ 𝓟 T :=
    le_principal_iff.2 (sdiff_mem x.2 (Set.finite_singleton i).compl_mem_cofinite)
  let g : R i → Πʳ j, [R j, A j]_[𝓟 T] := fun y ↦
    ⟨Function.update x i y, eventually_principal.2 fun j hj ↦ by
      rw [Function.update_of_ne hj.2]
      exact hj.1⟩
  have hg : Continuous g := RestrictedProduct.continuous_rng_of_principal.2
    (continuous_const.update i continuous_id)
  refine ⟨RestrictedProduct.inclusion R A hT ∘ g,
    ((RestrictedProduct.continuous_inclusion hT).comp hg).continuousAt, ?_, fun y ↦ ?_⟩
  · ext j
    exact congrFun (Function.update_eq_self i (⇑x)) j
  · exact Function.update_self i y (⇑x)

/-- **On a principal stage, the restricted-product topology is the product topology.**
If `𝓕 ≤ 𝓟 T` and an embedding `f` into the restricted product `Πʳ i, [R i, A i]_[𝓕]` lands in the
reference sets at every index of `T`, then reading off all coordinates of `f` is an embedding into
the full product `Π i, R i`. Over the cofinite filter, `T` is the complement of a finite set. -/
theorem isEmbedding_restrictedProduct_coe_comp {X : Type w} [TopologicalSpace X] {T : Set ι}
    (hT : 𝓕 ≤ 𝓟 T) {f : X → Πʳ i, [R i, A i]_[𝓕]} (hf : IsEmbedding f)
    (hmem : ∀ x, ∀ i ∈ T, f x i ∈ A i) :
    IsEmbedding fun x ↦ ⇑(f x) := by
  -- `f` factors through the principal stage `Πʳ i, [R i, A i]_[𝓟 T]`
  let g : X → Πʳ i, [R i, A i]_[𝓟 T] := fun x ↦ ⟨f x, eventually_principal.mpr (hmem x)⟩
  -- `RestrictedProduct.inclusion` composed with `g` is `f` by definition
  have hg : IsEmbedding g := by
    refine ⟨((RestrictedProduct.isEmbedding_inclusion_principal hT).isInducing.of_comp_iff).mp
      hf.isInducing, fun x y hxy ↦ hf.injective ?_⟩
    ext i
    exact RestrictedProduct.ext_iff.mp hxy i
  exact RestrictedProduct.isEmbedding_coe_of_principal.comp hg

section

variable {S : ι → Type w} {G : ι → Type v} [∀ i, SetLike (S i) (G i)] (B : ∀ i, S i)
variable [DecidableEq ι] [∀ i, One (G i)] [∀ i, OneMemClass (S i) (G i)]
variable [∀ i, TopologicalSpace (G i)]

/-- Inserting a single factor into a restricted product is continuous. -/
@[to_additive (attr := continuity, fun_prop)
  /-- Inserting a single factor into a restricted product is continuous. -/]
theorem continuous_restrictedProduct_mulSingle (i : ι) :
    Continuous (RestrictedProduct.mulSingle B i) := by
  have h : (cofinite : Filter ι) ≤ 𝓟 {i}ᶜ :=
    le_principal_iff.2 (Set.finite_singleton i).compl_mem_cofinite
  let f : G i → Πʳ j, [G j, B j]_[𝓟 {i}ᶜ] := fun x ↦
    ⟨Pi.mulSingle i x, eventually_principal.2 fun j hj ↦ by
      rw [Pi.mulSingle_eq_of_ne (Set.notMem_singleton_iff.1 hj)]
      exact one_mem _⟩
  have hf : Continuous f :=
    RestrictedProduct.continuous_rng_of_principal.2 (continuous_mulSingle i)
  exact (RestrictedProduct.continuous_inclusion h).comp hf

/-- The map `RestrictedProduct.mulSingle B i`, which inserts a factor at `i` and takes value `1`
elsewhere, is a closed embedding when all factors are Hausdorff. -/
@[to_additive
  /-- The map `RestrictedProduct.single B i`, which inserts a factor at `i` and takes value `0`
  elsewhere, is a closed embedding when all factors are Hausdorff. -/]
theorem isClosedEmbedding_restrictedProduct_mulSingle [∀ i, T2Space (G i)] (i : ι) :
    IsClosedEmbedding (RestrictedProduct.mulSingle B i) :=
  Function.LeftInverse.isClosedEmbedding (f := fun x : Πʳ j, [G j, B j] ↦ x i)
    (RestrictedProduct.mulSingle_eq_same B i) (RestrictedProduct.continuous_eval i)
    (continuous_restrictedProduct_mulSingle B i)

end

section Discrete

/-- A principal stage `Πʳ i, [R i, A i]_[𝓟 S]` with `S` cofinite is discrete when the reference
sets `A i` for `i ∈ S` have at most one element and the spaces `R i` for `i ∉ S` are discrete: on
the stage the coordinates in `S` are determined by the reference sets, and only finitely many
coordinates remain free. -/
theorem discreteTopology_restrictedProduct_principal {S : Set ι} (hS : Sᶜ.Finite)
    (hA : ∀ i ∈ S, (A i).Subsingleton) (hR : ∀ i ∉ S, DiscreteTopology (R i)) :
    DiscreteTopology (Πʳ i, [R i, A i]_[𝓟 S]) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦ ?_
  rw [RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff]
  refine ⟨Set.pi Sᶜ fun i ↦ {x i}, isOpen_set_pi hS fun i hi ↦ ?_, ?_⟩
  · have := hR i hi
    exact isOpen_discrete _
  ext y
  simp only [Set.mem_preimage, Set.mem_pi, Set.mem_compl_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    ext i
    by_cases hi : i ∈ S
    · exact hA i hi (eventually_principal.1 y.2 i hi) (eventually_principal.1 x.2 i hi)
    · exact h i hi
  · rintro rfl i _
    rfl

variable [∀ i, DiscreteTopology (R i)]

/-- A restricted product of discrete spaces relative to reference sets with at most one element
is discrete: every principal stage indexed by a cofinite set is, and the restricted-product
topology is the final topology over these stages. -/
theorem discreteTopology_restrictedProduct (hA : ∀ i, (A i).Subsingleton) :
    DiscreteTopology (Πʳ i, [R i, A i]) := by
  refine discreteTopology_iff_isOpen_singleton.2 fun x ↦
    isOpen_restrictedProduct_iff.2 fun S hS ↦ ?_
  have := discreteTopology_restrictedProduct_principal (mem_cofinite.1 (le_principal_iff.1 hS))
    (fun i _ ↦ hA i) fun i _ ↦ inferInstance
  exact isOpen_discrete _

variable {G : ι → Type v} [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- A restricted product of discrete groups relative to the trivial reference subgroups is
discrete. -/
instance discreteTopology_restrictedProduct_bot [∀ i, DiscreteTopology (G i)] :
    DiscreteTopology (Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))]) :=
  discreteTopology_restrictedProduct fun i ↦ by
    rw [Subgroup.coe_bot]
    exact Set.subsingleton_singleton

/-- For discrete groups with trivial reference subgroups, infinitely many of them nontrivial, the
restricted product does not carry the topology induced from the full product: the restricted
product is discrete, but every neighbourhood of `1` in the full product contains an element
supported at a single index with nontrivial group. The restricted-product topology is therefore
strictly finer than the induced one in general, and continuity of a map into a restricted product
does not follow from continuity of its coordinates. -/
theorem not_isInducing_coe_bot [∀ i, DiscreteTopology (G i)]
    (hG : {i | Nontrivial (G i)}.Infinite) :
    ¬ IsInducing ((↑) : Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))] → ∀ i, G i) := by
  classical
  intro h
  obtain ⟨t, ht, hts⟩ := h.isOpen_iff.1
    (isOpen_discrete {(1 : Πʳ i, [G i, ((⊥ : Subgroup (G i)) : Set (G i))])})
  obtain ⟨I, u, hu, hIt⟩ := isOpen_pi_iff.1 ht _ (by rw [← Set.mem_preimage, hts]; rfl)
  obtain ⟨j, hj, hjI⟩ := hG.exists_notMem_finset I
  have : Nontrivial (G j) := hj
  obtain ⟨g, hg⟩ := exists_ne (1 : G j)
  -- The element supported at `j` lies in the basic neighbourhood `I.pi u` of `1`, hence in `t`,
  -- but is not `1`.
  have hmem : RestrictedProduct.mulSingle (fun i ↦ (⊥ : Subgroup (G i))) j g ∈ (↑) ⁻¹' t :=
    hIt fun a ha ↦ by
      have haj : a ≠ j := fun hab ↦ hjI (hab ▸ ha)
      rw [RestrictedProduct.coe_mulSingle_apply, Pi.mulSingle_eq_of_ne haj]
      exact (hu a ha).2
  rw [hts, Set.mem_singleton_iff, RestrictedProduct.mulSingle_eq_one_iff] at hmem
  exact hg hmem

end Discrete

section Bases

/-- A box `{x | ∀ i, x i ∈ C i}` in a restricted product over the cofinite filter is open whenever
every factor `C i` is open and `A i ⊆ C i` for all but finitely many `i` (in particular, whenever
`C i = A i` for all but finitely many `i`). -/
theorem isOpen_restrictedProduct_box {C : ∀ i, Set (R i)} (hC : ∀ i, IsOpen (C i))
    (hAC : ∀ᶠ i in cofinite, A i ⊆ C i) :
    IsOpen {x : Πʳ i, [R i, A i] | ∀ i, x i ∈ C i} := by
  refine isOpen_restrictedProduct_iff.2 fun T hT ↦ ?_
  have hfin : ({i | A i ⊆ C i} ∩ T)ᶜ.Finite :=
    mem_cofinite.mp (hAC.and (le_principal_iff.mp hT))
  convert (isOpen_set_pi hfin fun i _ ↦ hC i).preimage RestrictedProduct.continuous_coe using 1
  ext y
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_compl_iff]
  refine ⟨fun h i _ ↦ h i, fun h i ↦ ?_⟩
  by_cases hi : i ∈ {i | A i ⊆ C i} ∩ T
  · exact hi.1 (y.2 hi.2)
  · exact h i hi

private theorem isOpen_restrictedProduct_finset_box (hA : ∀ i, IsOpen (A i))
    (S : Finset ι) {U : ∀ i : S, Set (R i)} (hU : ∀ i, IsOpen (U i)) :
    IsOpen {x : Πʳ i, [R i, A i] | (∀ i : S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i} := by
  classical
  let C : ∀ i, Set (R i) := fun i ↦ if hi : i ∈ S then U ⟨i, hi⟩ else A i
  have hC : ∀ i, IsOpen (C i) := fun i ↦ by
    by_cases hi : i ∈ S
    · simpa [C, hi] using hU ⟨i, hi⟩
    · simpa [C, hi] using hA i
  have hAC : ∀ᶠ i in cofinite, A i ⊆ C i := by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
    have hi' : i ∉ S := hi
    simp [C, hi']
  convert isOpen_restrictedProduct_box hC hAC using 1
  ext x
  simp only [Set.mem_ofPred_eq, C]
  exact ⟨fun h i ↦ by split_ifs with hi; exacts [h.1 ⟨i, hi⟩, h.2 i hi],
    fun h ↦ ⟨fun i ↦ by simpa [i.2] using h i.1, fun i hi ↦ by simpa [hi] using h i⟩⟩

/-- Given a topological basis `b i` on each factor `R i` and open reference sets `A i`, the boxes
restricting finitely many coordinates to elements of `b i` and the remaining coordinates to `A i`
form a topological basis of the restricted product `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_restrictedProduct_boxes (hA : ∀ i, IsOpen (A i))
    {b : ∀ i, Set (Set (R i))} (hb : ∀ i, TopologicalSpace.IsTopologicalBasis (b i)) :
    TopologicalSpace.IsTopologicalBasis
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ (S : Finset ι) (U : ∀ i : S, Set (R i)),
          (∀ i : S, U i ∈ b i.1) ∧
          s = {x | (∀ i : S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}} := by
  classical
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro _ ⟨S, U, hU, rfl⟩
    exact isOpen_restrictedProduct_finset_box hA S fun i ↦ (hb i.1).isOpen (hU i)
  · intro x V hxV hV
    -- Work inside the principal stage determined by the indices where `x i ∈ A i`.
    set T₀ : Set ι := {i | x i ∈ A i}
    have hT₀ : (cofinite : Filter ι) ≤ 𝓟 T₀ := le_principal_iff.mpr x.2
    let x₀ : Πʳ i, [R i, A i]_[𝓟 T₀] := ⟨x, eventually_principal.mpr fun _ hi ↦ hi⟩
    obtain ⟨W, hW, hW_eq⟩ := RestrictedProduct.isEmbedding_coe_of_principal.isOpen_iff.mp
      (hV.preimage (RestrictedProduct.continuous_inclusion hT₀))
    have hxW : (x : ∀ i, R i) ∈ W := by
      have hx₀ : x₀ ∈ RestrictedProduct.inclusion R A hT₀ ⁻¹' V := hxV
      rwa [← hW_eq] at hx₀
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.mp hW x hxW
    let S : Finset ι := I ∪ (mem_cofinite.mp x.2).toFinset
    -- On `i ∈ S`, intersect with `u i` (when `i ∈ I`) and `A i` (when `x i ∈ A i`) so that points
    -- of the box remain in the principal stage `𝓟 T₀` and land in `W`.
    have hU_ex : ∀ i : S, ∃ U ∈ b i.1, x i.1 ∈ U ∧
        (i.1 ∈ I → U ⊆ u i.1) ∧ (i.1 ∈ T₀ → U ⊆ A i.1) := fun i ↦ by
      let Wᵢ : Set (R i.1) :=
        (if i.1 ∈ I then u i.1 else Set.univ) ∩ (if i.1 ∈ T₀ then A i.1 else Set.univ)
      have hWᵢ : IsOpen Wᵢ :=
        ((by split_ifs with hi; exacts [(hu i.1 hi).1, isOpen_univ] : IsOpen _).inter
          (by split_ifs with hi; exacts [hA i.1, isOpen_univ]))
      have hxWᵢ : x i.1 ∈ Wᵢ :=
        ⟨by split_ifs with hi; exacts [(hu i.1 hi).2, trivial],
          by split_ifs with hi; exacts [hi, trivial]⟩
      obtain ⟨U, hUb, hxU, hUWᵢ⟩ := (hb i.1).exists_subset_of_mem_open hxWᵢ hWᵢ
      exact ⟨U, hUb, hxU, fun hi y hy ↦ by simpa [Wᵢ, hi] using (hUWᵢ hy).1,
        fun hi y hy ↦ by simpa [Wᵢ, hi] using (hUWᵢ hy).2⟩
    choose U hUb hxU hUu hUA using hU_ex
    refine ⟨{y | (∀ i : S, y i ∈ U i) ∧ ∀ i ∉ S, y i ∈ A i}, ⟨S, U, hUb, rfl⟩,
      ⟨hxU, fun i hi ↦ by_contra fun hxA ↦
        hi (Finset.mem_union_right I ((Set.Finite.mem_toFinset _).mpr hxA))⟩, fun y hy ↦ ?_⟩
    have hyT₀ : ∀ i ∈ T₀, y i ∈ A i := fun i hi ↦ by
      by_cases hiS : i ∈ S
      · exact hUA ⟨i, hiS⟩ hi (hy.1 ⟨i, hiS⟩)
      · exact hy.2 i hiS
    let y₀ : Πʳ i, [R i, A i]_[𝓟 T₀] := ⟨y, eventually_principal.mpr hyT₀⟩
    have hyW : y₀ ∈ ((↑) : Πʳ i, [R i, A i]_[𝓟 T₀] → ∀ i, R i) ⁻¹' W :=
      hIu fun i hi ↦ hUu ⟨i, Finset.mem_union_left _ hi⟩ hi (hy.1 ⟨i, Finset.mem_union_left _ hi⟩)
    rw [hW_eq] at hyW
    exact hyW

/-- When the reference sets `A i` are open, the boxes `{x | ∀ i, x i ∈ C i}` with open factors
`C i` eventually equal to `A i` form a topological basis of `Πʳ i, [R i, A i]`. -/
theorem isTopologicalBasis_restrictedProduct_open_boxes (hA : ∀ i, IsOpen (A i)) :
    TopologicalSpace.IsTopologicalBasis
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ C : ∀ i, Set (R i), (∀ i, IsOpen (C i)) ∧
          (∀ᶠ i in cofinite, C i = A i) ∧ s = {x | ∀ i, x i ∈ C i}} := by
  classical
  convert isTopologicalBasis_restrictedProduct_boxes hA
    (fun i ↦ TopologicalSpace.isTopologicalBasis_opens (α := R i)) using 1
  ext s
  constructor
  · rintro ⟨C, hC, hCA, rfl⟩
    refine ⟨(mem_cofinite.mp hCA).toFinset, fun i ↦ C i.1, fun i ↦ hC i.1, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Set.Finite.mem_toFinset, Set.mem_compl_iff, not_not]
    refine ⟨fun h ↦ ⟨fun i ↦ h i.1, fun i hi ↦ hi ▸ h i⟩, fun h i ↦ ?_⟩
    by_cases hi : C i = A i
    · exact hi ▸ h.2 i hi
    · exact h.1 ⟨i, (Set.Finite.mem_toFinset _).mpr hi⟩
  · rintro ⟨S, U, hU, rfl⟩
    refine ⟨fun i ↦ if hi : i ∈ S then U ⟨i, hi⟩ else A i, fun i ↦ ?_, ?_, ?_⟩
    · by_cases hi : i ∈ S
      · simpa [hi] using hU ⟨i, hi⟩
      · simpa [hi] using hA i
    · filter_upwards [S.finite_toSet.compl_mem_cofinite] with i hi
      have hi' : i ∉ S := hi
      simp [hi']
    · ext x
      simp only [Set.mem_ofPred_eq]
      exact ⟨fun h i ↦ by split_ifs with hi; exacts [h.1 ⟨i, hi⟩, h.2 i hi],
        fun h ↦ ⟨fun i ↦ by simpa [i.2] using h i.1, fun i hi ↦ by simpa [hi] using h i⟩⟩

/-- A restricted product of countably many second-countable spaces relative to open reference sets
is second countable. -/
theorem secondCountableTopology_restrictedProduct [Countable ι]
    [∀ i, SecondCountableTopology (R i)] (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  choose b hb_count _ hb using fun i ↦ TopologicalSpace.exists_countable_basis (R i)
  have (i : ι) : Countable (b i) := (hb_count i).to_subtype
  let f : (Σ S : Finset ι, ∀ i : S, b i.1) → Set (Πʳ i, [R i, A i]) :=
    fun p ↦ {x | (∀ i : p.1, x i ∈ (p.2 i : Set (R i.1))) ∧ ∀ i ∉ p.1, x i ∈ A i}
  have hrange : Set.range f =
      {s : Set (Πʳ i, [R i, A i]) |
        ∃ (S : Finset ι) (U : ∀ i : S, Set (R i)),
          (∀ i : S, U i ∈ b i.1) ∧
          s = {x | (∀ i : S, x i ∈ U i) ∧ ∀ i ∉ S, x i ∈ A i}} := by
    ext s
    constructor
    · rintro ⟨⟨S, U⟩, rfl⟩
      exact ⟨S, fun i ↦ (U i : Set (R i.1)), fun i ↦ (U i).2, rfl⟩
    · rintro ⟨S, U, hU, rfl⟩
      exact ⟨⟨S, fun i ↦ ⟨U i, hU i⟩⟩, rfl⟩
  have hbasis : TopologicalSpace.IsTopologicalBasis (Set.range f) := by
    rw [hrange]
    exact isTopologicalBasis_restrictedProduct_boxes hA hb
  exact ⟨⟨Set.range f, Set.countable_range f, hbasis.eq_generateFrom⟩⟩

/-- A restricted product of countably many second-countable spaces relative to open reference sets
is second countable. -/
instance instSecondCountableTopologyRestrictedProduct [Countable ι]
    [∀ i, SecondCountableTopology (R i)] [hA : Fact (∀ i, IsOpen (A i))] :
    SecondCountableTopology (Πʳ i, [R i, A i]) :=
  secondCountableTopology_restrictedProduct hA.out

end Bases

end TauCeti
