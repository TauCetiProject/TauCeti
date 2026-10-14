/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Nonarchimedean.Basic

/-!
# Bounded subsets of topological modules

A subset `S` of a topological `R`-module `M` is *bounded* when every neighbourhood `U` of zero in
`M` contains `V • S` for some neighbourhood `V` of zero in `R`. Only the scalar action and the
two topologies enter, so no norm on `R` is needed; this is the notion of boundedness used for
modules over Huber rings (Wedhorn, *Adic Spaces*, Definition 5.27 and Remark 5.28). Boundedness
in a topological ring is the case of the ring acting on itself, which is developed in
`TauCeti.RingTheory.Huber.Bounded`.

Module boundedness is preserved by every linear map continuous at zero
(`TauCeti.IsModuleBounded.image`), because the neighbourhood of zero in the scalars does not have
to be transported along the map.

## Provenance

The calculus of subsets, unions and finite sets follows the ring calculus of William Coram's
mathlib4#40013, and its proofs adapt the proofs there. The images, products and nonarchimedean
sums are new.

## Main definitions

* `TauCeti.IsModuleBounded`: `S` is a bounded subset of a topological module.

## Main results

* `TauCeti.IsModuleBounded.image`: linear maps continuous at zero, in particular continuous
  linear maps, send bounded subsets of modules to bounded subsets.
* `TauCeti.isModuleBounded_prod_iff`: a subset of a product of two modules is bounded exactly
  when both of its projections are.
* `TauCeti.isModuleBounded_finite`: under a continuous scalar action, finite sets are bounded.
* `TauCeti.IsModuleBounded.add`, `TauCeti.IsModuleBounded.addSubgroupClosure`: in a module with a
  nonarchimedean additive group, sums and the generated additive subgroup of bounded sets stay
  bounded.

## Implementation notes

This is not Mathlib's `Bornology.IsVonNBounded`. That predicate asks that every neighbourhood of
zero absorb `S` after dilation by a norm-large scalar, so it needs a `SeminormedRing` of scalars;
a Huber ring such as `ℤ_[p]⟦T⟧` with its `(p, T)`-adic topology carries no such norm.

## References

* [Wedhorn, *Adic Spaces*][wedhorn_adic], Definition 5.27 and Remark 5.28.
* William Coram, *feat: define bounded sets and power bounded elements*,
  [mathlib4#40013](https://github.com/leanprover-community/mathlib4/pull/40013).

-/

public section

open Filter Pointwise Topology

namespace TauCeti

section Module

variable {R M N : Type*} [TopologicalSpace R] [TopologicalSpace M] [TopologicalSpace N]

section SMul

variable [Zero R] [Zero M] [SMul R M]

variable (R) in
/-- A subset `S` of a topological `R`-module `M` is *bounded* if for every neighbourhood `U` of `0`
in `M` there is a neighbourhood `V` of `0` in `R` with `V • S ⊆ U`.

Only the scalar action is used, so this applies to any topological space with zero carrying an
action of a topological space with zero. -/
def IsModuleBounded (S : Set M) : Prop := ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : R), V • S ⊆ U

/-- Unfolding lemma for `TauCeti.IsModuleBounded`. -/
theorem isModuleBounded_iff {S : Set M} :
    IsModuleBounded R S ↔ ∀ U ∈ 𝓝 (0 : M), ∃ V ∈ 𝓝 (0 : R), V • S ⊆ U := (Iff.rfl)

/-- Subsets of bounded sets are bounded. -/
theorem IsModuleBounded.subset {S T : Set M} (hS : IsModuleBounded R S) (hTS : T ⊆ S) :
    IsModuleBounded R T :=
  fun U hU ↦
    let ⟨V, hV, hVS⟩ := hS U hU
    ⟨V, hV, (Set.smul_subset_smul_left hTS).trans hVS⟩

variable (R) in
/-- The empty set is bounded. -/
@[simp]
theorem isModuleBounded_empty : IsModuleBounded R (∅ : Set M) :=
  fun _ _ ↦ ⟨Set.univ, univ_mem, by simp⟩

/-- A finite union of bounded sets is bounded. -/
theorem isModuleBounded_iUnion {ι : Sort*} [Finite ι] {S : ι → Set M}
    (hS : ∀ i, IsModuleBounded R (S i)) : IsModuleBounded R (⋃ i, S i) := by
  intro U hU
  choose V hV hVS using fun i ↦ hS i U hU
  refine ⟨⋂ i, V i, Filter.iInter_mem.mpr hV, ?_⟩
  rw [Set.smul_iUnion]
  exact Set.iUnion_subset fun i ↦
    (Set.smul_subset_smul_right (Set.iInter_subset _ i)).trans (hVS i)

/-- A finite indexed union is bounded exactly when every piece is. -/
@[simp]
theorem isModuleBounded_iUnion_iff {ι : Sort*} [Finite ι] {S : ι → Set M} :
    IsModuleBounded R (⋃ i, S i) ↔ ∀ i, IsModuleBounded R (S i) :=
  ⟨fun h i ↦ h.subset (Set.subset_iUnion _ i), isModuleBounded_iUnion⟩

/-- The union of two bounded sets is bounded. -/
theorem IsModuleBounded.union {S T : Set M} (hS : IsModuleBounded R S)
    (hT : IsModuleBounded R T) : IsModuleBounded R (S ∪ T) := by
  rw [Set.union_eq_iUnion]
  exact isModuleBounded_iUnion (by rintro (_ | _) <;> assumption)

/-- A union is bounded exactly when both parts are. -/
@[simp]
theorem isModuleBounded_union {S T : Set M} :
    IsModuleBounded R (S ∪ T) ↔ IsModuleBounded R S ∧ IsModuleBounded R T :=
  ⟨fun h ↦ ⟨h.subset Set.subset_union_left, h.subset Set.subset_union_right⟩,
    fun h ↦ h.1.union h.2⟩

/-- **Images of bounded sets under linear maps continuous at zero are bounded.** This covers
continuous linear maps. Unlike `TauCeti.Huber.IsBounded.image` for ring homomorphisms, no
openness is needed: the neighbourhood of zero in the scalars is not transported. -/
theorem IsModuleBounded.image [Zero N] [SMul R N] {F : Type*} [FunLike F M N]
    [ZeroHomClass F M N] [MulActionHomClass F R M N] {f : F} (hf : ContinuousAt f 0)
    {S : Set M} (hS : IsModuleBounded R S) : IsModuleBounded R (f '' S) := by
  intro U hU
  obtain ⟨V, hV, hVS⟩ := hS (f ⁻¹' U) (hf.preimage_mem_nhds (by rwa [map_zero]))
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
  simpa [map_smul] using hVS (Set.smul_mem_smul hv hs)

/-- A subset of a product of two modules is bounded exactly when both of its projections are. -/
@[simp]
theorem isModuleBounded_prod_iff [Zero N] [SMul R N] {S : Set (M × N)} :
    IsModuleBounded R S ↔
      IsModuleBounded R (Prod.fst '' S) ∧ IsModuleBounded R (Prod.snd '' S) := by
  refine ⟨fun hS ↦ ⟨fun U hU ↦ ?_, fun U hU ↦ ?_⟩, fun ⟨h₁, h₂⟩ U hU ↦ ?_⟩
  · obtain ⟨V, hV, hVS⟩ := hS (U ×ˢ Set.univ) (prod_mem_nhds hU univ_mem)
    refine ⟨V, hV, ?_⟩
    rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.smul_mem_smul hv hs)).1
  · obtain ⟨V, hV, hVS⟩ := hS (Set.univ ×ˢ U) (prod_mem_nhds univ_mem hU)
    refine ⟨V, hV, ?_⟩
    rintro _ ⟨v, hv, _, ⟨s, hs, rfl⟩, rfl⟩
    exact (hVS (Set.smul_mem_smul hv hs)).2
  · obtain ⟨U₁, hU₁, U₂, hU₂, hU⟩ := mem_nhds_prod_iff.mp hU
    obtain ⟨V₁, hV₁, hVS₁⟩ := h₁ U₁ hU₁
    obtain ⟨V₂, hV₂, hVS₂⟩ := h₂ U₂ hU₂
    refine ⟨V₁ ∩ V₂, inter_mem hV₁ hV₂, ?_⟩
    rintro _ ⟨v, hv, s, hs, rfl⟩
    exact hU ⟨hVS₁ (Set.smul_mem_smul hv.1 ⟨s, hs, rfl⟩),
      hVS₂ (Set.smul_mem_smul hv.2 ⟨s, hs, rfl⟩)⟩

/-- The product of two bounded sets is bounded. -/
theorem IsModuleBounded.prod [Zero N] [SMul R N] {S : Set M} {T : Set N}
    (hS : IsModuleBounded R S) (hT : IsModuleBounded R T) : IsModuleBounded R (S ×ˢ T) :=
  isModuleBounded_prod_iff.mpr ⟨hS.subset (Set.fst_image_prod_subset S T),
    hT.subset (Set.snd_image_prod_subset S T)⟩

end SMul

section SMulZeroClass

variable [Zero R] [Zero M] [SMulZeroClass R M]

variable (R) in
/-- The singleton `{0}` is bounded. -/
@[simp]
theorem isModuleBounded_singleton_zero : IsModuleBounded R ({0} : Set M) :=
  fun U hU ↦ ⟨Set.univ, univ_mem, fun _ hx ↦ by simp_all [mem_of_mem_nhds hU]⟩

end SMulZeroClass

section ContinuousSMul

variable [Zero R] [Zero M] [SMulWithZero R M] [ContinuousSMul R M]

variable (R) in
/-- Every singleton is bounded. -/
@[simp]
theorem isModuleBounded_singleton (m : M) : IsModuleBounded R ({m} : Set M) :=
  fun U hU ↦ ⟨(· • m) ⁻¹' U, (continuous_id.smul continuous_const).continuousAt.preimage_mem_nhds
    (by simp [hU]), by simp⟩

variable (R) in
/-- Every finite subset is bounded. -/
theorem isModuleBounded_finite {S : Set M} (hS : S.Finite) : IsModuleBounded R S := by
  refine Set.Finite.induction_on S hS (isModuleBounded_empty R) fun {m s} _ _ ih ↦ ?_
  exact Set.insert_eq m s ▸ (isModuleBounded_singleton R m).union ih

end ContinuousSMul

section Nonarchimedean

variable [Zero R] [AddGroup M] [NonarchimedeanAddGroup M] [DistribSMul R M]

/-- The additive subgroup generated by a bounded subset of a module with a nonarchimedean
additive group is bounded. -/
theorem IsModuleBounded.addSubgroupClosure {S : Set M} (hS : IsModuleBounded R S) :
    IsModuleBounded R (AddSubgroup.closure S : Set M) := by
  intro U hU
  obtain ⟨G, hGU⟩ := NonarchimedeanAddGroup.is_nonarchimedean U hU
  obtain ⟨V, hV, hVS⟩ := hS _ (G.isOpen.mem_nhds G.zero_mem)
  refine ⟨V, hV, ?_⟩
  rintro _ ⟨v, hv, x, hx, rfl⟩
  refine hGU (?_ : v • x ∈ (G : Set M))
  induction hx using AddSubgroup.closure_induction with
  | mem s hs => exact hVS (Set.smul_mem_smul hv hs)
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact G.toAddSubgroup.add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact G.toAddSubgroup.neg_mem hx

/-- The pointwise sum of two bounded subsets of a module with a nonarchimedean additive group is
bounded. -/
theorem IsModuleBounded.add {S T : Set M} (hS : IsModuleBounded R S)
    (hT : IsModuleBounded R T) : IsModuleBounded R (S + T) := by
  refine (hS.union hT).addSubgroupClosure.subset ?_
  rintro _ ⟨s, hs, t, ht, rfl⟩
  exact AddSubgroup.add_mem _ (AddSubgroup.subset_closure (.inl hs))
    (AddSubgroup.subset_closure (.inr ht))

end Nonarchimedean

end Module

end TauCeti
