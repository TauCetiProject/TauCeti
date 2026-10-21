/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Equidecomp
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Data.Set.Lattice.Disjoint
public import Mathlib.SetTheory.Cardinal.SchroederBernstein

/-!
# Equidecomposability of sets

Let `G` act on `X`. Two sets `A B : Set X` are *equidecomposable*, `TauCeti.Equidecomposable G A B`,
when some `Equidecomp X G` (a partial bijection that moves each point of its source by one of
finitely many elements of `G`) has source `A` and target `B`. Equivalently, `A` can be cut into
finitely many pieces which, each moved by a single element of `G`, reassemble into `B`. The set `A`
is *equidecomposable with a subset of* `B`, `TauCeti.EquidecomposableLE G A B`, when it is
equidecomposable with some `B' ⊆ B`.

This file shows that equidecomposability is an equivalence relation stable under restriction to
subsets, finite disjoint unions, single translations, equivariant bijections and changes of the
acting group that do not change the action, and that `EquidecomposableLE G` is a preorder. The main
result is the Schröder–Bernstein theorem for equidecompositions (`EquidecomposableLE.antisymm`):
if each of `A` and `B` is equidecomposable with a subset of the other, then `A` and `B` are
equidecomposable. It follows from Mathlib's Schröder–Bernstein theorem for injections preserving a
relation (`Function.Embedding.schroeder_bernstein_of_rel`), so the resulting equidecomposition uses
only the finitely many group elements of the first given equidecomposition together with the
inverses of those of the second.
These are the basic tools for paradoxical decompositions, for instance in Tarski's characterization
of amenable groups.

## Main definitions

* `Equidecomp.disjointUnion`: the union of two equidecompositions with disjoint sources and
  disjoint targets.
* `TauCeti.Equidecomposable G A B`: `A` and `B` are equidecomposable using `G`.
* `TauCeti.EquidecomposableLE G A B`: `A` is equidecomposable with a subset of `B`.

## Main results

* `TauCeti.Equidecomposable.equivalence`: equidecomposability is an equivalence relation.
* `TauCeti.Equidecomposable.biUnion_finset`: finite disjoint unions of equidecomposable families
  are equidecomposable.
* `TauCeti.Equidecomposable.exists_subset_and_sdiff`: restricting an equidecomposition to a subset
  `A' ⊆ A` splits both `A' ∼ B'` and `A \ A' ∼ B \ B'` off it.
* `TauCeti.EquidecomposableLE.antisymm`: the Schröder–Bernstein theorem for equidecompositions.
* `TauCeti.equidecomposable_iff_equidecomposableLE`: equidecomposability is the equivalence
  relation induced by the preorder `EquidecomposableLE G`.

## References

* G. Tomkowicz, S. Wagon, *The Banach–Tarski Paradox*, 2nd ed., Chapter 3, for the
  Banach–Schröder–Bernstein theorem and its proof.
* A. Garrido, *An introduction to amenable groups*, §1.
-/

public section

open Function Set Pointwise

variable {X Y G H : Type*}

namespace Equidecomp

section SMul

variable [SMul G X]

/-- The union of two equidecompositions with disjoint sources and disjoint targets: it acts as
`f` on `f.source` and as `f'` on `f'.source`. -/
def disjointUnion (f f' : Equidecomp X G) (hs : Disjoint f.source f'.source)
    (ht : Disjoint f.target f'.target) [∀ x, Decidable (x ∈ f.source)]
    [∀ y, Decidable (y ∈ f.target)] : Equidecomp X G where
  toPartialEquiv := f.toPartialEquiv.disjointUnion f'.toPartialEquiv hs ht
  isDecompOn' := by
    classical
    refine ⟨f.witness ∪ f'.witness, fun a ha => ?_⟩
    by_cases h : a ∈ f.source
    · obtain ⟨g, hg, hga⟩ := f.isDecompOn a h
      exact ⟨g, Finset.mem_union_left _ hg, by
        simpa [PartialEquiv.disjointUnion_apply, piecewise_eq_of_mem _ _ _ h] using hga⟩
    · have h' : a ∈ f'.source := (PartialEquiv.disjointUnion_source _ _ hs ht ▸ ha).resolve_left h
      obtain ⟨g, hg, hga⟩ := f'.isDecompOn a h'
      exact ⟨g, Finset.mem_union_right _ hg, by
        simpa [PartialEquiv.disjointUnion_apply, piecewise_eq_of_notMem _ _ _ h] using hga⟩

@[simp]
theorem disjointUnion_toPartialEquiv (f f' : Equidecomp X G) (hs : Disjoint f.source f'.source)
    (ht : Disjoint f.target f'.target) [∀ x, Decidable (x ∈ f.source)]
    [∀ y, Decidable (y ∈ f.target)] :
    (f.disjointUnion f' hs ht).toPartialEquiv =
      f.toPartialEquiv.disjointUnion f'.toPartialEquiv hs ht :=
  (rfl)

/-- The union of two equidecompositions acts as the first on its source and as the second
elsewhere. -/
theorem disjointUnion_apply (f f' : Equidecomp X G) (hs : Disjoint f.source f'.source)
    (ht : Disjoint f.target f'.target) [∀ x, Decidable (x ∈ f.source)]
    [∀ y, Decidable (y ∈ f.target)] :
    ⇑(f.disjointUnion f' hs ht) = f.source.piecewise f f' :=
  (rfl)

/-- The target of the restriction of an equidecomposition to a subset of its source is the image
of that subset. -/
theorem target_restr (f : Equidecomp X G) {A : Set X} (hA : A ⊆ f.source) :
    (f.restr A).target = f '' A :=
  (f.toPartialEquiv.image_eq_target_inter_inv_preimage hA).symm

end SMul

end Equidecomp

namespace TauCeti

section SMul

variable [SMul G X]

variable (G) in
/-- Two sets `A B : Set X` are *equidecomposable* using `G` when some equidecomposition has source
`A` and target `B`: `A` can be cut into finitely many pieces which, each moved by a single element
of `G`, reassemble into `B`. -/
def Equidecomposable (A B : Set X) : Prop :=
  ∃ f : Equidecomp X G, f.source = A ∧ f.target = B

variable (G) in
/-- A set `A` is *equidecomposable with a subset of* `B` using `G`. For a monoid action this is a
preorder, and for a group action its induced equivalence relation is `Equidecomposable G`
(`equidecomposable_iff_equidecomposableLE`). -/
def EquidecomposableLE (A B : Set X) : Prop :=
  ∃ B' ⊆ B, Equidecomposable G A B'

variable {A A' B B' : Set X}

/-- Unfolds `Equidecomposable`: some equidecomposition has source `A` and target `B`. -/
theorem equidecomposable_iff :
    Equidecomposable G A B ↔ ∃ f : Equidecomp X G, f.source = A ∧ f.target = B :=
  Iff.rfl

/-- Unfolds `EquidecomposableLE`: `A` is equidecomposable with some subset of `B`. -/
theorem equidecomposableLE_iff :
    EquidecomposableLE G A B ↔ ∃ B' ⊆ B, Equidecomposable G A B' :=
  Iff.rfl

/-- The source and target of an equidecomposition are equidecomposable. -/
theorem _root_.Equidecomp.equidecomposable (f : Equidecomp X G) :
    Equidecomposable G f.source f.target :=
  ⟨f, rfl, rfl⟩

/-- A subset of the source of an equidecomposition is equidecomposable with its image. -/
theorem _root_.Equidecomp.equidecomposable_image (f : Equidecomp X G) (hA : A ⊆ f.source) :
    Equidecomposable G A (f '' A) :=
  ⟨f.restr A, f.source_restr hA, f.target_restr hA⟩

/-- The empty set is equidecomposable with itself. -/
@[simp]
theorem equidecomposable_empty : Equidecomposable G (∅ : Set X) ∅ :=
  ⟨⟨(PartialEquiv.refl X).restr ∅, ∅, fun _ ha => by simp at ha⟩, by simp, by simp⟩

/-- Restricting an equidecomposition of `A` with `B` to `A' ⊆ A` makes `A'` equidecomposable with
some `B' ⊆ B`, and the remaining pieces `A \ A'` and `B \ B'` equidecomposable too. -/
theorem Equidecomposable.exists_subset_and_sdiff (h : Equidecomposable G A B) (hA' : A' ⊆ A) :
    ∃ B' ⊆ B, Equidecomposable G A' B' ∧ Equidecomposable G (A \ A') (B \ B') := by
  obtain ⟨f, rfl, rfl⟩ := h
  refine ⟨f '' A', f.image_source_eq_target ▸ image_mono hA', f.equidecomposable_image hA', ?_⟩
  have := f.equidecomposable_image (A := f.source \ A') sdiff_subset
  rwa [f.injOn.image_sdiff_subset hA', f.image_source_eq_target] at this

/-- A subset of a set equidecomposable with `B` is equidecomposable with a subset of `B`. -/
theorem Equidecomposable.equidecomposableLE_of_subset (h : Equidecomposable G A B)
    (hA' : A' ⊆ A) : EquidecomposableLE G A' B :=
  let ⟨B', hB', h', _⟩ := h.exists_subset_and_sdiff hA'
  ⟨B', hB', h'⟩

/-- If `A` is equidecomposable with `B`, then `A` is equidecomposable with a subset of `B`. -/
theorem Equidecomposable.equidecomposableLE (h : Equidecomposable G A B) :
    EquidecomposableLE G A B :=
  ⟨B, subset_rfl, h⟩

/-- Unions of equidecomposable pairs with disjoint sources and disjoint targets are
equidecomposable. -/
theorem Equidecomposable.union {A₁ A₂ B₁ B₂ : Set X} (h₁ : Equidecomposable G A₁ B₁)
    (h₂ : Equidecomposable G A₂ B₂) (hA : Disjoint A₁ A₂) (hB : Disjoint B₁ B₂) :
    Equidecomposable G (A₁ ∪ A₂) (B₁ ∪ B₂) := by
  classical
  obtain ⟨f, rfl, rfl⟩ := h₁
  obtain ⟨f', rfl, rfl⟩ := h₂
  exact ⟨f.disjointUnion f' hA hB, rfl, rfl⟩

/-- Finite unions of pairwise disjoint families, termwise equidecomposable, are
equidecomposable. -/
theorem Equidecomposable.biUnion_finset {ι : Type*} {s : Finset ι} {A B : ι → Set X}
    (h : ∀ i ∈ s, Equidecomposable G (A i) (B i)) (hA : (s : Set ι).PairwiseDisjoint A)
    (hB : (s : Set ι).PairwiseDisjoint B) :
    Equidecomposable G (⋃ i ∈ s, A i) (⋃ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.coe_insert, pairwiseDisjoint_insert] at hA hB
    simp only [Finset.set_biUnion_insert]
    have hne : ∀ j ∈ s, i ≠ j := fun j hj hij => hi (hij ▸ hj)
    refine (h i (Finset.mem_insert_self i s)).union
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) hA.1 hB.1) ?_ ?_
    · exact disjoint_iUnion₂_right.2 fun j hj => hA.2 j hj (hne j hj)
    · exact disjoint_iUnion₂_right.2 fun j hj => hB.2 j hj (hne j hj)

/-- An equidecomposition using `G` is one using `H` when each element of `G` acts as some element
of `H` does. -/
theorem Equidecomposable.of_smul_eq [SMul H X] (φ : G → H)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) (h : Equidecomposable G A B) :
    Equidecomposable H A B := by
  classical
  obtain ⟨f, rfl, rfl⟩ := h
  refine ⟨⟨f.toPartialEquiv, f.witness.image φ, fun a ha => ?_⟩, rfl, rfl⟩
  obtain ⟨g, hg, hga⟩ := f.isDecompOn a ha
  exact ⟨φ g, Finset.mem_image_of_mem φ hg, by rw [hφ]; exact hga⟩

/-- Equidecomposability does not depend on the acting group, only on the transformations through
which it acts: a surjection `φ : G → H` with `φ g • x = g • x` identifies equidecomposability using
`G` and using `H`. This applies in particular to a group isomorphism. -/
theorem equidecomposable_iff_of_surjective [SMul H X] {φ : G → H} (hφs : Surjective φ)
    (hφ : ∀ (g : G) (x : X), φ g • x = g • x) :
    Equidecomposable G A B ↔ Equidecomposable H A B :=
  ⟨Equidecomposable.of_smul_eq φ hφ, Equidecomposable.of_smul_eq (fun h => (hφs h).choose)
    fun h x => by rw [← hφ, (hφs h).choose_spec]⟩

/-- An equivariant bijection `e : X ≃ Y` carries equidecomposable sets to equidecomposable sets. -/
theorem Equidecomposable.image_equiv [SMul G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) (h : Equidecomposable G A B) :
    Equidecomposable G (e '' A) (e '' B) := by
  obtain ⟨f, rfl, rfl⟩ := h
  refine ⟨⟨e.symm.transPartialEquiv (f.toPartialEquiv.transEquiv e), f.witness, fun y hy => ?_⟩,
    ?_, ?_⟩
  · obtain ⟨g, hg, hga⟩ := f.isDecompOn _ hy
    exact ⟨g, hg, by simpa [he] using congrArg e hga⟩
  · simp [e.image_eq_preimage_symm]
  · simp [e.image_eq_preimage_symm]

/-- Equidecomposability is invariant under equivariant bijections. -/
theorem equidecomposable_image_equiv_iff [SMul G Y] (e : X ≃ Y)
    (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Equidecomposable G (e '' A) (e '' B) ↔ Equidecomposable G A B := by
  refine ⟨fun h => ?_, Equidecomposable.image_equiv e he⟩
  have he' : ∀ (g : G) (y : Y), e.symm (g • y) = g • e.symm y := fun g y => by
    rw [e.symm_apply_eq, he, e.apply_symm_apply]
  simpa [e.symm_image_image] using h.image_equiv e.symm he'

end SMul

section Monoid

variable [Monoid G] [MulAction G X] {A B C : Set X}

/-- Every set is equidecomposable with itself. -/
@[refl, simp]
theorem Equidecomposable.refl (A : Set X) : Equidecomposable G A A :=
  ⟨(Equidecomp.refl X G).restr A, by simp, by simp⟩

/-- Equidecomposability is transitive. -/
@[trans]
theorem Equidecomposable.trans (h₁ : Equidecomposable G A B) (h₂ : Equidecomposable G B C) :
    Equidecomposable G A C := by
  obtain ⟨f, rfl, rfl⟩ := h₁
  obtain ⟨f', hf', rfl⟩ := h₂
  refine ⟨f.trans f', ?_, ?_⟩
  · simpa [hf'] using f.toPartialEquiv.mapsTo.subset_preimage
  · simpa [← hf'] using f'.toPartialEquiv.mapsTo_symm.subset_preimage

/-- A subset of `B` is equidecomposable with a subset of `B`. -/
theorem equidecomposableLE_of_subset (h : A ⊆ B) : EquidecomposableLE G A B :=
  ⟨A, h, .refl A⟩

/-- Every set is equidecomposable with a subset of itself. -/
@[refl, simp]
theorem EquidecomposableLE.refl (A : Set X) : EquidecomposableLE G A A :=
  equidecomposableLE_of_subset subset_rfl

/-- Being equidecomposable with a subset is transitive. -/
@[trans]
theorem EquidecomposableLE.trans (h₁ : EquidecomposableLE G A B)
    (h₂ : EquidecomposableLE G B C) : EquidecomposableLE G A C := by
  obtain ⟨B', hB', h₁⟩ := h₁
  obtain ⟨C', hC', h₂⟩ := h₂
  obtain ⟨C'', hC'', h₂'⟩ := h₂.equidecomposableLE_of_subset hB'
  exact ⟨C'', hC''.trans hC', h₁.trans h₂'⟩

instance : IsPreorder (Set X) (EquidecomposableLE G) where
  refl := EquidecomposableLE.refl
  trans _ _ _ := EquidecomposableLE.trans

end Monoid

section Group

variable [Group G] [MulAction G X] {A B : Set X}

/-- Equidecomposability is symmetric. -/
@[symm]
theorem Equidecomposable.symm (h : Equidecomposable G A B) : Equidecomposable G B A := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨f.symm, rfl, rfl⟩

/-- Equidecomposability is a symmetric relation. -/
theorem equidecomposable_comm : Equidecomposable G A B ↔ Equidecomposable G B A :=
  ⟨Equidecomposable.symm, Equidecomposable.symm⟩

variable (G X) in
/-- Equidecomposability is an equivalence relation on `Set X`. -/
theorem Equidecomposable.equivalence : Equivalence (Equidecomposable G (X := X)) :=
  ⟨Equidecomposable.refl, Equidecomposable.symm, Equidecomposable.trans⟩

/-- A set is equidecomposable with each of its translates. -/
theorem equidecomposable_smul_set (g : G) (A : Set X) : Equidecomposable G A (g • A) := by
  refine ⟨⟨(MulAction.toPerm g : Equiv.Perm X).toPartialEquiv.restr A, {g}, fun a _ => ?_⟩,
    by simp, ?_⟩
  · exact ⟨g, Finset.mem_singleton_self g, rfl⟩
  · ext x
    simp [mem_smul_set_iff_inv_smul_mem]

/-- **Schröder–Bernstein theorem for equidecompositions.** If each of `A` and `B` is
equidecomposable with a subset of the other, then `A` and `B` are equidecomposable. -/
theorem EquidecomposableLE.antisymm (hAB : EquidecomposableLE G A B)
    (hBA : EquidecomposableLE G B A) : Equidecomposable G A B := by
  classical
  obtain ⟨B', hB', f, rfl, rfl⟩ := hAB
  obtain ⟨A', hA', g, rfl, rfl⟩ := hBA
  obtain hX | hX := isEmpty_or_nonempty X
  · simp [eq_empty_of_isEmpty]
  -- Schröder–Bernstein for the induced injections `f.source → g.source → f.source`, keeping track
  -- of the group element moving each point.
  obtain ⟨h, hh, hR⟩ := Embedding.schroeder_bernstein_of_rel
    (f := fun a : f.source => (⟨f a, hB' (f.apply_mem_target a.2)⟩ : g.source))
    (g := fun b : g.source => (⟨g b, hA' (g.apply_mem_target b.2)⟩ : f.source))
    (fun a b hab => Subtype.ext (f.injOn a.2 b.2 (congrArg Subtype.val hab)))
    (fun a b hab => Subtype.ext (g.injOn a.2 b.2 (congrArg Subtype.val hab)))
    (fun a b => ∃ k ∈ f.witness ∪ g.witness⁻¹, (b : X) = k • (a : X))
    (fun a => let ⟨k, hk, e⟩ := f.isDecompOn a a.2; ⟨k, Finset.mem_union_left _ hk, e⟩)
    (fun b => let ⟨k, hk, e⟩ := g.isDecompOn b b.2
      ⟨k⁻¹, Finset.mem_union_right _ (Finset.inv_mem_inv hk), by simp [e]⟩)
  let F : X → X := fun x => if hx : x ∈ f.source then h ⟨x, hx⟩ else x
  have hF : BijOn F f.source g.source := by
    refine ⟨fun x hx => by simp [F, hx], fun x hx y hy hxy => ?_, fun y hy => ?_⟩
    · exact congrArg Subtype.val (hh.1 (Subtype.ext (by simpa [F, hx, hy] using hxy)) :
        (⟨x, hx⟩ : f.source) = ⟨y, hy⟩)
    · obtain ⟨a, ha⟩ := hh.2 ⟨y, hy⟩
      exact ⟨a, a.2, by simp [F, ha]⟩
  refine ⟨⟨hF.toPartialEquiv F _ _, f.witness ∪ g.witness⁻¹, fun a ha => ?_⟩, rfl, rfl⟩
  obtain ⟨k, hk, e⟩ := hR ⟨a, ha⟩
  exact ⟨k, hk, (dite_eq_left_of_eq_true (eq_true ha)).trans e⟩

/-- Equidecomposability is the equivalence relation induced by the preorder
`EquidecomposableLE G`. -/
theorem equidecomposable_iff_equidecomposableLE :
    Equidecomposable G A B ↔ EquidecomposableLE G A B ∧ EquidecomposableLE G B A :=
  ⟨fun h => ⟨h.equidecomposableLE, h.symm.equidecomposableLE⟩, fun h => h.1.antisymm h.2⟩

end Group

end TauCeti
