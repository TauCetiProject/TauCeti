/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.Connected.Clopen
public import Mathlib.Topology.Separation.Basic
public import Mathlib.SetTheory.Cardinal.Continuum

/-!
# Second countability and cardinality

A second-countable `T₀` space has at most continuum many points, since a point is determined by
the basic open sets containing it. An open-cover criterion also establishes second countability
of a preconnected space from second-countable pieces with countably many neighbours.

## Main results

* `TauCeti.secondCountableTopology_of_isOpen_cover`: a preconnected space covered by open
  second-countable subsets, each meeting only countably many cover members, is second countable.
* `TauCeti.secondCountableTopology_of_preimage_isOpen_cover`: a preconnected space mapping into a
  second-countable space whose image is covered by open sets with preimages covered by pairwise
  disjoint open second-countable pieces is second countable.
* `TauCeti.mk_le_continuum_of_secondCountableTopology`: a second-countable `T₀` space has at most
  `𝔠` points; in particular so does every Polish space.

## References

* A. S. Kechris, *Classical Descriptive Set Theory*, Graduate Texts in Mathematics 156,
  Springer, 1995, Corollary 6.3.
* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 4.40, for the open-cover chain argument.
-/

public section

open Set Function Cardinal TopologicalSpace

universe u

namespace TauCeti

/-- **A second-countable `T₀` space has at most continuum many points.** A point is determined
by the members of a countable basis containing it. In particular a Polish space has at most `𝔠`
points. -/
theorem mk_le_continuum_of_secondCountableTopology (X : Type u) [TopologicalSpace X]
    [SecondCountableTopology X] [T0Space X] : #X ≤ 𝔠 := by
  obtain ⟨b, hbc, hb⟩ := exists_countable_basis X
  have : Countable b := hbc.to_subtype
  have hinj : Injective fun x : X => {s : b | x ∈ (s : Set X)} := fun x y hxy =>
    hb.2.eq_iff.2 fun s hs => by simpa using congrArg (⟨s, hs⟩ ∈ ·) hxy
  calc #X ≤ #(Set b) := mk_le_of_injective hinj
    _ = 2 ^ #b := mk_set
    _ ≤ 2 ^ ℵ₀ := power_le_power_left two_ne_zero mk_le_aleph0
    _ = 𝔠 := two_power_aleph0

variable {E : Type*} [TopologicalSpace E]

/-- Let `V` be a cover of a preconnected space by open second-countable subsets, each of which
meets only countably many members of the cover. Then the space is second countable. -/
theorem secondCountableTopology_of_isOpen_cover [PreconnectedSpace E] {ι : Type*}
    (V : ι → Set E) (hVo : ∀ i, IsOpen (V i)) (hcover : ⋃ i, V i = Set.univ)
    (hV : ∀ i, SecondCountableTopology (V i))
    (hadj : ∀ i, {j | (V i ∩ V j).Nonempty}.Countable) : SecondCountableTopology E := by
  rcases isEmpty_or_nonempty E with hE | ⟨⟨x₀⟩⟩
  · exact secondCountableTopology_of_countable_cover (U := fun _ : Empty ↦ (∅ : Set E))
      (fun _ ↦ isOpen_empty) (Set.eq_univ_of_forall fun x ↦ hE.elim x)
  obtain ⟨a₀, ha₀⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x₀ : x₀ ∈ ⋃ i, V i)
  let reach : ℕ → Set ι := fun k ↦
    Nat.rec {a₀} (fun _ s ↦ ⋃ a ∈ s, {j | (V a ∩ V j).Nonempty}) k
  have hreach_succ (k : ℕ) : reach (k + 1) = ⋃ a ∈ reach k, {j | (V a ∩ V j).Nonempty} := rfl
  have hcount : ∀ k, (reach k).Countable := by
    intro k
    induction k with
    | zero => exact countable_singleton a₀
    | succ k ih => rw [hreach_succ]; exact ih.biUnion fun a _ ↦ hadj a
  set R := ⋃ k, reach k
  have hRc : R.Countable := countable_iUnion hcount
  have hstep {a b : ι} (ha : a ∈ R) (hab : (V a ∩ V b).Nonempty) : b ∈ R := by
    obtain ⟨k, hk⟩ := mem_iUnion.mp ha
    exact mem_iUnion.mpr ⟨k + 1, by rw [hreach_succ]; exact mem_biUnion hk hab⟩
  set W := ⋃ a ∈ R, V a with hW
  have hWo : IsOpen W := isOpen_biUnion fun a _ ↦ hVo a
  have hWc : IsClosed W := by
    refine isOpen_compl_iff.mp (isOpen_iff_forall_mem_open.mpr fun x hx ↦ ?_)
    obtain ⟨b, hb⟩ := mem_iUnion.mp (hcover.symm ▸ mem_univ x : x ∈ ⋃ i, V i)
    refine ⟨V b, fun y hy hyW ↦ ?_, hVo b, hb⟩
    obtain ⟨a, ha, hya⟩ := mem_iUnion₂.mp hyW
    exact hx (mem_iUnion₂.mpr ⟨b, hstep ha ⟨y, hya, hy⟩, hb⟩)
  have hWu : W = Set.univ :=
    IsClopen.eq_univ ⟨hWc, hWo⟩ ⟨x₀, mem_iUnion₂.mpr ⟨a₀, mem_iUnion.mpr ⟨0, rfl⟩, ha₀⟩⟩
  have := hRc.to_subtype
  exact secondCountableTopology_of_countable_cover (U := fun a : R ↦ V a) (fun a ↦ hVo a)
    (by rw [← hWu, hW, biUnion_eq_iUnion])

/-- Let `f : E → X` map a preconnected space `E` into a second-countable space `X`. Suppose `U` is a
family of open sets in `X` covering `range f`, and for each `i` the preimage `f ⁻¹' U i` is covered
by a pairwise disjoint family `S i` of open second-countable subsets of `E`. Then `E` is second
countable. -/
theorem secondCountableTopology_of_preimage_isOpen_cover [PreconnectedSpace E]
    {X : Type*} [TopologicalSpace X] [SecondCountableTopology X]
    {ι : Type*} {κ : ι → Type*} (f : E → X)
    (U : ι → Set X) (hUo : ∀ i, IsOpen (U i)) (hU : range f ⊆ ⋃ i, U i)
    (S : ∀ i, κ i → Set E) (hSo : ∀ i j, IsOpen (S i j))
    (hSsc : ∀ i j, SecondCountableTopology (S i j))
    (hSd : ∀ i, Pairwise (Disjoint on S i))
    (hSU : ∀ i, f ⁻¹' U i ⊆ ⋃ j, S i j) : SecondCountableTopology E := by
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable U hUo
  have := hTc.to_subtype
  let V : (Σ i : T, κ i.1) → Set E := fun a ↦ S a.1.1 a.2
  have hVo (a) : IsOpen (V a) := hSo a.1.1 a.2
  have hVsc (a) : SecondCountableTopology (V a) := hSsc a.1.1 a.2
  refine secondCountableTopology_of_isOpen_cover V hVo ?_ hVsc fun a ↦ ?_
  · refine eq_univ_of_forall fun e ↦ ?_
    have hx : f e ∈ ⋃ i ∈ T, U i := hTcover ▸ hU (mem_range_self e)
    obtain ⟨i, hiT, hei⟩ := mem_iUnion₂.mp hx
    obtain ⟨j, hj⟩ := mem_iUnion.mp (hSU i hei)
    exact mem_iUnion.mpr ⟨⟨⟨i, hiT⟩, j⟩, hj⟩
  · have hsub : {b | (V a ∩ V b).Nonempty} ⊆
        ⋃ i : T, Sigma.mk i '' {j | (V a ∩ S i.1 j).Nonempty} := by
      rintro ⟨i, j⟩ hb
      exact mem_iUnion.mpr ⟨i, j, hb, rfl⟩
    refine Countable.mono hsub (countable_iUnion fun i ↦ Countable.image ?_ _)
    have := (hVsc a).to_separableSpace
    exact Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun j ↦ ((↑) : V a → E) ⁻¹' S i.1 j)
      (a := {j | (V a ∩ S i.1 j).Nonempty})
      (fun j₁ _ j₂ _ hne ↦ (hSd i.1 hne).preimage _)
      (fun j _ ↦ (hSo i.1 j).preimage continuous_subtype_val)
      (fun j ⟨e, he, he'⟩ ↦ ⟨⟨e, he⟩, he'⟩)

end TauCeti
