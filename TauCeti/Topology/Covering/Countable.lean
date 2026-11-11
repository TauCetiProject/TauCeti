/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Covering.Basic

/-!
# Connected coverings of second-countable spaces are second countable

Let `p : E → X` be a covering map with `E` connected and `X` second countable. Then `E` is
second countable. No local connectedness, Hausdorff property or countability of the fibres is
assumed: the countability of the fibres is a consequence (`IsCoveringMap.countable_fiber`).

The proof is a chain argument. Countably many evenly covered open sets `U` cover `X`, and the
sheets over them are open subsets of `E`, each homeomorphic to its base `U` and hence second
countable. Two sheets over the same `U` are disjoint, so a given sheet meets only countably many
sheets over each `U`: they cut out pairwise disjoint nonempty open subsets of a separable space.
Thus every sheet has countably many neighbouring sheets, the sheets reachable from a fixed one by
finite chains of overlapping sheets are countably many, and their union is open and closed in `E`.
By connectedness it is all of `E`, a countable union of open second-countable subspaces
(`TauCeti.secondCountableTopology_of_isOpen_cover`).

## References

* John M. Lee, *Introduction to Smooth Manifolds*, second edition, Graduate Texts in
  Mathematics 218, Springer, 2013, Proposition 4.40.
* Allen Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Section 1.3.
-/

public section

open Set Topology TopologicalSpace

namespace TauCeti

variable {E : Type*} [TopologicalSpace E]

/-- Let `V` be a cover of a preconnected space by open second-countable subsets, each of which
meets only countably many members of the cover. Then the space is second countable. -/
theorem secondCountableTopology_of_isOpen_cover [PreconnectedSpace E] {ι : Type*}
    (V : ι → Set E) (hVo : ∀ i, IsOpen (V i)) (hcover : ⋃ i, V i = univ)
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
  set R := ⋃ k, reach k with hR
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
  have hWu : W = univ :=
    IsClopen.eq_univ ⟨hWc, hWo⟩ ⟨x₀, mem_iUnion₂.mpr ⟨a₀, mem_iUnion.mpr ⟨0, rfl⟩, ha₀⟩⟩
  have := hRc.to_subtype
  exact secondCountableTopology_of_countable_cover (U := fun a : R ↦ V a) (fun a ↦ hVo a)
    (by rw [← hWu, hW, biUnion_eq_iUnion])

variable {X : Type*} [TopologicalSpace X] {p : E → X}

/-- The sheet of an evenly covered open set `U` labelled by a point `i` of the fibre: the image
of `U × {i}` under the inverse of the trivialization. -/
private def sheet {U : Set X} {I : Type*} [TopologicalSpace I] (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    Set E :=
  range fun u : U ↦ (H.symm (u, i) : E)

private theorem isEmbedding_sheet {U : Set X} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (i : I) : IsEmbedding fun u : U ↦ (H.symm (u, i) : E) :=
  IsEmbedding.subtypeVal.comp (H.symm.isEmbedding.comp (isEmbedding_prodMkLeft i))

private theorem isOpen_sheet {U : Set X} (hfU : IsOpen (p ⁻¹' U)) {I : Type*}
    [TopologicalSpace I] [DiscreteTopology I] (H : p ⁻¹' U ≃ₜ U × I) (i : I) :
    IsOpen (sheet H i) := by
  have : sheet H i = Subtype.val '' (H ⁻¹' (univ ×ˢ {i})) := by
    ext e
    constructor
    · rintro ⟨u, rfl⟩
      exact ⟨H.symm (u, i), by simp, rfl⟩
    · rintro ⟨e', he', rfl⟩
      refine ⟨(H e').1, ?_⟩
      have h2 : (H e').2 = i := he'.2
      rw [← h2]
      simp
  rw [this]
  exact hfU.isOpenMap_subtype_val _ ((isOpen_univ.prod (isOpen_discrete _)).preimage H.continuous)

private theorem disjoint_sheet {U : Set X} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) {i j : I} (hij : i ≠ j) : Disjoint (sheet H i) (sheet H j) := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨u, rfl⟩ ⟨v, hv⟩
  exact hij (congrArg Prod.snd (H.symm.injective (Subtype.ext hv))).symm

private theorem mem_sheet {U : Set X} {I : Type*} [TopologicalSpace I]
    (H : p ⁻¹' U ≃ₜ U × I) (e : p ⁻¹' U) : (e : E) ∈ sheet H (H e).2 :=
  ⟨(H e).1, by simp⟩

/-- **Connected coverings of second-countable spaces are second countable.** The total space of
a covering map with connected total space over a second-countable space is second countable. -/
theorem _root_.IsCoveringMap.secondCountableTopology [SecondCountableTopology X]
    [PreconnectedSpace E] (hp : IsCoveringMap p) : SecondCountableTopology E := by
  choose hdisc U hxU hU hpU H _ using hp
  obtain ⟨T, hTc, hTcover⟩ := isOpen_iUnion_countable U hU
  have := hTc.to_subtype
  let V : (Σ x : T, p ⁻¹' {(x : X)}) → Set E := fun a ↦ sheet (H a.1) a.2
  have hVo (a) : IsOpen (V a) := by
    have := hdisc a.1
    exact isOpen_sheet (hpU a.1) (H a.1) a.2
  have hVsc (a) : SecondCountableTopology (V a) :=
    (isEmbedding_sheet (H a.1) a.2).toHomeomorph.symm.secondCountableTopology
  refine secondCountableTopology_of_isOpen_cover V hVo ?_ hVsc fun a ↦ ?_
  · refine eq_univ_of_forall fun e ↦ ?_
    have hx : p e ∈ ⋃ i ∈ T, U i := hTcover ▸ mem_iUnion.mpr ⟨p e, hxU (p e)⟩
    obtain ⟨x, hxT, hex⟩ := mem_iUnion₂.mp hx
    exact mem_iUnion.mpr ⟨⟨⟨x, hxT⟩, (H x ⟨e, hex⟩).2⟩, mem_sheet (H x) ⟨e, hex⟩⟩
  · have hsub : {b | (V a ∩ V b).Nonempty} ⊆
        ⋃ y : T, Sigma.mk y '' {j | (V a ∩ sheet (H y) j).Nonempty} := by
      rintro ⟨y, j⟩ hb
      exact mem_iUnion.mpr ⟨y, j, hb, rfl⟩
    refine Countable.mono hsub (countable_iUnion fun y ↦ Countable.image ?_ _)
    have := (hVsc a).to_separableSpace
    have hcount := Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun j ↦ ((↑) : V a → E) ⁻¹' sheet (H y) j)
      (a := {j | (V a ∩ sheet (H y) j).Nonempty})
      (fun i _ j _ hij ↦ ((disjoint_sheet (H y) hij).preimage _))
      (fun j _ ↦ by
        have := hdisc y
        exact (isOpen_sheet (hpU y) (H y) j).preimage continuous_subtype_val)
      (fun j ⟨e, he, he'⟩ ↦ ⟨⟨e, he⟩, he'⟩)
    exact hcount

/-- The fibres of a covering map with connected total space over a second-countable space are
countable. -/
theorem _root_.IsCoveringMap.countable_fiber [SecondCountableTopology X] [PreconnectedSpace E]
    (hp : IsCoveringMap p) (x : X) : Countable (p ⁻¹' {x}) := by
  have := hp.secondCountableTopology
  have := (hp x).discreteTopology_fiber
  exact separableSpace_iff_countable.mp inferInstance

end TauCeti
