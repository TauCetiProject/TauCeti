/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.Complex.Basic
public import TauCeti.AlgebraicTopology.SimplicialComplex.Maps
public import Mathlib.Data.Fintype.CardEmbedding

/-!
# Labeled copies of finite hypergraph complexes

A copy of a complex is an injective map of its ambient vertices preserving every face.
These copies need not be induced: a nonface may map to a face. Vertices outside all faces
are still labeled vertices and must also be mapped injectively. The source and target may
have different rank bounds.

`HypergraphComplex.IsCopy` uses containment of the image of the underlying pre-abstract
simplicial complex. Its graded characterization also accounts for the empty face, which
is absent from the precomplex. On finite vertex types, `copies` enumerates the eligible
injections and `labelledCopyCount` counts them without dividing by automorphisms.
Postcomposition with a copy gives an injection of copy sets, so these counts are monotone
under containment of hosts and bounded by the falling factorial of the host size.

This follows the labeled, edge-preserving convention of Mathlib's `SimpleGraph.Copy` and
`SimpleGraph.labelledCopyCount`, using the existing simplicial-map image API.
-/

public section

open Finset

namespace TauCeti.HypergraphComplex

variable {r s t : ℕ} {U V W : Type*} [DecidableEq V] [DecidableEq W]
  {C : HypergraphComplex r U} {D : HypergraphComplex s V} {E : HypergraphComplex t W}

/-- An injection is a copy when it preserves every face. Nonfaces need not be preserved,
and the injection includes ambient vertices not occurring in any face. -/
def IsCopy (D : HypergraphComplex s V) (C : HypergraphComplex r U) (f : U ↪ V) : Prop :=
  C.toPreAbstractSimplicialComplex.map f ≤ D.toPreAbstractSimplicialComplex

/-- A copy preserves each graded face, including the empty face, at the same cardinality.
In particular, every occupied source level also exists within the target rank bound. -/
theorem IsCopy.map_face {f : U ↪ V} (h : D.IsCopy C f) {k : ℕ} (hk : k ≤ r)
    {a : Finset U} (ha : a ∈ C.faces k hk) :
    ∃ hk' : k ≤ s, a.map f ∈ D.faces k hk' := by
  have hcard := C.face_card k hk a ha
  obtain rfl | hne := a.eq_empty_or_nonempty
  · simp only [card_empty] at hcard
    subst k
    exact ⟨Nat.zero_le _, by simp⟩
  · have hpre : a ∈ C.toPreAbstractSimplicialComplex :=
      (C.mem_toPreAbstractSimplicialComplex _).2
        ⟨hne, hcard ▸ hk, by simpa only [hcard] using ha⟩
    have him := h (_root_.PreAbstractSimplicialComplex.mem_map_iff.2 ⟨a, hpre, rfl⟩)
    rw [← map_eq_image] at him
    obtain ⟨-, hle, hface⟩ := (D.mem_toPreAbstractSimplicialComplex _).1 him
    have him : ∃ hk' : #(a.map f) ≤ s, a.map f ∈ D.faces #(a.map f) hk' := ⟨hle, hface⟩
    simpa only [card_map, hcard] using him

/-- An injection is a copy exactly when it preserves every graded face. -/
theorem isCopy_iff (D : HypergraphComplex s V) (C : HypergraphComplex r U) (f : U ↪ V) :
    D.IsCopy C f ↔ ∀ k (hk : k ≤ r), ∀ a ∈ C.faces k hk,
      ∃ hk' : k ≤ s, a.map f ∈ D.faces k hk' := by
  refine ⟨fun h _ hk _ ha ↦ h.map_face hk ha, ?_⟩
  intro h
  rw [IsCopy, _root_.PreAbstractSimplicialComplex.SimplicialMap.map_le_iff]
  intro a ha
  obtain ⟨hne, hk, ha⟩ := (C.mem_toPreAbstractSimplicialComplex _).1 ha
  obtain ⟨hk', hf⟩ := h _ hk a ha
  rw [← map_eq_image, D.mem_toPreAbstractSimplicialComplex]
  exact ⟨hne.map, by simpa only [card_map] using hk', by simpa only [card_map] using hf⟩

/-- The identity injection is a copy. -/
@[simp]
theorem isCopy_refl [DecidableEq U] (C : HypergraphComplex r U) :
    C.IsCopy C (Function.Embedding.refl U) := by
  rw [IsCopy, Function.Embedding.coe_refl, _root_.PreAbstractSimplicialComplex.map_id]

/-- Composing two face-preserving injections gives a face-preserving injection. -/
theorem IsCopy.comp {f : U ↪ V} {g : V ↪ W} (hg : E.IsCopy D g) (hf : D.IsCopy C f) :
    E.IsCopy C (f.trans g) := by
  rw [IsCopy, _root_.PreAbstractSimplicialComplex.SimplicialMap.map_le_iff] at hg hf ⊢
  intro a ha
  simpa only [Function.Embedding.coe_trans, Finset.image_comp] using hg (hf ha)

section Finite

variable [Fintype U] [Fintype V]

open Classical in
/-- All labeled copies of `C` in `D`, represented by their vertex injections. -/
noncomputable def copies (D : HypergraphComplex s V) (C : HypergraphComplex r U) :
    Finset (U ↪ V) :=
  univ.filter (D.IsCopy C)

/-- Membership in the copy set means that the injection preserves faces. -/
@[simp]
theorem mem_copies (D : HypergraphComplex s V) (C : HypergraphComplex r U) (f : U ↪ V) :
    f ∈ D.copies C ↔ D.IsCopy C f := by
  classical
  simp [copies]

/-- The number of labeled face-preserving injections, without quotienting by automorphisms. -/
noncomputable def labelledCopyCount (D : HypergraphComplex s V) (C : HypergraphComplex r U) : ℕ :=
  #(D.copies C)

/-- The labeled count is the cardinality of the finite set of copies. -/
theorem labelledCopyCount_def (D : HypergraphComplex s V) (C : HypergraphComplex r U) :
    D.labelledCopyCount C = #(D.copies C) :=
  (rfl)

/-- A positive labeled count is equivalent to the existence of a face-preserving injection. -/
theorem labelledCopyCount_pos_iff (D : HypergraphComplex s V) (C : HypergraphComplex r U) :
    0 < D.labelledCopyCount C ↔ ∃ f, D.IsCopy C f := by
  simp only [labelledCopyCount_def, card_pos, Finset.Nonempty, mem_copies]

/-- The labeled count is at most the number of injections of the ambient vertex types. -/
theorem labelledCopyCount_le (D : HypergraphComplex s V) (C : HypergraphComplex r U) :
    D.labelledCopyCount C ≤ (Fintype.card V).descFactorial (Fintype.card U) := by
  classical
  simpa only [labelledCopyCount_def, card_univ, Fintype.card_embedding_eq] using
    card_le_univ (D.copies C)

/-- A pattern with more ambient vertices than its host has no copies. -/
theorem labelledCopyCount_eq_zero_of_card_lt (D : HypergraphComplex s V)
    (C : HypergraphComplex r U) (h : Fintype.card V < Fintype.card U) :
    D.labelledCopyCount C = 0 :=
  Nat.eq_zero_of_le_zero ((D.labelledCopyCount_le C).trans_eq (Nat.descFactorial_of_lt h))

/-- A face larger than the target rank prevents a copy, even when its vertex injection exists. -/
theorem labelledCopyCount_eq_zero_of_rank_lt (D : HypergraphComplex s V)
    (C : HypergraphComplex r U) {k : ℕ} (hk : k ≤ r) {a : Finset U}
    (ha : a ∈ C.faces k hk) (hs : s < k) : D.labelledCopyCount C = 0 := by
  apply Nat.eq_zero_of_not_pos
  rw [labelledCopyCount_pos_iff]
  rintro ⟨f, hf⟩
  exact hs.not_ge (hf.map_face hk ha).choose

/-- Postcomposition with a copy of the host cannot decrease the labeled count. -/
theorem IsCopy.labelledCopyCount_le [Fintype W] {g : V ↪ W} (hg : E.IsCopy D g)
    (C : HypergraphComplex r U) : D.labelledCopyCount C ≤ E.labelledCopyCount C := by
  classical
  rw [labelledCopyCount_def, labelledCopyCount_def]
  apply card_le_card_of_injOn (fun f : U ↪ V ↦ f.trans g)
  · intro f hf
    exact (mem_copies _ _ _).2 (hg.comp ((mem_copies _ _ _).1 hf))
  · intro f _ f' _ h
    ext x
    exact g.injective (congrArg (fun e : U ↪ W ↦ e x) h)

end Finite

end TauCeti.HypergraphComplex
