/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Network.Menger.Vertex

/-!
# Menger's theorem for directed paths between adjacent terminals

Let `Q` be an arrow family on a finite vertex type `V`, and let `s ≠ t` be vertices with finitely
many, say `m`, arrows from `s` to `t`. The local vertex form of Menger's theorem
(`TauCeti.exists_paths_vertexSeparator_card_eq`) assumes that there is no arrow from `s` to `t`:
otherwise no set of vertices avoiding `s` and `t` separates `t` from `s`. This file removes that
hypothesis by counting the direct arrows separately.

After deleting all `m` arrows from `s` to `t`, some set `X` of `k` vertices avoiding `s` and `t`
separates `t` from `s`, and the original arrow family has `k + m` distinct directed `s`–`t` paths
pairwise sharing no vertex other than `s` and `t`; this family contains the `m` paths consisting of
a single arrow from `s` to `t`. Conversely, every such family has at most `#X + m` members whenever
`X` separates `t` from `s` after the deletion of the arrows from `s` to `t`. Arrows from `t` to `s`
are retained and do not contribute to `m`. The separation after deletion is expressed as the mixed
separator `TauCeti.IsMixedSeparator X (TauCeti.arrowFinset Q s t) s t`.

## Main definitions

* `TauCeti.arrowFinset Q s t`: the arrows from `s` to `t`, as a finite set of the total arrow type.

## Main results

* `TauCeti.card_le_card_add_card_of_isMixedSeparator`: **weak duality**, a family of distinct
  `s`–`t` paths pairwise sharing no vertex other than `s` and `t` has at most `#X + m` members.
* `TauCeti.exists_paths_isMixedSeparator_card_eq`: **Menger's theorem for adjacent terminals**, in
  witness form.
* `TauCeti.forall_not_isMixedSeparator_iff_exists_paths`: its predicate form.

## Implementation notes

Attainment applies `TauCeti.exists_paths_vertexSeparator_card_eq` to the arrow family
`TauCeti.WithoutHom` obtained by deleting the arrows from `s` to `t`, whose walks are the walks
avoiding those arrows, and adds the `m` single-arrow paths to the resulting family.

## References

* K. Menger, *Zur allgemeinen Kurventheorie*, Fund. Math. 10 (1927).
* A. Schrijver, *Combinatorial Optimization: Polyhedra and Efficiency*, Springer, 2003,
  Section 9.1.
-/

public section

namespace TauCeti

open Finset

universe u v

variable {V : Type u} {Q : V → V → Type v} {s t : V}

/-! ### The arrows from `s` to `t` -/

section ArrowFinset

variable (Q) in
/-- The arrows from `s` to `t`, each recorded with its endpoints, as a finite set of the total
arrow type. -/
def arrowFinset (s t : V) [Fintype (Q s t)] : Finset (Σ v w, Q v w) :=
  univ.map ((Function.Embedding.sigmaMk (β := Q s) t).trans
    (Function.Embedding.sigmaMk (β := fun v ↦ Σ w, Q v w) s))

variable [Fintype (Q s t)]

@[simp]
theorem mem_arrowFinset {a : Σ v w, Q v w} : a ∈ arrowFinset Q s t ↔ a.1 = s ∧ a.2.1 = t := by
  obtain ⟨v, w, e⟩ := a
  simp only [arrowFinset, mem_map, mem_univ, true_and, Function.Embedding.trans_apply,
    Function.Embedding.sigmaMk_apply]
  constructor
  · rintro ⟨e', he'⟩
    cases he'
    exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨e, rfl⟩

@[simp]
theorem card_arrowFinset : #(arrowFinset Q s t) = Fintype.card (Q s t) := by
  simp [arrowFinset]

end ArrowFinset

/-! ### Weak duality -/

/-- **Weak duality for internally vertex-disjoint paths between possibly adjacent terminals.** Let
`X` be a set of vertices, avoiding `s` and `t`, whose deletion together with that of every arrow
from `s` to `t` leaves `t` unreachable from `s`. A family of distinct directed `s`–`t` paths whose
members pairwise share no vertex other than `s` and `t` has at most `#X + m` members, where `m` is
the number of arrows from `s` to `t`. -/
theorem card_le_card_add_card_of_isMixedSeparator [Fintype (Q s t)] {ι : Type*} [Fintype ι]
    {P : ι → ArrowWalk Q s t} (hinj : Function.Injective P) (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) {X : Finset V}
    (hX : IsMixedSeparator X (arrowFinset Q s t) s t) :
    Fintype.card ι ≤ #X + Fintype.card (Q s t) := by
  -- Every member passes through a vertex of `X` or is a single arrow from `s` to `t`.
  have h (i : ι) : ∃ x : X ⊕ Q s t, Sum.elim (fun v : X ↦ v.1 ∈ (P i).vertices)
      (fun e ↦ P i = (ArrowWalk.nil s).cons e) x := by
    rcases hX.exists_mem (P i) with ⟨v, hv, hvX⟩ | ⟨⟨v, w, e⟩, he, hD⟩
    · exact ⟨.inl ⟨v, hvX⟩, hv⟩
    · obtain ⟨rfl, rfl⟩ := mem_arrowFinset.1 hD
      exact ⟨.inr e, (hP i).eq_cons_of_mem_arrows he⟩
  choose g hg using h
  -- Different members are sent to different vertices of `X` or different arrows.
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_contra hne
    have hi := hg i
    have hj := hg j
    rw [hij] at hi
    cases hgj : g j with
    | inl v =>
      rw [hgj] at hi hj
      rcases ArrowWalk.internallyDisjoint_def.1 (hdisj hne) v.1 hi hj with h | h
      exacts [hX.source_notMem (h ▸ v.2), hX.target_notMem (h ▸ v.2)]
    | inr _ =>
      rw [hgj] at hi hj
      exact hne (hinj (hi.trans hj.symm))
  simpa using Fintype.card_le_of_injective g hg_inj

/-! ### Menger's theorem for adjacent terminals -/

section Attainment

/-- Push internally disjoint paths avoiding every arrow from `s` to `t` into the original arrow
family, and add the one-arrow path for each arrow from `s` to `t`. -/
theorem exists_paths_of_withoutHom {ι : Type*} {F : Set (Σ v w, Q v w)}
    (hF : ∀ e : Q s t, ⟨s, t, e⟩ ∈ F) (hst : s ≠ t)
    (P : ι → ArrowWalk (WithoutHom F) s t) (hP : ∀ i, (P i).IsPath)
    (hdisj : Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) :
    ∃ R : ι ⊕ Q s t → ArrowWalk Q s t, Function.Injective R ∧ (∀ i, (R i).IsPath) ∧
      (Pairwise fun i j ↦ (R i).InternallyDisjoint (R j)) ∧
      ∀ e, R (.inr e) = (ArrowWalk.nil s).cons e := by
  have hadj : IsEmpty (WithoutHom F s t) := ⟨fun e ↦ e.2 (hF e.1)⟩
  let φ := WithoutHom.incl F
  let R : ι ⊕ Q s t → ArrowWalk Q s t :=
    Sum.elim (fun i ↦ @Prefunctor.mapPath V ⟨WithoutHom F⟩ V ⟨Q⟩ φ s t (P i))
      fun e ↦ (ArrowWalk.nil s).cons e
  have hRl (i : ι) : (R (.inl i)).vertices = (P i).vertices :=
    ArrowWalk.vertices_mapPath_of_obj_eq_id φ rfl (P i)
  have hRr (e : Q s t) : R (.inr e) = (ArrowWalk.nil s).cons e := rfl
  have hint (i : ι) : ∃ v ∈ (R (.inl i)).vertices, v ≠ s ∧ v ≠ t :=
    hRl i ▸ (P i).exists_mem_vertices_ne_ne hst hadj
  have hdisj' : Pairwise fun i j ↦ (R i).InternallyDisjoint (R j) := by
    intro i j hij
    rw [ArrowWalk.internallyDisjoint_def]
    intro v hvi hvj
    rcases i with i | _
    · rcases j with j | _
      · exact ArrowWalk.internallyDisjoint_def.1 (hdisj fun h ↦ hij (congrArg _ h)) v
          (hRl i ▸ hvi) (hRl j ▸ hvj)
      · simpa [hRr] using hvj
    · simpa [hRr] using hvi
  refine ⟨R, ?_, ?_, hdisj', hRr⟩
  · have hleft : Function.Injective fun i ↦ R (.inl i) :=
      injective_of_pairwise_internallyDisjoint
        (hdisj'.comp_of_injective Sum.inl_injective) hint
    rintro (i | e) (j | e') h
    · exact congrArg Sum.inl (hleft h)
    · obtain ⟨v, hv, hvs, hvt⟩ := hint i
      rw [h, hRr] at hv
      simp [hvs, hvt] at hv
    · obtain ⟨v, hv, hvs, hvt⟩ := hint j
      rw [← h, hRr] at hv
      simp [hvs, hvt] at hv
    · rw [hRr, hRr] at h
      simpa using congrArg ArrowWalk.arrows h
  · rintro (i | e)
    · rw [ArrowWalk.isPath_def, hRl]
      exact (ArrowWalk.isPath_def _).1 (hP i)
    · rw [hRr]
      simpa [ArrowWalk.isPath_def] using hst

/-- **Menger's theorem for internally vertex-disjoint directed paths between possibly adjacent
terminals.** Let `s ≠ t` be vertices of an arrow family on a finite vertex type, with finitely many
arrows from `s` to `t`. For some `k`, there are a family of distinct directed `s`–`t` paths indexed
by `Fin k ⊕ Q s t`, pairwise sharing no vertex other than `s` and `t`, whose member indexed by an
arrow `e` from `s` to `t` is the path consisting of `e`, and a set `X` of `k` vertices, avoiding `s`
and `t`, whose deletion together with that of every arrow from `s` to `t` leaves `t` unreachable
from `s`. By `TauCeti.card_le_card_add_card_of_isMixedSeparator`, the family is then largest and
the separator smallest. -/
theorem exists_paths_isMixedSeparator_card_eq [Finite V] [Fintype (Q s t)] (hst : s ≠ t) :
    ∃ (k : ℕ) (P : Fin k ⊕ Q s t → ArrowWalk Q s t) (X : Finset V), Function.Injective P ∧
      (∀ i, (P i).IsPath) ∧ (Pairwise fun i j ↦ (P i).InternallyDisjoint (P j)) ∧
      (∀ e, P (.inr e) = (ArrowWalk.nil s).cons e) ∧
      IsMixedSeparator X (arrowFinset Q s t) s t ∧ #X = k := by
  let F : Set (Σ v w, Q v w) := arrowFinset Q s t
  have hR : IsEmpty (WithoutHom F s t) := ⟨fun e ↦ e.2 (mem_arrowFinset.2 ⟨rfl, rfl⟩)⟩
  obtain ⟨k, P, X, -, hP, hdisj, hs, ht, hX, hk⟩ :=
    exists_paths_vertexSeparator_card_eq (Q := WithoutHom F) hst hR
  obtain ⟨P', hinj, hP', hdisj', hP'r⟩ := exists_paths_of_withoutHom
    (F := F) (fun _ ↦ mem_arrowFinset.2 ⟨rfl, rfl⟩) hst P hP hdisj
  refine ⟨k, P', X, hinj, hP', hdisj', hP'r,
    isMixedSeparator_iff.2 ⟨hs, ht, fun p ↦ ?_⟩, hk⟩
  · -- A walk avoiding `X` and the arrows from `s` to `t` would survive in the deleted family.
    by_contra h
    simp only [not_or, not_exists, not_and, mem_arrowFinset] at h
    obtain ⟨p', rfl⟩ := WithoutHom.exists_mapPath_incl_eq p fun a ha haF ↦
      h.2 a ha (mem_arrowFinset.1 haF).1 (mem_arrowFinset.1 haF).2
    exact hX (reachableAvoiding_def.2
      ⟨p', fun v hv hvX ↦ h.1 v
        ((ArrowWalk.vertices_mapPath_of_obj_eq_id (WithoutHom.incl F) rfl p').symm ▸ hv) hvX⟩)

/-- **Menger's theorem for internally vertex-disjoint directed paths between possibly adjacent
terminals, predicate form.** Let `s ≠ t` be vertices of an arrow family on a finite vertex type,
with finitely many arrows from `s` to `t`. Then `t` stays reachable from `s` after deleting every
arrow from `s` to `t` and any fewer than `k` vertices other than `s` and `t` exactly when there is a
family of distinct directed `s`–`t` paths indexed by `Fin k ⊕ Q s t`, pairwise sharing no vertex
other than `s` and `t`. -/
theorem forall_not_isMixedSeparator_iff_exists_paths [Finite V] [Fintype (Q s t)] (hst : s ≠ t)
    (k : ℕ) :
    (∀ X : Finset V, #X < k → ¬IsMixedSeparator X (arrowFinset Q s t) s t) ↔
      ∃ P : Fin k ⊕ Q s t → ArrowWalk Q s t, Function.Injective P ∧ (∀ i, (P i).IsPath) ∧
        Pairwise fun i j ↦ (P i).InternallyDisjoint (P j) := by
  refine ⟨fun h ↦ ?_, fun ⟨P, hinj, hP, hdisj⟩ X hX hsep ↦ ?_⟩
  · obtain ⟨m, P, X, hinj, hP, hdisj, -, hX, rfl⟩ :=
      exists_paths_isMixedSeparator_card_eq (Q := Q) hst
    have hkm : k ≤ #X := not_lt.1 fun hlt ↦ h X hlt hX
    have hf : Function.Injective (Sum.map (Fin.castLE hkm) (id : Q s t → Q s t)) :=
      Sum.map_injective.2 ⟨Fin.castLE_injective hkm, Function.injective_id⟩
    exact ⟨P ∘ Sum.map (Fin.castLE hkm) id, hinj.comp hf, fun i ↦ hP _, hdisj.comp_of_injective hf⟩
  · have := card_le_card_add_card_of_isMixedSeparator hinj hP hdisj hsep
    simp only [Fintype.card_sum, Fintype.card_fin] at this
    omega

end Attainment

end TauCeti
