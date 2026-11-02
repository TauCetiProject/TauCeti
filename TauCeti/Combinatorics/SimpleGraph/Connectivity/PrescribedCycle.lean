/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Combinatorics.SimpleGraph.Connectivity.Fan

/-!
# Cycles through prescribed vertices

This file proves **Dirac's theorem** on cycles through prescribed vertices: for `k ≥ 2`, every
set of at most `k` vertices of a `k`-vertex-connected simple graph on a finite vertex type lies on
a common cycle. No cyclic order of the prescribed vertices is imposed.

## Main results

* `SimpleGraph.Walk.IsCycle.exists_isCycle_forall_mem_support_insert`: for `2 ≤ k`, a cycle
  through a set `T` of fewer than `k` vertices can be replaced by a cycle through `T` and any
  vertex that is `k`-vertex-reachable from every vertex of the cycle.
* `SimpleGraph.IsVertexConnected.exists_isCycle_forall_mem_support`: **Dirac's theorem**.
* `SimpleGraph.Walk.IsCycle.isPath_append_of_append_append` and
  `SimpleGraph.Walk.IsPath.isCycle_append_append_reverse`: cutting a cycle at an arc leaves a
  path, and two paths from a common vertex close up with a third path into a cycle.

## Implementation notes

Given a cycle `C` through `T` and a vertex `x` off `C`, the fan lemma
`SimpleGraph.exists_fan_of_forall_isVertexReachable` joins `x` to `min k |C|` distinct vertices
of `C` by paths meeting only at `x` and avoiding `C` otherwise. These ends cut `C` into as many
arcs, which outnumber the vertices of `T` not among the ends, so the interior of some arc between
two consecutive ends avoids `T`. Replacing that arc by the two fan paths to its ends gives the new
cycle. The arc is found by scanning the cycle, rotated to start at an end, for consecutive ends.

## References

* G. A. Dirac, *In abstrakten Graphen vorhandene vollständige 4-Graphen und ihre Unterteilungen*,
  Math. Nachr. 22 (1960), 61–85.
* J. A. Bondy and U. S. R. Murty, *Graph Theory*, Graduate Texts in Mathematics 244, Springer,
  2008, Chapter 9.
-/

public section

open Finset

universe u

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V}

/-- If `F` has `min k #U` of the elements of a nonempty set `U`, and `T ⊆ U` has fewer than `k`
elements, then fewer elements of `T` lie outside `F` than in `F`. -/
private theorem card_sdiff_lt_of_card_eq_min [DecidableEq V] {F T U : Finset V} {k : ℕ}
    (hFU : F ⊆ U) (hTU : T ⊆ U) (hU : U.Nonempty) (hF : #F = min k #U) (hT : #T < k) :
    #(T \ F) < #F := by
  by_cases hkU : k ≤ #U
  · exact (card_le_card sdiff_subset).trans_lt (by omega)
  · rw [eq_of_subset_of_card_le hFU (by omega), sdiff_eq_empty_iff_subset.2 hTU, card_empty]
    exact hU.card_pos

namespace Walk

/-- A path does not return to its start. -/
theorem IsPath.start_notMem_tail_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← cons_tail_support] at h
  exact (List.nodup_cons.1 h).1

/-- A walk meeting a set `F` splits at its first vertex `b` in `F`: the first part has `b` as its
only vertex in `F`, occurring once. -/
private theorem exists_eq_append_of_exists_mem_support [DecidableEq V] (F : Finset V) {v w : V}
    (W : G.Walk v w) (h : ∃ y ∈ W.support, y ∈ F) :
    ∃ (b : V) (B : G.Walk v b) (W₂ : G.Walk b w), W = B.append W₂ ∧ b ∈ F ∧
      (∀ y ∈ B.support, y ≠ b → y ∉ F) ∧ B.support.countP (· ∈ F) = 1 := by
  induction W with
  | nil =>
    obtain ⟨y, hy, hyF⟩ := h
    rw [support_nil, List.mem_singleton] at hy
    subst hy
    exact ⟨_, nil, nil, rfl, hyF, by simp, by simp [hyF]⟩
  | @cons v v' w hadj W ih =>
    by_cases hv : v ∈ F
    · exact ⟨v, nil, cons hadj W, rfl, hv, by simp, by simp [hv]⟩
    obtain ⟨y, hy, hyF⟩ := h
    rw [support_cons, List.mem_cons] at hy
    obtain ⟨b, B, W₂, rfl, hb, hBF, hBc⟩ :=
      ih ⟨y, hy.resolve_left (by rintro rfl; exact hv hyF), hyF⟩
    refine ⟨b, cons hadj B, W₂, rfl, hb, fun y hy hyb ↦ ?_, by simp [hv, hBc]⟩
    rw [support_cons, List.mem_cons] at hy
    obtain rfl | hy := hy
    exacts [hv, hBF y hy hyb]

/-- Let `W` be a walk starting in `F`, with fewer vertices of `T \ F` than of `F` after its start,
counted with multiplicity. Then some subwalk `A` of `W` of positive length runs between two
vertices of `F`, has its end as its only vertex in `F` after its start, and has no vertex of `T`
other than its ends. -/
private theorem exists_eq_append_append_of_countP_lt [DecidableEq V] (F T : Finset V) {u w : V}
    (W : G.Walk u w) (hu : u ∈ F)
    (hW : W.support.tail.countP (· ∈ T \ F) < W.support.tail.countP (· ∈ F)) :
    ∃ (a b : V) (W₁ : G.Walk u a) (A : G.Walk a b) (W₂ : G.Walk b w),
      W = W₁.append (A.append W₂) ∧ a ∈ F ∧ b ∈ F ∧ ¬A.Nil ∧
      A.support.tail.countP (· ∈ F) = 1 ∧ ∀ y ∈ A.support, y ≠ a → y ≠ b → y ∉ T := by
  induction hn : W.length using Nat.strongRec generalizing u with
  | ind n ih =>
  cases W with
  | nil => simp at hW
  | cons hadj W' =>
    obtain ⟨y, hy, hyF⟩ := List.countP_pos_iff.1 (hW.trans_le' (Nat.zero_le _))
    obtain ⟨b, B, W₂, rfl, hb, hBF, hBc⟩ :=
      exists_eq_append_of_exists_mem_support F W' ⟨y, by simpa using hy, by simpa using hyF⟩
    by_cases hT : ∃ y ∈ B.support, y ≠ b ∧ y ∈ T
    · -- The first arc meets `T`, so the rest of the walk still satisfies the counting hypothesis.
      obtain ⟨y, hy, hyb, hyT⟩ := hT
      have hTB : 0 < B.support.countP (· ∈ T \ F) :=
        List.countP_pos_iff.2 ⟨y, hy, by simpa [hBF y hy hyb] using hyT⟩
      simp only [support_cons, List.tail_cons, support_append, List.countP_append] at hW
      obtain ⟨a', b', W₁, A, W₂', rfl, ha', hb', hA, hAc, hAi⟩ :=
        ih W₂.length (by rw [← hn, length_cons, length_append]; omega) W₂ hb (by omega) rfl
      exact ⟨a', b', (cons hadj B).append W₁, A, W₂', by simp [append_assoc], ha', hb', hA, hAc,
        hAi⟩
    · push Not at hT
      refine ⟨u, b, nil, cons hadj B, W₂, rfl, hu, hb, not_nil_cons, by simpa using hBc,
        fun y hy hyu hyb ↦ ?_⟩
      rw [support_cons, List.mem_cons] at hy
      exact hT y (hy.resolve_left hyu) hyb

/-- Removing a subwalk of positive length from a cycle leaves a path: if `W₁`, `A`, `W₂` traverse
a cycle in turn and `A` is not trivial, then `W₂` followed by `W₁` is a path. -/
theorem IsCycle.isPath_append_of_append_append {u a b : V} {W₁ : G.Walk u a} {A : G.Walk a b}
    {W₂ : G.Walk b u} (hc : (W₁.append (A.append W₂)).IsCycle) (hA : ¬A.Nil) :
    (W₂.append W₁).IsPath := by
  have hnd := hc.support_nodup
  rw [tail_support_append, tail_support_append] at hnd
  have hbA : b ∈ A.support.tail := end_mem_tail_support hA
  rw [isPath_def, support_append, ← cons_tail_support W₂]
  simp only [List.nodup_append, List.nodup_cons, List.cons_append, List.mem_append] at hnd ⊢
  grind

/-- If `W₁`, `A`, `W₂` traverse a closed walk in turn, then every vertex of it that is not an
interior vertex of `A` lies on `W₂` followed by `W₁`. -/
theorem mem_support_append_of_mem_support_append_append {u a b v : V} {W₁ : G.Walk u a}
    {A : G.Walk a b} {W₂ : G.Walk b u} (hv : v ∈ (W₁.append (A.append W₂)).support)
    (hA : v ∈ A.support → v = a ∨ v = b) : v ∈ (W₂.append W₁).support := by
  rw [mem_support_append_iff, mem_support_append_iff] at hv
  rw [mem_support_append_iff]
  obtain hv | hv | hv := hv
  · exact .inr hv
  · obtain rfl | rfl := hA hv
    exacts [.inr W₁.end_mem_support, .inl W₂.start_mem_support]
  · exact .inl hv

/-- Two paths `P` and `Q` from `x` to distinct vertices `a` and `b`, sharing only `x`, close up
with a path `R` from `b` to `a` meeting them only at `a` and `b` into a cycle. -/
theorem IsPath.isCycle_append_append_reverse {x a b : V} {P : G.Walk x a} {Q : G.Walk x b}
    {R : G.Walk b a} (hP : P.IsPath) (hQ : Q.IsPath) (hR : R.IsPath) (hab : a ≠ b)
    (hPQ : ∀ v ∈ P.support, v ∈ Q.support → v = x)
    (hPR : ∀ v ∈ P.support, v ∈ R.support → v = a)
    (hQR : ∀ v ∈ Q.support, v ∈ R.support → v = b) :
    ((Q.append R).append P.reverse).IsCycle := by
  have hp : (Q.append R).IsPath := by
    refine (isPath_append _ _).2 ⟨hQ, hR.tail, fun v hvQ hvR ↦ ?_⟩
    exact hR.start_notMem_tail_support (hQR v hvQ (List.mem_of_mem_tail hvR) ▸ hvR)
  have hq : P.reverse.IsPath := hP.reverse
  refine hp.isCycle_append hq (fun v hvp hvq ↦ ?_) (.inl ?_)
  · have hvx : v ≠ x := fun hvx ↦ hp.start_notMem_tail_support (hvx ▸ hvp)
    have hva : v ≠ a := fun hva ↦ hq.start_notMem_tail_support (hva ▸ hvq)
    have hvP : v ∈ P.support := by simpa using List.mem_of_mem_tail hvq
    rcases (mem_support_append_iff _ _).1 (List.mem_of_mem_tail hvp) with hv | hv
    exacts [hvx (hPQ v hvP hv), hva (hPR v hvP hv)]
  · have hxR : x ∉ R.support := fun h ↦
      hab ((hPR x P.start_mem_support h).symm.trans (hQR x Q.start_mem_support h))
    have h₁ : Q.length ≠ 0 := fun h0 ↦ hxR (eq_of_length_eq_zero h0 ▸ R.start_mem_support)
    have h₂ : R.length ≠ 0 := fun h0 ↦ hab (eq_of_length_eq_zero h0).symm
    rw [length_append]
    omega

/-- Let `F` be a set of at least two vertices of a cycle `c` starting in `F`, with fewer vertices
of `T` outside `F` than vertices in `F`. Then `c` has an arc between two distinct vertices of `F`
whose interior avoids `T`. -/
private theorem IsCycle.exists_eq_append_append [DecidableEq V] {F T : Finset V} {r : V}
    {c : G.Walk r r} (hc : c.IsCycle) (hr : r ∈ F) (hF : ∀ v ∈ F, v ∈ c.support)
    (hF2 : 2 ≤ #F) (hTF : #(T \ F) < #F) :
    ∃ (a b : V) (W₁ : G.Walk r a) (A : G.Walk a b) (W₂ : G.Walk b r),
      c = W₁.append (A.append W₂) ∧ a ∈ F ∧ b ∈ F ∧ a ≠ b ∧ ¬A.Nil ∧
      ∀ y ∈ A.support, y ≠ a → y ≠ b → y ∉ T := by
  -- Counted along the tail of the support, each vertex of `c` occurs exactly once.
  have hcount (s : Finset V) : c.support.tail.countP (· ∈ s) = #(s.filter (· ∈ c.support)) := by
    rw [← hc.support_nodup.card_eq_countP]
    congr 1
    ext v
    have := c.end_mem_tail_support hc.not_nil
    have hv := List.mem_cons (a := v) (b := r) (l := c.support.tail)
    rw [cons_tail_support] at hv
    simp only [mem_filter, List.mem_toFinset]
    grind
  have hcF : c.support.tail.countP (· ∈ F) = #F := by rw [hcount, filter_true_of_mem hF]
  obtain ⟨a, b, W₁, A, W₂, rfl, ha, hb, hA, hAc, hAi⟩ :=
    exists_eq_append_append_of_countP_lt F T c hr <| by
      rw [hcF, hcount]
      exact (card_filter_le _ _).trans_lt hTF
  refine ⟨a, b, W₁, A, W₂, rfl, ha, hb, ?_, hA, hAi⟩
  -- The arc joins distinct vertices: otherwise it would be the whole cycle, meeting `F` once.
  rintro rfl
  have hnd := hc.support_nodup
  rw [tail_support_append, tail_support_append] at hnd
  have haA : a ∈ A.support.tail := end_mem_tail_support hA
  have hW₁ : W₁.Nil := by
    by_contra hW₁
    exact List.disjoint_of_nodup_append hnd (end_mem_tail_support hW₁) (List.mem_append_left _ haA)
  obtain rfl := hW₁.eq
  have hW₂ : W₂.Nil := by
    by_contra hW₂
    exact List.disjoint_of_nodup_append hnd.of_append_right haA (end_mem_tail_support hW₂)
  rw [tail_support_append, tail_support_append, List.countP_append, List.countP_append, hAc,
    nil_iff_support_eq.1 hW₁, nil_iff_support_eq.1 hW₂] at hcF
  simp only [List.tail_cons, List.countP_nil] at hcF
  omega

/-- Let `c` be a cycle in a simple graph on a finite vertex type, through a set `T` of fewer than
`k` of its vertices, where `2 ≤ k`. If a vertex `x` is `k`-vertex-reachable from every vertex of
`c`, then `x` lies on a cycle through all of `T`. -/
theorem IsCycle.exists_isCycle_forall_mem_support_insert [Finite V] [DecidableEq V] {k : ℕ}
    {r x : V} {c : G.Walk r r} (hc : c.IsCycle) (hk : 2 ≤ k)
    (h : ∀ y ∈ c.support, G.IsVertexReachable k x y) {T : Finset V}
    (hT : ∀ v ∈ T, v ∈ c.support) (hTk : #T < k) :
    ∃ (u : V) (c' : G.Walk u u), c'.IsCycle ∧ ∀ v ∈ insert x T, v ∈ c'.support := by
  simp only [mem_insert, forall_eq_or_imp]
  by_cases hx : x ∈ c.support
  · exact ⟨r, c, hc, hx, hT⟩
  -- A fan from `x` to `min k |c|` distinct vertices of `c`; its set of ends is `F`.
  set U := c.support.toFinset with hU
  have hxU : x ∉ U := by simpa [U] using hx
  have hU2 : 2 ≤ #U := one_lt_card.2 ⟨r, by simp [U], c.snd, by simp [U, c.getVert_mem_support 1],
    (c.adj_snd hc.not_nil).ne⟩
  obtain ⟨u, P, hinj, huU, hP, hint, hdisj⟩ :=
    exists_fan_of_forall_isVertexReachable hxU (min_le_right k #U) fun y hy ↦
      (h y (by simpa [U] using hy)).anti (by exact_mod_cast min_le_left k #U)
  set F := univ.image u with hF
  have hFm : #F = min k #U := by
    rw [hF, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]
  have hFU : F ⊆ U := by
    intro v hv
    obtain ⟨i, -, rfl⟩ := mem_image.1 hv
    exact huU i
  -- The ends outnumber the vertices of `T` that are not ends.
  have hTF : #(T \ F) < #F :=
    card_sdiff_lt_of_card_eq_min hFU (fun v hv ↦ by simpa [U] using hT v hv)
      (card_pos.1 (by omega)) hFm hTk
  -- Rotate `c` to start at an end, and cut it at an arc between two ends avoiding `T`.
  obtain ⟨r', hr'F, hr'⟩ : ∃ r' ∈ F, r' ∈ c.support :=
    ⟨u ⟨0, by omega⟩, mem_image_of_mem _ (mem_univ _), by simpa [U] using huU ⟨0, by omega⟩⟩
  obtain ⟨c', hc', hmem⟩ : ∃ c' : G.Walk r' r', c'.IsCycle ∧ ∀ v, v ∈ c'.support ↔ v ∈ c.support :=
    ⟨c.rotate r' hr', hc.rotate hr', fun v ↦ mem_support_rotate_iff ..⟩
  obtain ⟨a, b, W₁, A, W₂, rfl, ha, hb, hab, hA, hAi⟩ := hc'.exists_eq_append_append hr'F
    (fun v hv ↦ (hmem v).2 (by simpa [U] using hFU hv)) (hFm ▸ le_min hk hU2) hTF
  obtain ⟨i, -, rfl⟩ := mem_image.1 ha
  obtain ⟨j, -, rfl⟩ := mem_image.1 hb
  -- The rest `R` of the cycle, from `u j` back to `u i`, is a path through `T`.
  have hRc : ∀ v ∈ (W₂.append W₁).support, v ∈ U := by
    intro v hv
    rw [mem_support_append_iff] at hv
    rw [hU, List.mem_toFinset, ← hmem, mem_support_append_iff, mem_support_append_iff]
    tauto
  have hTR : ∀ v ∈ T, v ∈ (W₂.append W₁).support := fun v hv ↦
    mem_support_append_of_mem_support_append_append ((hmem v).2 (hT v hv)) fun hvA ↦ by
      by_contra! hvij
      exact hAi v hvA hvij.1 hvij.2 hv
  -- Close up the fan paths to `u j` and `u i` with `R`.
  have hcyc := (hP i).isCycle_append_append_reverse (hP j) (hc'.isPath_append_of_append_append hA)
    hab (hdisj fun hij ↦ hab (hij ▸ rfl))
    (fun v hvP hvR ↦ by_contra fun hv ↦ hint i v hvP hv (hRc v hvR))
    (fun v hvP hvR ↦ by_contra fun hv ↦ hint j v hvP hv (hRc v hvR))
  refine ⟨x, _, hcyc, start_mem_support _, fun v hv ↦ ?_⟩
  rw [mem_support_append_iff, mem_support_append_iff]
  exact .inl (.inr (hTR v hv))

end Walk

/-- **Dirac's theorem.** For `2 ≤ k`, every set of at most `k` vertices of a `k`-vertex-connected
simple graph on a finite vertex type lies on a common cycle. -/
theorem IsVertexConnected.exists_isCycle_forall_mem_support [Finite V] {k : ℕ} (hk : 2 ≤ k)
    (h : G.IsVertexConnected k) {S : Finset V} (hS : #S ≤ k) :
    ∃ (u : V) (c : G.Walk u u), c.IsCycle ∧ ∀ v ∈ S, v ∈ c.support := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    -- A `k`-vertex-connected graph has more than `k ≥ 2` vertices and is `2`-edge-connected.
    have h1 : (1 : ℕ∞) < k + 1 := by exact_mod_cast (show 1 < k + 1 by omega)
    have : Nontrivial V := (ENat.one_lt_card_iff_nontrivial V).1 (h1.trans_le h.add_one_le_card)
    obtain ⟨v, w, hvw⟩ := exists_pair_ne V
    obtain ⟨c, hc⟩ := exists_isCycle_of_two_le_isEdgeReachable hvw (by exact_mod_cast hk)
      (h.isEdgeConnected v w)
    exact ⟨v, c, hc, by simp⟩
  | insert x T hxT ih =>
    rw [card_insert_of_notMem hxT] at hS
    obtain ⟨r, c, hc, hT⟩ := ih (by omega)
    exact hc.exists_isCycle_forall_mem_support_insert hk (fun y _ ↦ h.isVertexReachable x y) hT
      (by omega)

end SimpleGraph
