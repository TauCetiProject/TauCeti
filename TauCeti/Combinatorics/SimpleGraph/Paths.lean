/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Cutting and closing up paths and cycles

This file collects general facts about paths and cycles in a simple graph, complementing Mathlib's
`Mathlib/Combinatorics/SimpleGraph/Paths.lean`.

## Main results

* `SimpleGraph.Walk.IsPath.start_notMem_tail_support`: a path does not return to its start.
* `SimpleGraph.Walk.IsPath.exists_support_eq_cons_append`: the support of a path between distinct
  endpoints splits as `a :: (I ++ [b])` with duplicate-free internal vertices and adjacent
  predecessor and successor sublists.
* `SimpleGraph.Walk.IsCycle.isPath_append_of_append_append`: cutting an arc of positive length
  out of a cycle leaves a path.
* `SimpleGraph.Walk.mem_support_append_of_mem_support_append_append`: the vertices of a closed
  walk outside the interior of such an arc lie on the remaining path.
* `SimpleGraph.Walk.IsPath.isCycle_append_append_reverse`: two paths from a common vertex close
  up with a third path into a cycle.
* `SimpleGraph.Walk.IsPath.isCycle_cons_append_cons_reverse`: two vertex-disjoint paths joined at
  both ends by distinct edges form a cycle.
* `SimpleGraph.Walk.exists_eq_append_of_exists_mem_support`: a walk meeting a finset splits at
  its first vertex in it.
* `SimpleGraph.Walk.exists_eq_append_append_of_countP_lt`: a walk starting in `F` with fewer
  vertices of `T \ F` than of `F` has an arc between consecutive vertices of `F` whose interior
  avoids `T`.
* `SimpleGraph.Walk.IsCycle.exists_eq_append_append`: a cycle with fewer vertices of `T` outside
  `F` than in `F` has an arc between two distinct vertices of `F` whose interior avoids `T`.
* `SimpleGraph.exists_isPath_notMem_support_iff`: every walk avoiding one vertex can be shortened
  to a path avoiding it.
-/

public section

open Finset
open scoped List

universe u

namespace SimpleGraph.Walk

variable {V : Type u} {G : SimpleGraph V}

/-- A path does not return to its start. -/
theorem IsPath.start_notMem_tail_support {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u ∉ p.support.tail := by
  have h := hp.support_nodup
  rw [← cons_tail_support] at h
  exact (List.nodup_cons.1 h).1

/-- Decompose the support of a path `R : G.Walk a b` between distinct endpoints `a ≠ b` as
`a :: (I ++ [b])`, where the internal-vertex list `I` is duplicate-free, contains neither endpoint,
and gives every vertex in `I` both an adjacent predecessor and an adjacent successor in
`R.support`. -/
theorem IsPath.exists_support_eq_cons_append {a b : V} {R : G.Walk a b} (hR : R.IsPath)
    (hab : a ≠ b) :
    ∃ I : List V, R.support = a :: (I ++ [b]) ∧ I.Nodup ∧ (∀ v ∈ I, v ≠ a ∧ v ≠ b) ∧
      (∀ v ∈ I, (∃ u, G.Adj u v ∧ [u, v] <+ R.support) ∧
        (∃ w, G.Adj v w ∧ [v, w] <+ R.support)) := by
  have hRnil : ¬R.Nil := fun h ↦ hab h.eq
  let I := R.tail.support.dropLast
  have hsupp_eq : R.support = a :: (I ++ [b]) := by
    rw [← cons_support_tail hRnil, ← R.tail.dropLast_support_concat]
  have hsupp_nd : (a :: (I ++ [b])).Nodup := hsupp_eq ▸ hR.support_nodup
  refine ⟨I, hsupp_eq, (List.nodup_cons.1 hsupp_nd).2.of_append_left, fun v hvI ↦ ?_,
    fun v hvI ↦ ?_⟩
  · refine ⟨fun h ↦ (List.nodup_cons.1 hsupp_nd).1 (List.mem_append_left _ (h ▸ hvI)), ?_⟩
    rintro rfl
    exact (List.nodup_cons.1 hsupp_nd).2.disjoint hvI (List.mem_singleton_self v)
  · obtain ⟨I₁, I₂, hI_eq⟩ := List.mem_iff_append.1 hvI
    have h₁ : a :: I₁ ≠ [] := List.cons_ne_nil _ _
    have h₂ : (a :: I₁) ++ [v] ≠ [] := by simp
    have h₃ : I₂ ++ [b] ≠ [] := by simp
    have hchain₁ : ((a :: I₁) ++ (v :: (I₂ ++ [b]))).IsChain G.Adj := by
      simpa [hsupp_eq, hI_eq, List.cons_append, List.append_assoc] using R.isChain_adj_support
    have hchain₂ : (((a :: I₁) ++ [v]) ++ (I₂ ++ [b])).IsChain G.Adj := by
      simpa [hsupp_eq, hI_eq, List.cons_append, List.append_assoc] using R.isChain_adj_support
    refine ⟨⟨(a :: I₁).getLast h₁,
      by simpa using hchain₁.rel_getLast_head_of_append h₁ (List.cons_ne_nil _ _), ?_⟩,
      ⟨(I₂ ++ [b]).head h₃, by simpa using hchain₂.rel_getLast_head_of_append h₂ h₃, ?_⟩⟩
    · rw [hsupp_eq, hI_eq]
      have hs₁ : [(a :: I₁).getLast h₁] <+ a :: I₁ :=
        List.singleton_sublist.2 (List.getLast_mem h₁)
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        hs₁.append (by simp : [v] <+ v :: (I₂ ++ [b]))
    · rw [hsupp_eq, hI_eq]
      have hs₂ : [(I₂ ++ [b]).head h₃] <+ I₂ ++ [b] := List.singleton_sublist.2 (List.head_mem h₃)
      simpa only [List.cons_append, List.nil_append, List.append_assoc] using
        (by simp : [v] <+ (a :: I₁) ++ [v]).append hs₂

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

/-- Two vertex-disjoint paths `P` from `x` to `y` and `Q` from `x'` to `y'`, joined by distinct
edges `s(x, x')` and `s(y', y)`, close up into a cycle through both edges. -/
theorem IsPath.isCycle_cons_append_cons_reverse {x x' y y' : V} {P : G.Walk x y}
    {Q : G.Walk x' y'} (hP : P.IsPath) (hQ : Q.IsPath) (hPQ : P.support.Disjoint Q.support)
    (hx : G.Adj x x') (hy : G.Adj y' y) (hxy : s(x, x') ≠ s(y', y)) :
    (cons hx (Q.append (cons hy P.reverse))).IsCycle := by
  rw [cons_isCycle_iff, isPath_append, edges_append, List.mem_append, edges_cons, List.mem_cons,
    edges_reverse, List.mem_reverse]
  refine ⟨⟨hQ, by simpa using hP, by simpa using hPQ.symm⟩, ?_⟩
  rintro (h | h | h)
  · exact hPQ P.start_mem_support (Q.fst_mem_support_of_mem_edges h)
  · exact hxy h
  · exact hPQ (P.snd_mem_support_of_mem_edges h) Q.start_mem_support

/-- A walk meeting a set `F` splits at its first vertex `b` in `F`: the first part has `b` as its
only vertex in `F`, occurring once. -/
theorem exists_eq_append_of_exists_mem_support [DecidableEq V] (F : Finset V) {v w : V}
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
theorem exists_eq_append_append_of_countP_lt [DecidableEq V] (F T : Finset V) {u w : V}
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

/-- Let `F` be a set of at least two vertices of a cycle `c` starting in `F`, with fewer vertices
of `T` outside `F` than vertices in `F`. Then `c` has an arc between two distinct vertices of `F`
whose interior avoids `T`. -/
theorem IsCycle.exists_eq_append_append [DecidableEq V] {F T : Finset V} {r : V}
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

end SimpleGraph.Walk

namespace SimpleGraph

variable {V : Type u} {G : SimpleGraph V} {s t : V}

/-- A walk avoiding a vertex can be shortened to a path avoiding that vertex. -/
theorem exists_isPath_notMem_support_iff {x : V} :
    (∃ p : G.Walk s t, p.IsPath ∧ x ∉ p.support) ↔ ∃ p : G.Walk s t, x ∉ p.support := by
  classical
  constructor
  · rintro ⟨p, -, hp⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.bypass, p.bypass_isPath, fun hx ↦ hp (p.support_bypass_subset_support hx)⟩

end SimpleGraph
