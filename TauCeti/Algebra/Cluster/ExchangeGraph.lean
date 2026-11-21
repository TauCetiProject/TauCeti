/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.Data.List.Involutive
public import TauCeti.LinearAlgebra.FreeProduct.ReducedWords

/-!
# The mutation tree and the exchange graph

A mutation word is reduced when no two adjacent directions coincide. Reduced words over `K`
are the vertices of the mutation tree: mutation in direction `k` cancels a final letter `k`
and otherwise appends `k`. Each vertex therefore has exactly one edge with each label
(`LinearAlgebra.FreeProduct.ReducedWord.neighborSetEquiv`), and the resulting graph is a tree
(`TauCeti.Mutation.mutationTree_isTree`). It is the regular tree whose edges at each vertex
are labelled by the mutation directions.

Let `μ k` be a family of involutions, such as seed mutation in direction `k` on a total class
of seeds. Words act in reading order, and every word acts as its free reduction
(`LinearAlgebra.FreeProduct.ReducedWord.eval_reduce`). Given a class map `π`, for instance the
quotient by simultaneous relabelling of the directions, the exchange graph has as vertices the
classes of
the states reachable from an initial state, two distinct classes being adjacent when they are
represented by a state and one of its mutations. Evaluating reduced words realizes the exchange
graph as the simple-graph quotient of the mutation tree
(`TauCeti.Mutation.exchangeGraph_eq_map`).

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §2, for the regular tree with labelled edges indexing a cluster pattern.
* S. Fomin and A. Zelevinsky, *Cluster algebras II: Finite type classification*, Invent. Math.
  154 (2003), §1, for exchange graphs of seeds modulo simultaneous relabelling.
-/

public section


namespace TauCeti.Mutation

open SimpleGraph LinearAlgebra.FreeProduct LinearAlgebra.FreeProduct.ReducedWord

variable {K : Type*}

section Tree

variable (K) in
/-- The mutation tree: reduced words, with `w` joined to `step k w` by an edge labelled `k`. -/
def mutationTree [DecidableEq K] : SimpleGraph (ReducedWord K) where
  Adj v w := ∃ k, step k v = w
  symm := ⟨fun v _ ⟨k, h⟩ ↦ ⟨k, h ▸ step_step k v⟩⟩
  loopless := ⟨fun v ⟨k, h⟩ ↦ step_ne k v h⟩

variable [DecidableEq K]

/-- Adjacency in the mutation tree is a step in some direction. -/
@[simp]
theorem mutationTree_adj {v w : ReducedWord K} :
    (mutationTree K).Adj v w ↔ ∃ k, step k v = w := Iff.rfl

/-- Each vertex is adjacent to its step in every direction. -/
theorem mutationTree_adj_step (k : K) (w : ReducedWord K) :
    (mutationTree K).Adj w (step k w) := ⟨k, rfl⟩

/-- Two reduced words are adjacent in the mutation tree exactly when one of them extends the
other by one letter. -/
theorem mutationTree_adj_iff {v w : ReducedWord K} :
    (mutationTree K).Adj v w ↔
      (∃ k, w.toList = v.toList ++ [k]) ∨ ∃ k, v.toList = w.toList ++ [k] := by
  refine ⟨fun ⟨k, h⟩ ↦ h ▸ (toList_step_cases k v).symm.imp (⟨k, ·⟩) (⟨k, ·⟩), ?_⟩
  rintro (⟨k, h⟩ | ⟨k, h⟩)
  · exact ⟨k, step_eq_of_toList_eq_append h⟩
  · exact Adj.symm ⟨k, step_eq_of_toList_eq_append h⟩

/-- The neighbors of a vertex correspond to the directions: each vertex has exactly one edge with
each label, joining it to its step in that direction. -/
noncomputable def _root_.LinearAlgebra.FreeProduct.ReducedWord.neighborSetEquiv
    (w : ReducedWord K) :
    K ≃ (mutationTree K).neighborSet w :=
  Equiv.ofBijective (fun k ↦ ⟨step k w, k, rfl⟩)
    ⟨fun _ _ h ↦ step_inj.1 (congrArg Subtype.val h), fun ⟨_, k, hk⟩ ↦ ⟨k, Subtype.ext hk⟩⟩

/-- The neighbor with label `k` is the step in direction `k`. -/
@[simp]
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.coe_neighborSetEquiv_apply
    (w : ReducedWord K) (k : K) :
    (neighborSetEquiv w k : ReducedWord K) = step k w := (rfl)

/-- Every reduced word is joined to the empty word in the mutation tree. -/
theorem mutationTree_reachable_nil (w : ReducedWord K) : (mutationTree K).Reachable nil w := by
  obtain ⟨w, hw⟩ := w
  induction w using List.reverseRecOn with
  | nil => rfl
  | append_singleton u k ih =>
    exact (ih hw.left_of_append).trans <| Adj.reachable <|
      ⟨k, step_eq_of_toList_eq_append rfl⟩

/-- The mutation tree is connected. -/
theorem mutationTree_connected : (mutationTree K).Connected :=
  .mk fun v w ↦ (mutationTree_reachable_nil v).symm.trans (mutationTree_reachable_nil w)

/-- The mutation tree has no cycles. -/
theorem mutationTree_isAcyclic : (mutationTree K).IsAcyclic := by
  have key : ∀ {v w : ReducedWord K} {k : K}, w.toList = v.toList ++ [k] →
      ¬((mutationTree K).deleteEdges {s(v, w)}).Reachable w v := by
    intro v w k hvw hreach
    -- Without the edge `s(v, w)`, every vertex reachable from `w` still begins with `w`.
    have hprefix : ∀ u, ((mutationTree K).deleteEdges {s(v, w)}).Reachable w u →
        w.toList <+: u.toList := by
      intro u hu
      rw [reachable_iff_reflTransGen] at hu
      induction hu with
      | refl => exact List.prefix_rfl
      | @tail a b _ hab ha =>
        rw [deleteEdges_adj, mutationTree_adj_iff, Set.mem_singleton_iff] at hab
        obtain ⟨(⟨j, hj⟩ | ⟨j, hj⟩), hne⟩ := hab
        · rw [hj]
          exact ha.trans (List.prefix_append _ _)
        · rw [hj] at ha
          rcases List.prefix_concat_iff.1 ha with h | h
          · refine absurd ?_ hne
            have hwa : w = a := ReducedWord.ext (h.trans hj.symm)
            have hvb : v = b := ReducedWord.ext <| List.append_inj_left' (hvw.symm.trans h) rfl
            rw [← hwa, ← hvb, Sym2.eq_swap]
          · exact h
    have := (hprefix v hreach).length_le
    rw [hvw, List.length_append] at this
    simp at this
  rw [isAcyclic_iff_forall_adj_isBridge]
  intro v w hvw
  rw [isBridge_iff]
  rcases mutationTree_adj_iff.1 hvw with ⟨k, h⟩ | ⟨k, h⟩
  · exact fun hr ↦ key h hr.symm
  · rw [Sym2.eq_swap]
    exact key h

/-- Reduced words with mutation steps form a tree. -/
theorem mutationTree_isTree : (mutationTree K).IsTree :=
  ⟨mutationTree_connected, mutationTree_isAcyclic⟩

end Tree

/-! ### Word evaluation and the exchange graph -/

section Pattern

variable {V X : Type*} (μ : K → V → V) (s : V) (π : V → X)

/-- The state reached from `s` along a reduced word, mutating in reading order. -/
def _root_.LinearAlgebra.FreeProduct.ReducedWord.eval (w : ReducedWord K) : V :=
  w.toList.foldl (fun t k ↦ μ k t) s

/-- A reduced word acts by the left fold of its mutations. -/
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.eval_def (w : ReducedWord K) :
    w.eval μ s = w.toList.foldl (fun t k ↦ μ k t) s := (rfl)

/-- The empty word leaves the initial state unchanged. -/
@[simp]
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.eval_nil :
    (nil : ReducedWord K).eval μ s = s := (rfl)

/-- The value of a reduced word is reachable. -/
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.foldReachable_eval (w : ReducedWord K) :
    FoldReachable (fun t k ↦ μ k t) s (w.eval μ s) :=
  foldReachable_foldl _ s w.toList

/-- The classes, under a class map `π`, of the states reachable from `s`. For the quotient by
simultaneous relabelling these are the reachable seeds modulo relabelling. -/
def reachableClasses : Set X :=
  π '' {t | FoldReachable (fun t k ↦ μ k t) s t}

/-- The exchange graph of the states reachable from `s` modulo a class map `π`: two distinct
classes are adjacent when they contain a reachable state and one of its mutations. With `π` the
quotient by simultaneous relabelling of the directions, this is the exchange graph of a cluster
pattern; with `π = id` it is the graph of the reachable states themselves. -/
def exchangeGraph : SimpleGraph (reachableClasses μ s π) :=
  SimpleGraph.fromRel fun x y ↦
    ∃ t, FoldReachable (fun t k ↦ μ k t) s t ∧ ∃ k, π t = x ∧ π (μ k t) = y

/-- The class of the state reached along a reduced word. -/
def _root_.LinearAlgebra.FreeProduct.ReducedWord.reachableClass
    (w : ReducedWord K) : reachableClasses μ s π :=
  ⟨π (w.eval μ s), w.eval μ s, w.foldReachable_eval μ s, rfl⟩

variable {μ s π}

/-- Reachable classes are the classes of reachable states. -/
@[simp]
theorem mem_reachableClasses_iff {x : X} :
    x ∈ reachableClasses μ s π ↔ ∃ t, FoldReachable (fun t k ↦ μ k t) s t ∧ π t = x :=
  Iff.rfl

/-- The class of a reduced word is the class of its value. -/
@[simp]
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.coe_reachableClass (w : ReducedWord K) :
    (w.reachableClass μ s π : X) = π (w.eval μ s) := (rfl)

/-- Two distinct reachable classes are adjacent exactly when a reachable state in either class
has a mutation in the other. -/
theorem exchangeGraph_adj_iff {x y : reachableClasses μ s π} :
    (exchangeGraph μ s π).Adj x y ↔
      x ≠ y ∧
        ((∃ t, FoldReachable (fun t k ↦ μ k t) s t ∧ ∃ k, π t = x ∧ π (μ k t) = y) ∨
          ∃ t, FoldReachable (fun t k ↦ μ k t) s t ∧ ∃ k, π t = y ∧ π (μ k t) = x) :=
  Iff.rfl

/-- For involutive mutations, two distinct classes are adjacent exactly when some reachable state
of the first class has a mutation in the second. -/
theorem exchangeGraph_adj (hμ : ∀ k, Function.Involutive (μ k))
    {x y : reachableClasses μ s π} :
    (exchangeGraph μ s π).Adj x y ↔
      x ≠ y ∧
        ∃ t, FoldReachable (fun t k ↦ μ k t) s t ∧ ∃ k, π t = x ∧ π (μ k t) = y := by
  rw [exchangeGraph_adj_iff, or_iff_left_of_imp]
  rintro ⟨t, ht, k, hx, hy⟩
  refine ⟨μ k t, ht.trans (foldReachable_apply _ t k), k, hy, ?_⟩
  rw [hμ k t, hx]

/-- If equal classes have mutations in the same classes, up to a change of direction (as for
simultaneous relabelling), then adjacency can be tested on any reachable representative. -/
theorem exchangeGraph_adj_iff_forall (hμ : ∀ k, Function.Involutive (μ k))
    (hπ : ∀ t t', π t = π t' → ∀ k, ∃ j, π (μ j t') = π (μ k t))
    {x y : reachableClasses μ s π} :
    (exchangeGraph μ s π).Adj x y ↔
      x ≠ y ∧
        ∀ t, FoldReachable (fun t k ↦ μ k t) s t → π t = x → ∃ k, π (μ k t) = y := by
  rw [exchangeGraph_adj hμ]
  refine and_congr_right fun _ ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t₀, -, k, hx, hy⟩ t - ht
    obtain ⟨j, hj⟩ := hπ t₀ t (hx.trans ht.symm) k
    exact ⟨j, hj.trans hy⟩
  · obtain ⟨t, ht, hx⟩ := mem_reachableClasses_iff.1 x.property
    obtain ⟨k, hk⟩ := h t ht hx
    exact ⟨t, ht, k, hx, hk⟩

variable [DecidableEq K]

/-- A step in the mutation tree is a single mutation of the state. -/
@[simp]
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.eval_step
    (hμ : ∀ k, Function.Involutive (μ k)) (k : K)
    (w : ReducedWord K) : (step k w).eval μ s = μ k (w.eval μ s) := by
  rcases toList_step_cases k w with h | h
  · simp only [eval_def, h, List.foldl_concat, hμ k _]
  · simp only [eval_def, h, List.foldl_concat]

/-- Every word acts as its free reduction. -/
@[simp]
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.eval_reduce
    (hμ : ∀ k, Function.Involutive (μ k)) (w : List K) :
    (reduce w).eval μ s = w.foldl (fun t k ↦ μ k t) s := by
  induction w using List.reverseRecOn with
  | nil => simp only [reduce_nil, eval_nil, List.foldl_nil]
  | append_singleton u k ih =>
    rw [reduce_append_singleton, eval_step hμ, ih, List.foldl_concat]

omit [DecidableEq K] in
/-- The states reachable from `s` are exactly the values of reduced words. -/
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.foldReachable_iff_exists_eval
    (hμ : ∀ k, Function.Involutive (μ k))
    {t : V} : FoldReachable (fun t k ↦ μ k t) s t ↔ ∃ w : ReducedWord K, w.eval μ s = t := by
  classical
  exact ⟨fun h ↦ let ⟨w, hw⟩ := foldReachable_def.1 h; ⟨reduce w, (eval_reduce hμ w).trans hw⟩,
    fun ⟨w, hw⟩ ↦ hw ▸ w.foldReachable_eval μ s⟩

omit [DecidableEq K] in
/-- Every reachable class is the class of a reduced word. -/
theorem _root_.LinearAlgebra.FreeProduct.ReducedWord.reachableClass_surjective
    (hμ : ∀ k, Function.Involutive (μ k)) :
    Function.Surjective (ReducedWord.reachableClass (K := K) μ s π) := by
  rintro ⟨x, t, ht, rfl⟩
  obtain ⟨w, rfl⟩ := (foldReachable_iff_exists_eval hμ).1 ht
  exact ⟨w, rfl⟩

/-- Word evaluation realizes the exchange graph as the simple-graph quotient of the mutation
tree: two distinct classes are adjacent exactly when they are the classes of two adjacent
reduced words. -/
theorem exchangeGraph_eq_map (hμ : ∀ k, Function.Involutive (μ k)) :
    exchangeGraph μ s π = (mutationTree K).map (ReducedWord.reachableClass μ s π) := by
  ext x y
  rw [exchangeGraph_adj hμ, map_adj']
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · rintro ⟨t, ht, k, hx, hy⟩
    obtain ⟨w, rfl⟩ := (ReducedWord.foldReachable_iff_exists_eval hμ).1 ht
    refine ⟨w, step k w, mutationTree_adj_step k w, Subtype.ext hx, Subtype.ext ?_⟩
    rw [ReducedWord.coe_reachableClass, ReducedWord.eval_step hμ, hy]
  · rintro ⟨v, w, ⟨k, rfl⟩, rfl, rfl⟩
    exact ⟨v.eval μ s, v.foldReachable_eval μ s, k, rfl, by
      rw [ReducedWord.coe_reachableClass, ReducedWord.eval_step hμ]⟩

end Pattern

/-! ### Small ranks -/

/-- In rank one the reduced words are the empty word and the one-letter word. -/
example (w : ReducedWord Unit) : w = ReducedWord.nil ∨ w = singleton () := by
  obtain ⟨_ | ⟨a, _ | ⟨b, l⟩⟩, hw⟩ := w
  · exact .inl rfl
  · cases a
    exact .inr rfl
  · exact absurd rfl (List.isChain_cons_cons.1 hw).1

/-- The double letter acts as the identity. -/
example [DecidableEq K] (k : K) : ReducedWord.reduce [k, k] = ReducedWord.nil := by
  calc
    reduce [k, k] = step k (reduce [k]) := reduce_append_singleton [k] k
    _ = nil := by rw [reduce_singleton, ← step_nil k, step_step]

end TauCeti.Mutation
