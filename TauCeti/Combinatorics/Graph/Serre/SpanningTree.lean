/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import TauCeti.Combinatorics.Quiver.Prefunctor
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn

/-!
# Spanning trees of Serre graphs

A spanning tree of `Γ` is a reversal-closed set of darts whose subgraph is a tree. Every connected
Serre graph has one, and every acyclic reversal-closed set of darts extends to one, by Zorn's
lemma: a maximal acyclic set of darts reaches every vertex, since a dart leaving the vertices it
reaches could be added without creating a reduced closed path. Loops and parallel darts are
allowed throughout, and no finiteness is assumed. A tree is a spanning tree of itself, with all
of its darts, and a rose has exactly one spanning tree, with no darts.

Any two vertices are joined by a unique reduced path whose darts lie in a spanning tree `T`, the
tree path `T.path a b`. Dart weights that agree on `T` agree along tree paths, so a weight that is
trivial on `T` is trivial along them. For a group-valued weight compatible with reversal on `T`,
the weights of the tree paths from `a` to `b` and from `b` to `c` multiply to the weight of the
tree path from `a` to `c` (`weight_path_mul_weight_path`). The weights of the tree paths from `a`
to the two ends of a dart of `T` differ by the weight of that dart, as soon as the weight is
compatible with reversal at that dart (`weight_path_tgt`). The tree paths from a base vertex `v`
give a free basis of the fundamental group of a graph: choose one dart `e` from each reversal pair
outside `T`; the basis consists of the loops `T.path v (src e) · e · T.path (tgt e) v`.

## Main definitions

* `TauCeti.SerreGraph.SpanningTree`: a spanning tree of a Serre graph.
* `TauCeti.SerreGraph.SpanningTree.path`: the reduced path between two vertices in a spanning tree.
* `TauCeti.SerreGraph.IsTree.spanningTree`: a tree as a spanning tree of itself.
* `TauCeti.SerreGraph.SpanningTree.restrict`: a spanning tree contained in a subgraph, as a
  spanning tree of the subgraph.

## Main results

* `TauCeti.SerreGraph.exists_spanningTree_superset`: in a connected graph, every acyclic
  reversal-closed set of darts lies in a spanning tree.
* `TauCeti.SerreGraph.nonempty_spanningTree_iff`: a graph has a spanning tree exactly when it is
  connected.
* `TauCeti.SerreGraph.SpanningTree.eq_path`: the tree path is the only reduced path in the tree.
* `TauCeti.SerreGraph.SpanningTree.mapPath_path_of_injective`: a morphism injective on the darts
  issuing from each vertex and carrying one spanning tree into another sends tree paths to tree
  paths.
* `TauCeti.SerreGraph.SpanningTree.path_eq_cons_or_path_eq_cons_reverse`: the tree paths from a
  vertex to the two ends of a tree dart differ by that dart.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.3, Proposition 11.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

/-! ### Adding a dart to an acyclic set of darts -/

/-- A set of darts carries no nonempty reduced closed path. -/
private def IsAcyclicOn (S : Set Γ.E) : Prop :=
  ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → (∀ e ∈ Path.darts Γ p, e ∈ S) →
    p = Quiver.Path.nil

variable {Γ}

/-- Let `e` be a dart from a vertex set `R` preserved by `S` to its complement. A reduced path in
`S ∪ {e, rev e}` uses at most one of `e` and `rev e`, and at most once: between two such darts
the path would run through `S` from `tgt x` back to `tgt x`, and reducedness and acyclicity of
`S` rule this out. -/
private theorem darts_subset_or_eq_comp {S : Set Γ.E} {R : Set Γ.V}
    (hS : ∀ d ∈ S, Γ.rev d ∈ S) (hSa : IsAcyclicOn Γ S)
    (hR : ∀ d ∈ S, Γ.src d ∈ R → Γ.tgt d ∈ R) {e : Γ.E} (he : Γ.src e ∈ R)
    (he' : Γ.tgt e ∉ R) {a b : Γ.V} (p : Γ.Path a b) (hp : Path.IsReduced Γ p)
    (hpS : ∀ d ∈ Path.darts Γ p, d ∈ insert e (insert (Γ.rev e) S)) :
    (∀ d ∈ Path.darts Γ p, d ∈ S) ∨
      ∃ x, (x = e ∨ x = Γ.rev e) ∧ ∃ (q : Γ.Path a (Γ.src x)) (r : Γ.Path (Γ.tgt x) b),
        p = (q.cons (Γ.dart x)).comp r ∧ (∀ d ∈ Path.darts Γ q, d ∈ S) ∧
          ∀ d ∈ Path.darts Γ r, d ∈ S := by
  induction p with
  | nil => exact Or.inl (by simp)
  | @cons b c p f ih =>
    have hf : f.val = e ∨ f.val = Γ.rev e ∨ f.val ∈ S := hpS f.val (by simp)
    rcases ih (hp.of_cons Γ) (fun d hd => hpS d (by simp [hd])) with
      hpS' | ⟨x, hx, q, r, rfl, hq, hr⟩
    · rcases hf with hf | hf | hf
      · obtain ⟨f, rfl, rfl⟩ := f
        exact Or.inr ⟨f, Or.inl hf, p, .nil, congrArg p.cons (Subtype.ext (Γ.dart_val f).symm),
          hpS', by simp⟩
      · obtain ⟨f, rfl, rfl⟩ := f
        exact Or.inr ⟨f, Or.inr hf, p, .nil, congrArg p.cons (Subtype.ext (Γ.dart_val f).symm),
          hpS', by simp⟩
      · refine Or.inl ?_
        simp only [Path.darts_cons, List.mem_append, List.mem_singleton]
        rintro d (hd | rfl)
        exacts [hpS' d hd, hf]
    · by_cases hfS : f.val ∈ S
      · -- A dart of `S` extends the final segment `r`.
        refine Or.inr ⟨x, hx, q, r.cons f, rfl, hq, ?_⟩
        simp only [Path.darts_cons, List.mem_append, List.mem_singleton]
        rintro d (hd | rfl)
        exacts [hr d hd, hfS]
      · -- The crossing darts `e` and `rev e` cannot follow `r`.
        exfalso
        have hf : f.val = e ∨ f.val = Γ.rev e := hf.imp_right fun h => h.resolve_right hfS
        have hside := Path.mem_iff_mem_of_forall_mem_darts _ hS hR r hr
        rw [← f.property.1] at hside
        -- The darts `x` and `f` both cross between `R` and its complement, in opposite
        -- directions, so `f` reverses `x`.
        have hfx : f.val = Γ.rev x := by
          rcases hx with rfl | rfl <;> rcases hf with hf | hf
          · rw [hf] at hside
            exact absurd (hside.mpr he) he'
          · exact hf
          · rw [hf, rev_rev]
          · rw [hf, src_rev, tgt_rev] at hside
            exact absurd (hside.mp he) he'
        have hb : b = Γ.tgt x := by rw [← f.property.1, hfx, src_rev]
        subst hb
        obtain rfl := hSa _ r ((hp.of_cons Γ).of_comp_right Γ) hr
        exact ((Path.isReduced_cons_cons Γ q (Γ.dart x) f).mp hp).2 (by rw [dart_val]; exact hfx)

/-- Adding a dart pair from a vertex set `R` preserved by `S` to its complement keeps `S`
acyclic. -/
private theorem isAcyclicOn_insert {S : Set Γ.E} {R : Set Γ.V}
    (hS : ∀ d ∈ S, Γ.rev d ∈ S) (hSa : IsAcyclicOn Γ S)
    (hR : ∀ d ∈ S, Γ.src d ∈ R → Γ.tgt d ∈ R) {e : Γ.E} (he : Γ.src e ∈ R)
    (he' : Γ.tgt e ∉ R) : IsAcyclicOn Γ (insert e (insert (Γ.rev e) S)) := by
  intro u p hp hpS
  rcases darts_subset_or_eq_comp hS hSa hR he he' p hp hpS with
    hpS' | ⟨x, hx, q, r, -, hq, hr⟩
  · exact hSa u p hp hpS'
  · have h₁ := Path.mem_iff_mem_of_forall_mem_darts _ hS hR q hq
    have h₂ := Path.mem_iff_mem_of_forall_mem_darts _ hS hR r hr
    rcases hx with rfl | rfl
    · exact absurd (h₂.mpr (h₁.mpr he)) he'
    · rw [src_rev] at h₁
      rw [tgt_rev] at h₂
      exact absurd (h₁.mp (h₂.mp he)) he'

/-- A reversal-closed acyclic set of darts of a preconnected graph to which no dart can be added
joins any two vertices: otherwise a dart leaving the vertices it reaches from `a` could be added. -/
private theorem exists_path_of_maximal (h : Γ.Preconnected) {T : Set Γ.E}
    (hT : ∀ d ∈ T, Γ.rev d ∈ T) (hTa : IsAcyclicOn Γ T)
    (hmax : ∀ e, IsAcyclicOn Γ (insert e (insert (Γ.rev e) T)) → e ∈ T) (a b : Γ.V) :
    ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ T := by
  by_contra hab
  let R : Set Γ.V := {v | ∃ p : Γ.Path a v, ∀ e ∈ Path.darts Γ p, e ∈ T}
  have hR : ∀ d ∈ T, Γ.src d ∈ R → Γ.tgt d ∈ R := by
    rintro d hd ⟨p, hp⟩
    refine ⟨p.cons (Γ.dart d), ?_⟩
    simp only [Path.darts_cons, List.mem_append, List.mem_singleton, dart_val]
    rintro f (hf | rfl)
    exacts [hp f hf, hd]
  obtain ⟨p⟩ := Γ.preconnected_iff.mp h a b
  obtain ⟨e, -, he, he'⟩ := Path.exists_boundary_dart _ p R ⟨.nil, by simp⟩ hab
  exact he' (hR e (hmax e (isAcyclicOn_insert hT hTa hR he he')) he)

variable (Γ)

/-! ### Spanning trees -/

/-- A spanning tree of a Serre graph: a reversal-closed set of darts whose subgraph on all
vertices is a tree. -/
@[ext] structure SpanningTree where
  /-- The darts of the tree. -/
  darts : Set Γ.E
  /-- The reverse of a tree dart is a tree dart. -/
  rev_mem : ∀ e ∈ darts, Γ.rev e ∈ darts
  /-- The darts form a tree on all vertices. -/
  isTree : (Γ.restrict darts rev_mem).IsTree

/-- In a connected graph, every acyclic reversal-closed set of darts lies in a spanning tree. -/
theorem exists_spanningTree_superset (h : Γ.Connected) (S : Set Γ.E)
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) (hSa : (Γ.restrict S hS).IsAcyclic) :
    ∃ T : Γ.SpanningTree, S ⊆ T.darts := by
  let 𝓕 : Set (Set Γ.E) := {F | (∀ e ∈ F, Γ.rev e ∈ F) ∧ IsAcyclicOn Γ F}
  -- A path has finitely many darts, so a path in the union of a chain lies in one member.
  have hchain : ∀ c ⊆ 𝓕, IsChain (· ⊆ ·) c → c.Nonempty → ∃ ub ∈ 𝓕, ∀ s ∈ c, s ⊆ ub := by
    refine fun c hc hchain hne => ⟨⋃₀ c, ⟨fun e ⟨s, hs, he⟩ => ⟨s, hs, (hc hs).1 e he⟩,
      fun u p hp hpS => ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
    obtain ⟨s, hs, hsub⟩ := hchain.directedOn.exists_mem_subset_of_finite_of_subset_sUnion hne
      (Path.darts Γ p).finite_toSet hpS
    exact (hc hs).2 u p hp hsub
  obtain ⟨T, hST, hT⟩ :=
    zorn_subset_nonempty 𝓕 hchain S ⟨hS, (Γ.isAcyclic_restrict_iff S hS).mp hSa⟩
  have hmax : ∀ e, IsAcyclicOn Γ (insert e (insert (Γ.rev e) T)) → e ∈ T := by
    refine fun e he => hT.2 ⟨?_, he⟩ (fun d hd => Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ hd)) (Set.mem_insert e _)
    rintro d (rfl | rfl | hd)
    · exact Set.mem_insert_of_mem _ (Set.mem_insert _ _)
    · rw [rev_rev]
      exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (hT.prop.1 d hd))
  refine ⟨⟨T, hT.prop.1, (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨((connected_iff Γ).mp h).1,
    (Γ.preconnected_restrict_iff _ _).mpr ?_⟩, (Γ.isAcyclic_restrict_iff _ _).mpr hT.prop.2⟩⟩,
    hST⟩
  exact exists_path_of_maximal ((connected_iff Γ).mp h).2 hT.prop.1 hT.prop.2 hmax

/-- Every connected graph has a spanning tree. -/
theorem exists_spanningTree (h : Γ.Connected) : Nonempty Γ.SpanningTree := by
  obtain ⟨T, -⟩ := Γ.exists_spanningTree_superset h ∅ _ Γ.isAcyclic_restrict_empty
  exact ⟨T⟩

/-- A graph has a spanning tree exactly when it is connected. -/
theorem nonempty_spanningTree_iff : Nonempty Γ.SpanningTree ↔ Γ.Connected :=
  ⟨fun ⟨T⟩ => (Γ.restrictInclusion T.darts T.rev_mem).connected_of_surjective
    (fun a => ⟨a, rfl⟩) T.isTree.connected, Γ.exists_spanningTree⟩

namespace SpanningTree

variable {Γ} (T : Γ.SpanningTree)

/-- Two reduced paths with the same endpoints whose darts lie in a spanning tree are equal. -/
theorem eq_of_isReduced {a b : Γ.V} {p q : Γ.Path a b} (hp : Path.IsReduced Γ p)
    (hq : Path.IsReduced Γ q) (hpT : ∀ e ∈ Path.darts Γ p, e ∈ T.darts)
    (hqT : ∀ e ∈ Path.darts Γ q, e ∈ T.darts) : p = q := by
  obtain ⟨p, rfl⟩ := Γ.exists_restrict_path _ T.rev_mem p hpT
  obtain ⟨q, rfl⟩ := Γ.exists_restrict_path _ T.rev_mem q hqT
  rw [T.isTree.isAcyclic.eq_of_isReduced ((Γ.isReduced_restrictInclusion_mapPath_iff _ _ p).mp hp)
    ((Γ.isReduced_restrictInclusion_mapPath_iff _ _ q).mp hq)]

/-- Any two vertices are joined by a reduced path whose darts lie in a spanning tree. -/
theorem exists_path (a b : Γ.V) :
    ∃ p : Γ.Path a b, Path.IsReduced Γ p ∧ ∀ e ∈ Path.darts Γ p, e ∈ T.darts := by
  obtain ⟨q, hq, -⟩ := T.isTree.existsUnique_isReduced a b
  exact ⟨_, (Γ.isReduced_restrictInclusion_mapPath_iff _ _ q).mpr hq,
    fun e he => Γ.mem_of_mem_darts_mapPath _ _ q he⟩

/-- The tree path: the unique reduced path between two vertices whose darts lie in the spanning
tree. -/
noncomputable def path (a b : Γ.V) : Γ.Path a b := (T.exists_path a b).choose

/-- The tree path is reduced. -/
@[simp] theorem isReduced_path (a b : Γ.V) : Path.IsReduced Γ (T.path a b) :=
  (T.exists_path a b).choose_spec.1

theorem mem_of_mem_darts_path {a b : Γ.V} {e : Γ.E} (he : e ∈ Path.darts Γ (T.path a b)) :
    e ∈ T.darts :=
  (T.exists_path a b).choose_spec.2 e he

/-- A reduced path whose darts lie in a spanning tree is the tree path. -/
theorem eq_path {a b : Γ.V} {p : Γ.Path a b} (hp : Path.IsReduced Γ p)
    (hpT : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) : p = T.path a b :=
  T.eq_of_isReduced hp (T.isReduced_path a b) hpT fun _ => T.mem_of_mem_darts_path

/-- A path whose darts lie in a spanning tree reduces to the tree path between its endpoints. -/
theorem reduce_eq_path {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) : Path.reduce Γ p = T.path a b :=
  T.eq_path (Path.isReduced_reduce Γ p) fun e he =>
    hp e ((Path.darts_reduce_sublist Γ p).subset he)

/-- A path whose darts lie in a spanning tree is backtrack homotopic to the tree path between
its endpoints. -/
theorem homotopic_path {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) : Path.Homotopic Γ p (T.path a b) := by
  simpa only [T.reduce_eq_path p hp] using Path.homotopic_reduce Γ p

/-- Consecutive tree paths compose, up to backtrack homotopy, to the tree path between the
outer endpoints. -/
theorem homotopic_path_comp_path (a b c : Γ.V) :
    Path.Homotopic Γ ((T.path a b).comp (T.path b c)) (T.path a c) :=
  T.homotopic_path _ fun e he => by
    rw [Path.darts_comp, List.mem_append] at he
    exact he.elim T.mem_of_mem_darts_path T.mem_of_mem_darts_path

@[simp] theorem path_self (a : Γ.V) : T.path a a = Quiver.Path.nil :=
  (T.eq_path (Path.isReduced_nil Γ a) (by simp)).symm

@[simp] theorem reverse_path (a b : Γ.V) : (T.path a b).reverse = T.path b a :=
  T.eq_path ((Path.isReduced_reverse Γ _).mpr (T.isReduced_path a b)) fun e he => by
    simp only [Path.darts_reverse, List.mem_map, List.mem_reverse] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact T.rev_mem f (T.mem_of_mem_darts_path hf)

/-- The tree paths from a vertex `c` to the two ends of a tree dart `f` differ by that dart: the
tree path to the target of `f` is the tree path to its source followed by `f`, or the tree path
to the source of `f` is the tree path to its target followed by the reverse of `f`. -/
theorem path_eq_cons_or_path_eq_cons_reverse (c : Γ.V) {a b : Γ.V} (f : Quiver.Hom a b)
    (hf : f.val ∈ T.darts) :
    T.path c b = (T.path c a).cons f ∨ T.path c a = (T.path c b).cons (Quiver.reverse f) := by
  have hmem : ∀ e ∈ Path.darts Γ (T.path c a), e ∈ T.darts := fun _ => T.mem_of_mem_darts_path
  by_cases h : Path.IsReduced Γ ((T.path c a).cons f)
  · refine Or.inl (T.eq_path h fun e he => ?_).symm
    rw [Path.darts_cons, List.mem_append, List.mem_singleton] at he
    exact he.elim (hmem e) fun he => he ▸ hf
  -- Otherwise the tree path to `a` ends with the reverse of `f`.
  refine Or.inr ?_
  have hred := T.isReduced_path c a
  generalize T.path c a = p at h hred hmem ⊢
  cases p with
  | nil => exact absurd (Path.isReduced_toPath Γ f) h
  | @cons d _ r g =>
    have hfg : f.val = Γ.rev g.val :=
      of_not_not fun hne => h ((Path.isReduced_cons_cons Γ r g f).mpr ⟨hred, hne⟩)
    obtain rfl : b = d := f.property.2.symm.trans (by rw [hfg, tgt_rev, g.property.1])
    rw [T.eq_path (hred.of_cons Γ) fun e he => hmem e (by simp [he])]
    exact congrArg _ (Subtype.ext (by rw [reverse_val, hfg, rev_rev]))

/-- The tree path between the endpoints of a tree dart is that dart. -/
@[simp] theorem path_src_tgt {e : Γ.E} (he : e ∈ T.darts) :
    T.path (Γ.src e) (Γ.tgt e) = (Γ.dart e).toPath :=
  (T.eq_path (Path.isReduced_toPath Γ _) (by simpa using he)).symm

/-- Two darts of a spanning tree with the same source and the same target are equal. -/
theorem eq_of_src_eq_of_tgt_eq {e f : Γ.E} (he : e ∈ T.darts) (hf : f ∈ T.darts)
    (hs : Γ.src e = Γ.src f) (ht : Γ.tgt e = Γ.tgt f) : e = f := by
  have h : Path.darts Γ (T.path (Γ.src e) (Γ.tgt e)) =
      Path.darts Γ (T.path (Γ.src f) (Γ.tgt f)) := by rw [hs, ht]
  simpa [T.path_src_tgt he, T.path_src_tgt hf] using h

/-- A spanning tree contains no loop. -/
theorem src_ne_tgt {e : Γ.E} (he : e ∈ T.darts) : Γ.src e ≠ Γ.tgt e :=
  T.isTree.isAcyclic.src_ne_tgt ⟨e, he⟩

/-- A spanning tree of a graph with at most one vertex, such as a rose, has no darts. -/
instance [Subsingleton Γ.V] : IsEmpty T.darts :=
  T.isTree.isAcyclic.isEmpty_dart_of_subsingleton

section Map

variable {Δ : SerreGraph} (f : Γ.Hom Δ) (T' : Δ.SpanningTree)
  (hT : ∀ e ∈ T.darts, f.mapE e ∈ T'.darts)
include hT

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'` sends the
darts of the tree paths of `T` into `T'`. -/
theorem mem_of_mem_darts_mapPath_path {a b : Γ.V} {e : Δ.E}
    (he : e ∈ Path.darts Δ (f.toPrefunctor.mapPath (T.path a b))) : e ∈ T'.darts := by
  rw [Hom.darts_mapPath] at he
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
  exact hT d (T.mem_of_mem_darts_path hd)

/-- A morphism of Serre graphs carrying a spanning tree `T` into a spanning tree `T'` sends the
tree paths of `T` to paths backtrack homotopic to the tree paths of `T'`. -/
theorem homotopic_mapPath_path (a b : Γ.V) :
    Path.Homotopic Δ (f.toPrefunctor.mapPath (T.path a b))
      (T'.path (f.toPrefunctor.obj a) (f.toPrefunctor.obj b)) :=
  T'.homotopic_path _ fun _ => T.mem_of_mem_darts_mapPath_path f T' hT

/-- A morphism of Serre graphs injective on the darts issuing from each vertex and carrying a
spanning tree `T` into a spanning tree `T'` sends the tree paths of `T` to the tree paths of
`T'`. -/
theorem mapPath_path_of_injective
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e') (a b : Γ.V) :
    f.toPrefunctor.mapPath (T.path a b) =
      T'.path (f.toPrefunctor.obj a) (f.toPrefunctor.obj b) :=
  T'.eq_path (f.isReduced_mapPath hf _ (T.isReduced_path a b)) fun _ =>
    T.mem_of_mem_darts_mapPath_path f T' hT

end Map

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- A spanning tree whose darts lie in a subgraph is a spanning tree of that subgraph. -/
def restrict (hTS : T.darts ⊆ S) : (Γ.restrict S hS).SpanningTree where
  darts := {e | e.val ∈ T.darts}
  rev_mem e he := T.rev_mem e.val he
  isTree := by
    refine (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨((connected_iff _).mp T.isTree.connected).1,
      (preconnected_restrict_iff _ _ _).mpr fun a b => ?_⟩,
      (isAcyclic_restrict_iff _ _ _).mpr fun u p hp hpT => ?_⟩
    · obtain ⟨p, hp⟩ := Γ.exists_restrict_path S hS (T.path a b)
        fun e he => hTS (T.mem_of_mem_darts_path he)
      have hmem (e : (Γ.restrict S hS).E) (he : e ∈ Path.darts (Γ.restrict S hS) p) :
          e.val ∈ Path.darts Γ ((Γ.restrictInclusion S hS).toPrefunctor.mapPath p) := by
        rw [Hom.darts_mapPath]
        exact List.mem_map.mpr ⟨e, he, rfl⟩
      exact ⟨p, fun e he => T.mem_of_mem_darts_path (a := a) (b := b) (hp ▸ hmem e he)⟩
    · have hq := T.eq_path ((Γ.isReduced_restrictInclusion_mapPath_iff S hS p).mpr hp)
        fun e he => by
          rw [Hom.darts_mapPath] at he
          obtain ⟨d, hd, rfl⟩ := List.mem_map.mp he
          exact hpT d hd
      refine Quiver.Path.eq_nil_of_length_zero p ?_
      rw [← Prefunctor.length_mapPath (Γ.restrictInclusion S hS).toPrefunctor, hq, T.path_self,
        Quiver.Path.length_nil]

@[simp] theorem mem_restrict_darts (hTS : T.darts ⊆ S) {e : (Γ.restrict S hS).E} :
    e ∈ (T.restrict S hS hTS).darts ↔ e.val ∈ T.darts := Iff.rfl

/-- The inclusion of a subgraph containing a spanning tree sends the tree paths of the restricted
tree to the tree paths of the tree. -/
@[simp] theorem mapPath_path_restrict (hTS : T.darts ⊆ S) (a b : Γ.V) :
    (Γ.restrictInclusion S hS).toPrefunctor.mapPath ((T.restrict S hS hTS).path a b) =
      T.path a b :=
  (T.restrict S hS hTS).mapPath_path_of_injective (Γ.restrictInclusion S hS) T
    (fun _ he => (T.mem_restrict_darts S hS hTS).mp he) (fun _ _ _ h => Subtype.val_injective h)
    a b

end Restrict

/-- Two dart weights that agree on the darts of a spanning tree agree along every tree path. -/
theorem weight_path_congr {M : Type*} [Monoid M] {wt wt' : Γ.E → M}
    (hwt : ∀ e ∈ T.darts, wt e = wt' e) (a b : Γ.V) :
    (T.path a b).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) =
      (T.path a b).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt' e.val) :=
  Path.weight_congr Γ _ fun _ he => hwt _ (T.mem_of_mem_darts_path he)

/-- A dart weight that is trivial on the darts of a spanning tree is trivial along every tree
path. -/
theorem weight_path_eq_one {M : Type*} [Monoid M] {wt : Γ.E → M} (hwt : ∀ e ∈ T.darts, wt e = 1)
    (a b : Γ.V) : (T.path a b).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) = 1 :=
  Path.weight_eq_one Γ _ fun _ he => hwt _ (T.mem_of_mem_darts_path he)

/-- For a dart weight compatible with reversal on the darts of a spanning tree, the weights of the
tree paths from `a` to `b` and from `b` to `c` multiply to the weight of the tree path from `a` to
`c`. -/
theorem weight_path_mul_weight_path {G : Type*} [Group G] {wt : Γ.E → G}
    (hwt : ∀ e ∈ T.darts, wt (Γ.rev e) = (wt e)⁻¹) (a b c : Γ.V) :
    (T.path a b).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) *
        (T.path b c).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) =
      (T.path a c).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) := by
  classical
  -- Extended by `1` off the tree, the weight is compatible with reversal on every dart.
  have hrev (e : Γ.E) : (if Γ.rev e ∈ T.darts then wt (Γ.rev e) else 1) =
      (if e ∈ T.darts then wt e else 1)⁻¹ := by
    by_cases he : e ∈ T.darts
    · simp [he, T.rev_mem e he, hwt e he]
    · have hr : Γ.rev e ∉ T.darts := fun h => he (Γ.rev_rev e ▸ T.rev_mem _ h)
      simp [he, hr]
  have h (e : Γ.E) (he : e ∈ T.darts) : wt e = if e ∈ T.darts then wt e else 1 := by simp [he]
  rw [T.weight_path_congr h, T.weight_path_congr h, T.weight_path_congr h,
    ← Quiver.Path.weight_comp]
  exact Path.Homotopic.weight_eq Γ (fun e => if e ∈ T.darts then wt e else 1) hrev
    (T.homotopic_path_comp_path a b c)

/-- For a dart weight compatible with reversal at a tree dart `e`, the weight of the tree path
from `a` to the target of `e` is the weight of the tree path from `a` to its source times the
weight of `e`. -/
theorem weight_path_tgt {G : Type*} [Group G] {wt : Γ.E → G} (a : Γ.V) {e : Γ.E}
    (he : e ∈ T.darts) (hwt : wt (Γ.rev e) = (wt e)⁻¹) :
    (T.path a (Γ.tgt e)).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) =
      (T.path a (Γ.src e)).weight (fun {a b : Γ.V} (e : a ⟶ b) => wt e.val) * wt e := by
  rcases T.path_eq_cons_or_path_eq_cons_reverse a (Γ.dart e) (by simpa using he) with h | h
  · simp [h]
  · simp [h, hwt]

end SpanningTree

variable {Γ} in
/-- A tree is a spanning tree of itself: all of its darts form a spanning tree. -/
def IsTree.spanningTree (h : Γ.IsTree) : Γ.SpanningTree where
  darts := Set.univ
  rev_mem _ _ := Set.mem_univ _
  isTree := by
    have hΓ := Γ.connected_iff.mp (IsTree.connected _ h)
    refine (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨hΓ.1, (preconnected_iff _).mpr fun a b => ?_⟩,
      (Γ.isAcyclic_restrict_iff _ _).mpr fun _ p hp _ => h.eq_nil_of_isReduced _ p hp⟩
    -- Every path of the tree lies in the subgraph of all darts.
    obtain ⟨p⟩ := Γ.preconnected_iff.mp hΓ.2 a b
    obtain ⟨q, -⟩ := Γ.exists_restrict_path Set.univ (fun _ _ => Set.mem_univ _) p
      fun _ _ => Set.mem_univ _
    exact ⟨q⟩

variable {Γ} in
@[simp] theorem IsTree.spanningTree_darts (h : Γ.IsTree) : h.spanningTree.darts = Set.univ :=
  (rfl)

/-- The spanning tree of a rose, with no darts. -/
def roseTree (α : Type*) : (rose α).SpanningTree where
  darts := ∅
  rev_mem _ h := h.elim
  isTree := (isTree_iff _).mpr ⟨(connected_iff _).mpr ⟨⟨PUnit.unit⟩,
    (preconnected_iff _).mpr fun a b => by
      cases a
      cases b
      exact ⟨.nil⟩⟩, (rose α).isAcyclic_restrict_empty⟩

@[simp] theorem roseTree_darts (α : Type*) : (roseTree α).darts = ∅ := (rfl)

/-- Every spanning tree of the segment contains both of its darts: the tree path between the two
vertices crosses the edge. -/
@[simp] theorem segment_spanningTree_darts (T : segment.SpanningTree) : T.darts = Set.univ := by
  obtain ⟨e, he⟩ : ∃ e, e ∈ Path.darts _ (T.path false true) := by
    generalize T.path false true = q
    cases q with
    | cons q e => exact ⟨e.val, (Path.darts_cons _ q e).symm ▸
        List.mem_append_right _ (List.mem_singleton_self _)⟩
  refine Set.eq_univ_of_forall fun b => ?_
  rcases Bool.eq_or_eq_not b e with rfl | rfl
  · exact T.mem_of_mem_darts_path he
  · exact T.rev_mem _ (T.mem_of_mem_darts_path he)

/-- A rose has exactly one spanning tree, the one with no darts. -/
instance (α : Type*) : Unique (rose α).SpanningTree where
  default := roseTree α
  uniq T := SpanningTree.ext ((Set.eq_empty_of_isEmpty T.darts).trans (roseTree_darts α).symm)

end TauCeti.SerreGraph
