/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Tree
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Order.Zorn

/-!
# Spanning trees of Serre graphs

For a reversal-closed set `S` of darts of a Serre graph `Γ`, the subgraph `Γ.restrict S hS` keeps
every vertex of `Γ` and the darts in `S`. Its paths are the paths of `Γ` all of whose darts lie in
`S`, and it is acyclic exactly when no nonempty reduced closed path of `Γ` stays in `S`.

A spanning tree of `Γ` is a reversal-closed set of darts whose subgraph is a tree. Every connected
Serre graph has one, and every acyclic reversal-closed set of darts extends to one, by Zorn's
lemma: a maximal acyclic set of darts reaches every vertex, since a dart leaving the vertices it
reaches could be added without creating a reduced closed path. Loops and parallel darts are
allowed throughout, and no finiteness is assumed. A rose has exactly one spanning tree, with no
darts.

Any two vertices are joined by a unique reduced path whose darts lie in a spanning tree `T`, the
tree path `T.path a b`. The tree paths from a base vertex give the free basis of the fundamental
group of a graph: a dart `e` outside `T` gives the loop `T.path v (src e) · e · T.path (tgt e) v`.

## Main definitions

* `TauCeti.SerreGraph.restrict`: the subgraph on all vertices with a reversal-closed dart set.
* `TauCeti.SerreGraph.SpanningTree`: a spanning tree of a Serre graph.
* `TauCeti.SerreGraph.SpanningTree.path`: the reduced path between two vertices in a spanning tree.

## Main results

* `TauCeti.SerreGraph.isAcyclic_restrict_iff`: acyclicity of a restriction in terms of paths of
  the ambient graph.
* `TauCeti.SerreGraph.exists_spanningTree_superset`: in a connected graph, every acyclic
  reversal-closed set of darts lies in a spanning tree.
* `TauCeti.SerreGraph.nonempty_spanningTree_iff`: a graph has a spanning tree exactly when it is
  connected.
* `TauCeti.SerreGraph.SpanningTree.eq_path`: the tree path is the only reduced path in the tree.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.3, Proposition 11.
-/

public section

namespace TauCeti.SerreGraph

variable (Γ : SerreGraph)

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The subgraph of `Γ` with all vertices of `Γ` and the darts of a reversal-closed set `S`. The
vertex type reduces to that of `Γ`, so vertices of `Γ` are vertices of the subgraph. -/
abbrev restrict : SerreGraph where
  V := Γ.V
  E := S
  src e := Γ.src e.1
  rev e := ⟨Γ.rev e.1, hS e.1 e.2⟩
  rev_rev e := Subtype.ext (Γ.rev_rev e.1)
  rev_ne e he := Γ.rev_ne e.1 (congrArg Subtype.val he)

@[simp] theorem restrict_src (e : (Γ.restrict S hS).E) :
    (Γ.restrict S hS).src e = Γ.src e.1 := (rfl)

@[simp] theorem restrict_rev_val (e : (Γ.restrict S hS).E) :
    ((Γ.restrict S hS).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem restrict_tgt (e : (Γ.restrict S hS).E) :
    (Γ.restrict S hS).tgt e = Γ.tgt e.1 := (rfl)

/-- The inclusion of a restriction into the ambient graph. -/
@[expose] def restrictInclusion : (Γ.restrict S hS).Hom Γ where
  mapV := id
  mapE := Subtype.val
  map_src _ := rfl
  map_rev _ := rfl

@[simp] theorem restrictInclusion_mapV (a : (Γ.restrict S hS).V) :
    (Γ.restrictInclusion S hS).mapV a = a := (rfl)

@[simp] theorem restrictInclusion_mapE (e : (Γ.restrict S hS).E) :
    (Γ.restrictInclusion S hS).mapE e = e.1 := (rfl)

/-- A path all of whose darts lie in `S` lifts through the inclusion of the restriction. -/
theorem exists_restrict_path {a b : Γ.V} (p : Γ.Path a b)
    (hp : ∀ e ∈ Path.darts Γ p, e ∈ S) :
    ∃ q : (Γ.restrict S hS).Path a b,
      (Γ.restrictInclusion S hS).toPrefunctor.mapPath q = p := by
  induction p with
  | nil => exact ⟨.nil, rfl⟩
  | @cons b c p e ih =>
    obtain ⟨q, hq⟩ := ih fun f hf => hp f (by simp [hf])
    refine ⟨q.cons ⟨⟨e.1, hp e.1 (by simp)⟩, e.2⟩, ?_⟩
    subst hq
    rfl

/-- The darts of a path in the restriction lie in `S`. -/
theorem mem_of_mem_darts_mapPath {a b : (Γ.restrict S hS).V}
    (q : (Γ.restrict S hS).Path a b) {e : Γ.E}
    (he : e ∈ Path.darts Γ ((Γ.restrictInclusion S hS).toPrefunctor.mapPath q)) : e ∈ S := by
  rw [Hom.darts_mapPath] at he
  obtain ⟨f, -, rfl⟩ := List.mem_map.mp he
  exact f.2

/-- A path in the restriction is reduced exactly when it is reduced in the ambient graph. -/
@[simp] theorem isReduced_restrictInclusion_mapPath_iff {a b : (Γ.restrict S hS).V}
    (q : (Γ.restrict S hS).Path a b) :
    Path.IsReduced Γ ((Γ.restrictInclusion S hS).toPrefunctor.mapPath q) ↔
      Path.IsReduced (Γ.restrict S hS) q :=
  Hom.isReduced_mapPath_iff _ (Γ.restrictInclusion S hS) Subtype.val_injective q

/-- The restriction is preconnected exactly when any two vertices are joined by a path of `Γ`
whose darts lie in `S`. -/
theorem preconnected_restrict_iff : (Γ.restrict S hS).Preconnected ↔
    ∀ a b : Γ.V, ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S := by
  rw [preconnected_iff]
  refine ⟨fun h a b => ?_, fun h a b => ?_⟩
  · obtain ⟨q⟩ := h a b
    exact ⟨_, fun e he => Γ.mem_of_mem_darts_mapPath S hS q he⟩
  · obtain ⟨p, hp⟩ := h a b
    exact ⟨(Γ.exists_restrict_path S hS p hp).choose⟩

/-- The restriction is acyclic exactly when every reduced closed path of `Γ` whose darts lie in
`S` is empty. -/
theorem isAcyclic_restrict_iff : (Γ.restrict S hS).IsAcyclic ↔
    ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → (∀ e ∈ Path.darts Γ p, e ∈ S) →
      p = Quiver.Path.nil := by
  rw [isAcyclic_iff]
  refine ⟨fun h u p hp hpS => ?_, fun h u q hq => ?_⟩
  · obtain ⟨q, rfl⟩ := Γ.exists_restrict_path S hS p hpS
    rw [h u q ((Γ.isReduced_restrictInclusion_mapPath_iff S hS q).mp hp)]
    rfl
  · have hp := h u _ ((Γ.isReduced_restrictInclusion_mapPath_iff S hS q).mpr hq)
      fun e he => Γ.mem_of_mem_darts_mapPath S hS q he
    cases q with
    | nil => rfl
    | cons q e => cases hp

/-- The restriction to the empty set of darts is acyclic. -/
theorem isAcyclic_restrict_empty : (Γ.restrict ∅ fun _ h => h.elim).IsAcyclic :=
  (Γ.isAcyclic_restrict_iff _ _).mpr fun _ p _ hp => Quiver.Path.eq_nil_of_length_zero _ (by
    rw [← Path.length_darts, List.eq_nil_iff_forall_not_mem.mpr fun e he => hp e he,
      List.length_nil])

end Restrict

/-! ### Adding a dart to an acyclic set of darts -/

/-- A set of darts carries no nonempty reduced closed path. -/
private def IsAcyclicOn (S : Set Γ.E) : Prop :=
  ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → (∀ e ∈ Path.darts Γ p, e ∈ S) →
    p = Quiver.Path.nil

variable {Γ}

/-- Paths in a set of darts that preserves a vertex set `R` start in `R` exactly when they end
in `R`. -/
private theorem mem_iff_mem_of_darts {S : Set Γ.E} {R : Set Γ.V}
    (hS : ∀ e ∈ S, Γ.rev e ∈ S) (hR : ∀ e ∈ S, Γ.src e ∈ R → Γ.tgt e ∈ R)
    {a b : Γ.V} (p : Γ.Path a b) (hp : ∀ e ∈ Path.darts Γ p, e ∈ S) : a ∈ R ↔ b ∈ R := by
  induction p with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    have he : e ∈ S := hp e (by simp)
    rw [ih fun f hf => hp f (by simp [hf])]
    exact ⟨hR e he, fun h => by simpa using hR _ (hS e he) (by simpa using h)⟩

/-- A path from `R` to its complement has a dart from `R` to its complement. -/
private theorem exists_mem_darts_of_mem_of_notMem {R : Set Γ.V} {a b : Γ.V} (p : Γ.Path a b)
    (ha : a ∈ R) (hb : b ∉ R) : ∃ e ∈ Path.darts Γ p, Γ.src e ∈ R ∧ Γ.tgt e ∉ R := by
  induction p with
  | nil => exact absurd ha hb
  | @cons b c p f ih =>
    by_cases hb' : b ∈ R
    · exact ⟨f.1, by simp, by rwa [f.2.1], by rwa [f.2.2]⟩
    · obtain ⟨e, he, h⟩ := ih hb'
      exact ⟨e, by simp [he], h⟩

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
    have hf : f.1 = e ∨ f.1 = Γ.rev e ∨ f.1 ∈ S := hpS f.1 (by simp)
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
    · rcases hf with hf | hf | hf
      rotate_right
      -- A dart of `S` extends the final segment `r`; the crossing darts are impossible.
      · refine Or.inr ⟨x, hx, q, r.cons f, rfl, hq, ?_⟩
        simp only [Path.darts_cons, List.mem_append, List.mem_singleton]
        rintro d (hd | rfl)
        exacts [hr d hd, hf]
      all_goals
        exfalso
        have hside := mem_iff_mem_of_darts hS hR r hr
        rw [← f.2.1] at hside
        -- The darts `x` and `f` both cross between `R` and its complement, in opposite
        -- directions, so `f` reverses `x`.
        have hfx : f.1 = Γ.rev x := by
          rcases hx with rfl | rfl <;> rw [hf] at hside ⊢ <;> simp_all
        have hb : b = Γ.tgt x := by rw [← f.2.1, hfx, src_rev]
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
  · have h₁ := mem_iff_mem_of_darts hS hR q hq
    have h₂ := mem_iff_mem_of_darts hS hR r hr
    rcases hx with rfl | rfl <;> simp_all

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
  obtain ⟨e, -, he, he'⟩ := exists_mem_darts_of_mem_of_notMem (R := R) p ⟨.nil, by simp⟩ hab
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

theorem isReduced_path (a b : Γ.V) : Path.IsReduced Γ (T.path a b) :=
  (T.exists_path a b).choose_spec.1

theorem mem_of_mem_darts_path {a b : Γ.V} {e : Γ.E} (he : e ∈ Path.darts Γ (T.path a b)) :
    e ∈ T.darts :=
  (T.exists_path a b).choose_spec.2 e he

/-- A reduced path whose darts lie in a spanning tree is the tree path. -/
theorem eq_path {a b : Γ.V} {p : Γ.Path a b} (hp : Path.IsReduced Γ p)
    (hpT : ∀ e ∈ Path.darts Γ p, e ∈ T.darts) : p = T.path a b :=
  T.eq_of_isReduced hp (T.isReduced_path a b) hpT fun _ => T.mem_of_mem_darts_path

@[simp] theorem path_self (a : Γ.V) : T.path a a = Quiver.Path.nil :=
  (T.eq_path (Path.isReduced_nil Γ a) (by simp)).symm

@[simp] theorem reverse_path (a b : Γ.V) : (T.path a b).reverse = T.path b a :=
  T.eq_path ((Path.isReduced_reverse Γ _).mpr (T.isReduced_path a b)) fun e he => by
    simp only [Path.darts_reverse, List.mem_map, List.mem_reverse] at he
    obtain ⟨f, hf, rfl⟩ := he
    exact T.rev_mem f (T.mem_of_mem_darts_path hf)

/-- The tree path between the endpoints of a tree dart is that dart. -/
theorem path_src_tgt {e : Γ.E} (he : e ∈ T.darts) :
    T.path (Γ.src e) (Γ.tgt e) = (Γ.dart e).toPath :=
  (T.eq_path (Path.isReduced_toPath Γ _) (by simpa using he)).symm

/-- A spanning tree contains no loop. -/
theorem src_ne_tgt {e : Γ.E} (he : e ∈ T.darts) : Γ.src e ≠ Γ.tgt e := by
  intro h
  have hlen := congrArg Quiver.Path.length (T.path_src_tgt he)
  rw [Quiver.Path.length_toPath, ← h, path_self, Quiver.Path.length_nil] at hlen
  exact zero_ne_one hlen

end SpanningTree

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

/-- A rose has exactly one spanning tree, with no darts: each petal is a reduced loop. -/
instance (α : Type*) : Unique (rose α).SpanningTree where
  default := roseTree α
  uniq T := by
    ext e
    simp only [roseTree_darts, Set.mem_empty_iff_false, iff_false]
    exact fun he => T.src_ne_tgt he rfl

end TauCeti.SerreGraph
