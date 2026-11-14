/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Iso
public import TauCeti.Combinatorics.Graph.Serre.Reduction

/-!
# Trees of Serre graphs

A Serre graph is acyclic when it has no nonempty reduced closed path, and a tree when it is
moreover nonempty and connected. Equivalently, an acyclic graph has at most one reduced path
between two vertices, and a tree has exactly one. These unique reduced paths are the tree paths
used to build the free basis of the fundamental group of a graph from a spanning tree.

An acyclic graph has no loop, hence no dart at all when it has at most one vertex, and a
restriction `Γ.restrict S hS` is acyclic exactly when no nonempty reduced closed path of `Γ` has
all its darts in `S`.

A morphism `f : Γ → Δ` that is locally injective, in the sense that two darts with a common source
and the same image are equal, maps reduced paths to reduced paths. So its source is acyclic when
its target is (`SerreGraph.IsAcyclic.comap`), and from a preconnected graph to an acyclic graph it
is injective on vertices and on darts (`SerreGraph.Hom.mapV_injective_of_isAcyclic`,
`SerreGraph.Hom.mapE_injective_of_isAcyclic`). Hence a morphism from a nonempty preconnected graph
to a preconnected acyclic graph that maps the darts issuing from each vertex bijectively onto those
issuing from its image is an isomorphism (`SerreGraph.Iso.ofLocallyBijective`). In the structure
of groups acting on trees, this compares a tree with the Bass–Serre tree of its quotient graph of
groups. Isomorphic graphs are acyclic together and trees together (`SerreGraph.Iso.isAcyclic_iff`,
`SerreGraph.Iso.isTree_iff`).

A graph without darts, such as the graph `noEdge V` without edges, is acyclic, and it is a tree
exactly when it has one vertex. A graph without vertices is not a tree. The segment is a tree.
A rose with a petal is not a tree, since its petal is a reduced loop.

## References

* J.-P. Serre, *Trees*, Chapter I, §2.2 and §5.4.
-/

public section

universe u v

namespace TauCeti
namespace SerreGraph

variable (Γ : SerreGraph)

/-- A Serre graph is acyclic, or a forest, when every reduced closed path is empty. -/
def IsAcyclic : Prop :=
  ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil

/-- Unfold acyclicity: every reduced closed path is empty. -/
theorem isAcyclic_iff : Γ.IsAcyclic ↔
    ∀ (u : Γ.V) (p : Γ.Path u u), Path.IsReduced Γ p → p = Quiver.Path.nil := Iff.rfl

/-- A tree is a connected acyclic Serre graph. -/
def IsTree : Prop :=
  Γ.Connected ∧ Γ.IsAcyclic

/-- Characterization of Serre trees as connected acyclic graphs. -/
theorem isTree_iff : Γ.IsTree ↔ Γ.Connected ∧ Γ.IsAcyclic := Iff.rfl

namespace IsTree

/-- Every tree is connected. -/
theorem connected (h : Γ.IsTree) : Γ.Connected := h.1

/-- Every tree is acyclic. -/
theorem isAcyclic (h : Γ.IsTree) : Γ.IsAcyclic := h.2

/-- Every reduced closed path in a tree is empty. -/
theorem eq_nil_of_isReduced (h : Γ.IsTree) {u : Γ.V} (p : Γ.Path u u)
    (hp : Path.IsReduced Γ p) : p = Quiver.Path.nil := h.2 u p hp

end IsTree

variable {Γ} in
/-- In an acyclic graph, two reduced paths with the same endpoints are equal. -/
theorem IsAcyclic.eq_of_isReduced (h : Γ.IsAcyclic) {a b : Γ.V} {p q : Γ.Path a b}
    (hp : Path.IsReduced Γ p) (hq : Path.IsReduced Γ q) : p = q := by
  have hpq : Path.reduce Γ (p.comp q.reverse) = Quiver.Path.nil :=
    h a _ (Path.isReduced_reduce Γ _)
  calc p = Path.reduce Γ (p.comp (q.reverse.comp q)) := by
        rw [← Path.reduce_comp_reduce_right, Path.reduce_reverse_comp, Quiver.Path.comp_nil,
          Path.reduce_eq_self_of_isReduced Γ p hp]
    _ = Path.reduce Γ ((Path.reduce Γ (p.comp q.reverse)).comp q) := by
        rw [Path.reduce_comp_reduce_left, Quiver.Path.comp_assoc]
    _ = q := by
        rw [hpq, Quiver.Path.nil_comp, Path.reduce_eq_self_of_isReduced Γ q hq]

variable {Γ} in
/-- An acyclic graph has no loop: a loop dart is a nonempty reduced closed path. -/
theorem IsAcyclic.src_ne_tgt (h : Γ.IsAcyclic) (e : Γ.E) : Γ.src e ≠ Γ.tgt e := by
  have key : ∀ {a b : Γ.V} (_ : Quiver.Hom a b), a ≠ b := by
    rintro a _ f rfl
    cases h a f.toPath (Path.isReduced_toPath Γ f)
  exact key (Γ.dart e)

variable {Γ} in
/-- An acyclic graph with at most one vertex has no darts. -/
theorem IsAcyclic.isEmpty_dart_of_subsingleton (h : Γ.IsAcyclic) [Subsingleton Γ.V] :
    IsEmpty Γ.E :=
  ⟨fun e => h.src_ne_tgt e (Subsingleton.elim _ _)⟩

/-- A graph is acyclic exactly when any two reduced paths with the same endpoints are equal. -/
theorem isAcyclic_iff_eq_of_isReduced : Γ.IsAcyclic ↔
    ∀ ⦃a b : Γ.V⦄ (p q : Γ.Path a b), Path.IsReduced Γ p → Path.IsReduced Γ q → p = q :=
  ⟨fun h _ _ _ _ hp hq => h.eq_of_isReduced hp hq,
    fun h u p hp => h p .nil hp (Path.isReduced_nil Γ u)⟩

variable {Γ} in
/-- In a tree, any two vertices are joined by a path. -/
theorem IsTree.nonempty_path (h : Γ.IsTree) (a b : Γ.V) : Nonempty (Γ.Path a b) :=
  Γ.preconnected_iff.mp (Γ.connected_iff.mp h.connected).2 a b

variable {Γ} in
/-- In a tree, any two vertices are joined by exactly one reduced path. -/
theorem IsTree.existsUnique_isReduced (h : Γ.IsTree) (a b : Γ.V) :
    ∃! p : Γ.Path a b, Path.IsReduced Γ p := by
  obtain ⟨p⟩ := h.nonempty_path a b
  exact ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p,
    fun q hq => h.isAcyclic.eq_of_isReduced hq (Path.isReduced_reduce Γ p)⟩

/-- A graph is a tree exactly when it is nonempty and any two vertices are joined by exactly one
reduced path. -/
theorem isTree_iff_existsUnique_isReduced : Γ.IsTree ↔
    Nonempty Γ.V ∧ ∀ a b : Γ.V, ∃! p : Γ.Path a b, Path.IsReduced Γ p := by
  refine ⟨fun h => ⟨(Γ.connected_iff.mp h.connected).1, h.existsUnique_isReduced⟩,
    fun ⟨hV, h⟩ => ?_⟩
  refine ⟨Γ.connected_iff.mpr ⟨hV, Γ.preconnected_iff.mpr fun a b => ⟨(h a b).exists.choose⟩⟩,
    ?_⟩
  exact (Γ.isAcyclic_iff_eq_of_isReduced).mpr fun a b p q hp hq => (h a b).unique hp hq

/-- A Serre graph without darts is acyclic: its only closed paths are empty. -/
theorem isAcyclic_of_isEmpty_dart [IsEmpty Γ.E] : Γ.IsAcyclic := by
  refine (isAcyclic_iff Γ).mpr fun u p _ => ?_
  cases p with
  | nil => rfl
  | cons p e => exact isEmptyElim e.1

/-- A Serre graph without darts is a tree exactly when it has exactly one vertex. -/
theorem isTree_iff_of_isEmpty_dart [IsEmpty Γ.E] :
    Γ.IsTree ↔ Nonempty Γ.V ∧ Subsingleton Γ.V := by
  rw [isTree_iff, Γ.connected_iff_of_forall_src_eq_tgt isEmptyElim,
    and_iff_left Γ.isAcyclic_of_isEmpty_dart]

/-- A Serre graph without vertices is not a tree: a tree is connected. -/
theorem not_isTree_of_isEmpty [IsEmpty Γ.V] : ¬Γ.IsTree :=
  fun h => Γ.not_connected_of_isEmpty h.connected

section Restrict

variable (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

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
  isAcyclic_of_isEmpty_dart _

end Restrict

section Morphism

variable {Γ} {Δ : SerreGraph}

/-- The source of a morphism into an acyclic graph that is injective on the darts issuing from
each vertex is acyclic. -/
theorem IsAcyclic.comap (f : Γ.Hom Δ)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
    (h : Δ.IsAcyclic) : Γ.IsAcyclic := by
  refine (isAcyclic_iff Γ).mpr fun a p hp => ?_
  have hd := congrArg (Path.darts Δ) ((isAcyclic_iff Δ).mp h _ _ (f.isReduced_mapPath hf p hp))
  rw [Hom.darts_mapPath, Path.darts_nil, List.map_eq_nil_iff] at hd
  exact Quiver.Path.eq_nil_of_length_zero p (by rw [← Path.length_darts, hd, List.length_nil])

namespace Hom

/-- A morphism from a preconnected graph to an acyclic graph that is injective on the darts
issuing from each vertex is injective on vertices. -/
theorem mapV_injective_of_isAcyclic (f : Γ.Hom Δ) (hΓ : Γ.Preconnected) (hΔ : Δ.IsAcyclic)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e') :
    Function.Injective f.mapV := by
  -- A reduced path of `Δ` whose ends coincide is empty.
  have key {x y : Δ.V} (q : Δ.Path x y) (hq : Path.IsReduced Δ q) (hxy : x = y) :
      Path.darts Δ q = [] := by
    subst hxy
    rw [(isAcyclic_iff Δ).mp hΔ _ q hq, Path.darts_nil]
  intro a b hab
  obtain ⟨p⟩ := Γ.preconnected_iff.mp hΓ a b
  -- The image of the reduced path from `a` to `b` is a reduced closed path, hence empty.
  have hd := key _ (f.isReduced_mapPath hf _ (Path.isReduced_reduce Γ p)) hab
  rw [Hom.darts_mapPath, List.map_eq_nil_iff] at hd
  exact Path.eq_of_darts_eq_nil Γ _ hd

/-- A morphism from a preconnected graph to an acyclic graph that is injective on the darts
issuing from each vertex is injective on darts. -/
theorem mapE_injective_of_isAcyclic (f : Γ.Hom Δ) (hΓ : Γ.Preconnected) (hΔ : Δ.IsAcyclic)
    (hf : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e') :
    Function.Injective f.mapE := fun e e' h =>
  hf e e' (f.mapV_injective_of_isAcyclic hΓ hΔ hf (by rw [← f.map_src, h, f.map_src])) h

end Hom

namespace Iso

/-- A morphism from a nonempty preconnected graph to a preconnected acyclic graph is an
isomorphism if it is injective on the darts issuing from each vertex and every dart issuing from a
vertex of its image is the image of a dart. This holds when it maps the darts issuing from each
vertex bijectively onto the darts issuing from its image. -/
noncomputable def ofLocallyBijective (f : Γ.Hom Δ) [Nonempty Γ.V] (hΓ : Γ.Preconnected)
    (hΔ : Δ.Preconnected) (hΔ' : Δ.IsAcyclic)
    (hinj : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
    (hsurj : ∀ d : Δ.E, Δ.src d ∈ Set.range f.mapV → d ∈ Set.range f.mapE) : Γ.Iso Δ :=
  f.toIso ⟨f.mapV_injective_of_isAcyclic hΓ hΔ' hinj, f.mapV_surjective_of_preconnected hΔ hsurj⟩
    ⟨f.mapE_injective_of_isAcyclic hΓ hΔ' hinj, f.mapE_surjective_of_preconnected hΔ hsurj⟩

section ofLocallyBijective

variable (f : Γ.Hom Δ) [Nonempty Γ.V] (hΓ : Γ.Preconnected) (hΔ : Δ.Preconnected)
  (hΔ' : Δ.IsAcyclic) (hinj : ∀ e e' : Γ.E, Γ.src e = Γ.src e' → f.mapE e = f.mapE e' → e = e')
  (hsurj : ∀ d : Δ.E, Δ.src d ∈ Set.range f.mapV → d ∈ Set.range f.mapE)

@[simp] theorem ofLocallyBijective_equivV_apply (a : Γ.V) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV a = f.mapV a :=
  Hom.toIso_equivV_apply f _ _ a

@[simp] theorem ofLocallyBijective_equivE_apply (e : Γ.E) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE e = f.mapE e :=
  Hom.toIso_equivE_apply f _ _ e

@[simp] theorem ofLocallyBijective_toHom :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).toHom = f :=
  Hom.toIso_toHom f _ _

@[simp] theorem ofLocallyBijective_equivV_symm_apply_apply (a : Γ.V) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV.symm (f.mapV a) = a := by
  simpa only [ofLocallyBijective_equivV_apply] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV.symm_apply_apply a

@[simp] theorem ofLocallyBijective_equivV_apply_symm_apply (b : Δ.V) :
    f.mapV ((ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV.symm b) = b := by
  simpa only [ofLocallyBijective_equivV_apply] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivV.apply_symm_apply b

@[simp] theorem ofLocallyBijective_equivE_symm_apply_apply (e : Γ.E) :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE.symm (f.mapE e) = e := by
  simpa only [ofLocallyBijective_equivE_apply] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE.symm_apply_apply e

@[simp] theorem ofLocallyBijective_equivE_apply_symm_apply (d : Δ.E) :
    f.mapE ((ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE.symm d) = d := by
  simpa only [ofLocallyBijective_equivE_apply] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).equivE.apply_symm_apply d

@[simp] theorem comp_ofLocallyBijective_symm_toHom :
    f.comp (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).symm.toHom = Hom.id Δ := by
  simpa only [ofLocallyBijective_toHom] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).toHom_comp_symm_toHom

@[simp] theorem ofLocallyBijective_symm_toHom_comp :
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).symm.toHom.comp f = Hom.id Γ := by
  simpa only [ofLocallyBijective_toHom] using
    (ofLocallyBijective f hΓ hΔ hΔ' hinj hsurj).symm_toHom_comp_toHom

end ofLocallyBijective

/-- Isomorphic Serre graphs are acyclic together. -/
theorem isAcyclic_iff (φ : Γ.Iso Δ) : Γ.IsAcyclic ↔ Δ.IsAcyclic :=
  ⟨.comap φ.symm.toHom fun _ _ _ h => by simpa using h,
    .comap φ.toHom fun _ _ _ h => by simpa using h⟩

/-- Isomorphic Serre graphs are trees together. -/
theorem isTree_iff (φ : Γ.Iso Δ) : Γ.IsTree ↔ Δ.IsTree :=
  (SerreGraph.isTree_iff Γ).trans <|
    (and_congr φ.connected_iff.symm φ.isAcyclic_iff).trans (SerreGraph.isTree_iff Δ).symm

end Iso

end Morphism

/-- A graph without edges is acyclic. -/
@[simp] theorem noEdge_isAcyclic {V : Type u} : (noEdge.{u, v} V).IsAcyclic :=
  isAcyclic_of_isEmpty_dart _

/-- A graph without edges is a tree exactly when it has exactly one vertex. -/
@[simp] theorem noEdge_isTree_iff {V : Type u} :
    (noEdge.{u, v} V).IsTree ↔ Nonempty V ∧ Subsingleton V :=
  isTree_iff_of_isEmpty_dart _

/-- The graph with one vertex and no edges is a tree. -/
theorem single_vertex_isTree : (noEdge.{u, v} PUnit).IsTree :=
  noEdge_isTree_iff.mpr ⟨inferInstance, inferInstance⟩

/-- The segment, two vertices joined by a single pair of darts, is a tree. -/
theorem segment_isTree : segment.IsTree := by
  refine ⟨segment.connected_iff.mpr ⟨⟨true⟩, segment.preconnected_iff.mpr fun a b => ?_⟩,
    fun u p hp => ?_⟩
  · by_cases h : a = b
    · subst h
      exact ⟨.nil⟩
    · exact ⟨(Quiver.Hom.toPath (⟨a, rfl, by
        cases a <;> cases b <;> first | rfl | exact (h rfl).elim⟩ :
        Quiver.Hom a b))⟩
  · -- A closed path of one dart would join a vertex to its negation, and a second dart can
    -- only reverse the first.
    cases p with
    | nil => rfl
    | cons p f =>
      cases p with
      | nil =>
        -- The vertices and darts of the segment are both `Bool`, with `tgt f = !f`.
        exact absurd (f.2.2.trans f.2.1.symm) (Bool.not_ne_self f.1)
      | cons p e =>
        refine absurd ?_ ((Path.isReduced_cons_cons segment p e f).mp hp).2
        exact f.2.1.trans e.2.2.symm

/-- A rose with a petal is not a tree. -/
theorem rose_not_isTree {α : Type*} (a : α) : ¬(rose α).IsTree := by
  intro h
  have hp := h.eq_nil_of_isReduced (rose α) (rosePetal a) (rosePetal_isReduced a)
  rw [rosePetal_eq_toPath] at hp
  cases hp

/-- The one-petal rose is not a tree. -/
theorem rose_one_not_tree : ¬(rose PUnit).IsTree :=
  rose_not_isTree PUnit.unit

end SerreGraph
end TauCeti
