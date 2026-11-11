/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Serre.Aut

/-!
# Collapsing a set of edges of a Serre graph

For a reversal-closed set `S` of darts of a Serre graph `Γ`, the collapse `Γ.collapse S hS` is the
graph obtained by contracting every edge of `S` to a point. Its vertices are the classes of
vertices of `Γ` joined by a path of darts in `S`, that is the connected components of the
subgraph spanned by `S`, and its darts are the darts of `Γ` outside `S`. The collapse map
`Γ.collapseVertex S hS` sends a vertex to its class.

The collapse of a connected graph is connected, and the collapse of a forest is a forest: a
reduced path of the collapse lifts to a reduced path of `Γ`, by inserting between consecutive
darts a reduced path of darts in `S`. Hence the collapse of a tree is a tree. In a forest the
fibres of the collapse map are convex, so in a tree they are subtrees, and an automorphism
preserving `S` induces an automorphism of the collapse.

The collapse map is injective exactly when every dart of `S` is a loop; in particular collapsing
no dart changes nothing. Collapsing every dart of a connected graph leaves a single vertex and
no dart.

## Main declarations

* `TauCeti.SerreGraph.collapse`, `TauCeti.SerreGraph.collapseVertex`: the collapse and the
  collapse map on vertices, with `TauCeti.SerreGraph.collapseVertex_eq_iff`.
* `TauCeti.SerreGraph.IsAcyclic.collapse`, `TauCeti.SerreGraph.IsTree.collapse`: collapses of
  forests and trees.
* `TauCeti.SerreGraph.IsAcyclic.isConvex_collapseVertex_preimage`: the fibres of the collapse
  map of a forest are convex.
* `TauCeti.SerreGraph.Aut.collapse`: the automorphism of the collapse induced by an automorphism
  preserving the collapsed darts.

## References

* V. Guirardel and G. Levitt, *JSJ decompositions of groups*, Astérisque 395 (2017), §1.4.1
  (collapse maps) and the proof of Lemma 2.11 (the fibres of a collapse map are subtrees).
-/

public section

universe u v

namespace TauCeti

namespace SerreGraph

variable (Γ : SerreGraph.{u, v}) (S : Set Γ.E) (hS : ∀ e ∈ S, Γ.rev e ∈ S)

/-- The equivalence relation on vertices of being joined by a path of darts in a reversal-closed
set `S`. Its classes are the connected components of the subgraph spanned by `S`. -/
def collapseSetoid : Setoid Γ.V where
  r a b := ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S
  iseqv :=
    { refl a := ⟨.nil, by simp⟩
      symm := by
        rintro a b ⟨p, hp⟩
        refine ⟨p.reverse, fun e he => ?_⟩
        obtain ⟨f, hf, rfl⟩ := List.mem_map.mp (Path.darts_reverse Γ p ▸ he)
        exact hS f (hp f (List.mem_reverse.mp hf))
      trans := by
        rintro a b c ⟨p, hp⟩ ⟨q, hq⟩
        refine ⟨p.comp q, fun e he => ?_⟩
        rw [Path.darts_comp, List.mem_append] at he
        exact he.elim (hp e) (hq e) }

variable {Γ S} in
/-- Two vertices are related exactly when they are joined by a path of darts in `S`. -/
theorem collapseSetoid_iff {a b : Γ.V} :
    Γ.collapseSetoid S hS a b ↔ ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S := Iff.rfl

/-- The collapse of a Serre graph along a reversal-closed set `S` of darts: every edge of `S` is
contracted to a point. The vertices are the classes of vertices joined by a path of darts in `S`
and the darts are the darts outside `S`. -/
@[expose] def collapse : SerreGraph.{u, v} where
  V := Quotient (Γ.collapseSetoid S hS)
  E := {e : Γ.E // e ∉ S}
  src e := Quotient.mk _ (Γ.src e.1)
  rev e := ⟨Γ.rev e.1, fun h => e.2 (Γ.rev_rev e.1 ▸ hS _ h)⟩
  rev_rev e := Subtype.ext (Γ.rev_rev e.1)
  rev_ne e he := Γ.rev_ne e.1 (congrArg Subtype.val he)

/-- The collapse map on vertices: a vertex is sent to its class in the collapse. -/
def collapseVertex (a : Γ.V) : (Γ.collapse S hS).V := Quotient.mk _ a

theorem collapseVertex_surjective : Function.Surjective (Γ.collapseVertex S hS) :=
  Quotient.mk_surjective

variable {Γ S} in
/-- Two vertices have the same image in the collapse exactly when they are joined by a path of
collapsed darts. -/
theorem collapseVertex_eq_iff {a b : Γ.V} :
    Γ.collapseVertex S hS a = Γ.collapseVertex S hS b ↔
      ∃ p : Γ.Path a b, ∀ e ∈ Path.darts Γ p, e ∈ S :=
  Quotient.eq.trans (collapseSetoid_iff hS)

@[simp] theorem collapse_src (e : (Γ.collapse S hS).E) :
    (Γ.collapse S hS).src e = Γ.collapseVertex S hS (Γ.src e.1) := (rfl)

@[simp] theorem collapse_rev_val (e : (Γ.collapse S hS).E) :
    ((Γ.collapse S hS).rev e).1 = Γ.rev e.1 := (rfl)

@[simp] theorem collapse_tgt (e : (Γ.collapse S hS).E) :
    (Γ.collapse S hS).tgt e = Γ.collapseVertex S hS (Γ.tgt e.1) := (rfl)

variable {Γ S} in
/-- The endpoints of a collapsed dart have the same image in the collapse. -/
theorem collapseVertex_src_eq_tgt {e : Γ.E} (he : e ∈ S) :
    Γ.collapseVertex S hS (Γ.src e) = Γ.collapseVertex S hS (Γ.tgt e) :=
  (collapseVertex_eq_iff hS).mpr ⟨(Γ.dart e).toPath, by simpa using he⟩

variable {Γ S} in
/-- Two vertices with the same image in the collapse are joined by a reduced path of collapsed
darts. -/
theorem exists_isReduced_path_of_collapseVertex_eq {a b : Γ.V}
    (h : Γ.collapseVertex S hS a = Γ.collapseVertex S hS b) :
    ∃ p : Γ.Path a b, Path.IsReduced Γ p ∧ ∀ e ∈ Path.darts Γ p, e ∈ S := by
  obtain ⟨p, hp⟩ := (collapseVertex_eq_iff hS).mp h
  exact ⟨Path.reduce Γ p, Path.isReduced_reduce Γ p,
    fun e he => hp e ((Path.darts_reduce_sublist Γ p).subset he)⟩

/-! ### Connectedness -/

variable {Γ} in
/-- The collapse map carries paths to paths: vertices joined by a path have images joined by a
path of the collapse. -/
theorem nonempty_collapse_path {a b : Γ.V} (p : Γ.Path a b) :
    Nonempty ((Γ.collapse S hS).Path (Γ.collapseVertex S hS a) (Γ.collapseVertex S hS b)) := by
  induction p with
  | nil => exact ⟨.nil⟩
  | @cons b c p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    by_cases he : e ∈ S
    · rwa [← collapseVertex_src_eq_tgt hS he]
    · exact ⟨ih.some.cons ⟨⟨e, he⟩, rfl, rfl⟩⟩

variable {Γ} in
/-- The collapse of a preconnected graph is preconnected. -/
theorem Preconnected.collapse (h : Γ.Preconnected) : (Γ.collapse S hS).Preconnected := by
  refine (preconnected_iff _).mpr fun x y => ?_
  obtain ⟨a, rfl⟩ := Γ.collapseVertex_surjective S hS x
  obtain ⟨b, rfl⟩ := Γ.collapseVertex_surjective S hS y
  exact nonempty_collapse_path S hS ((Γ.preconnected_iff.mp h a b).some)

variable {Γ} in
/-- The collapse of a connected graph is connected. -/
theorem Connected.collapse (h : Γ.Connected) : (Γ.collapse S hS).Connected :=
  (connected_iff _).mpr ⟨(Γ.connected_iff.mp h).1.map (Γ.collapseVertex S hS),
    (Γ.connected_iff.mp h).2.collapse S hS⟩

/-! ### Collapses of forests and trees -/

variable {Γ S} in
include hS in
/-- A collapsed dart does not reverse a dart that is not collapsed. -/
private theorem ne_rev_of_mem_of_notMem {e f : Γ.E} (he : e ∉ S) (hf : f ∈ S) : f ≠ Γ.rev e :=
  fun h => he (Γ.rev_rev e ▸ hS _ (h ▸ hf))

/-- A reduced path of the collapse lifts to a reduced path of the graph from any vertex over its
start, ending with the last dart of the given path. -/
private theorem exists_isReduced_path_of_collapse {x y : (Γ.collapse S hS).V}
    (P : (Γ.collapse S hS).Path x y) (hP : Path.IsReduced _ P) (a : Γ.V)
    (ha : Γ.collapseVertex S hS a = x) :
    ∃ (b : Γ.V) (p : Γ.Path a b), Γ.collapseVertex S hS b = y ∧ Path.IsReduced Γ p ∧
      (Path.darts Γ p).getLast? = (Path.darts _ P).getLast?.map fun f => f.1 := by
  induction P with
  | nil => exact ⟨a, .nil, ha, Path.isReduced_nil Γ a, by simp⟩
  | @cons y' y P e ih =>
    obtain ⟨b', p', hb', hp', hlast⟩ := ih (hP.of_cons _)
    obtain ⟨e, rfl, rfl⟩ := e
    -- Join the end of the lift to the source of the new dart by a reduced path of collapsed darts.
    obtain ⟨q, hq, hqS⟩ := exists_isReduced_path_of_collapseVertex_eq hS hb'
    refine ⟨Γ.tgt e.1, (p'.comp q).cons (Γ.dart e.1), rfl, ?_, by simp⟩
    rw [Path.isReduced_iff_isChain] at hP hp' hq ⊢
    rw [Path.darts_cons, List.isChain_append] at hP
    rw [Path.darts_cons, Path.darts_comp, dart_val, List.isChain_append, List.isChain_append]
    refine ⟨⟨hp', hq, fun x hx y hy => ?_⟩, List.isChain_singleton _, fun x hx y hy => ?_⟩
    · obtain ⟨f, -, rfl⟩ := Option.mem_map.mp (hlast ▸ hx)
      exact ne_rev_of_mem_of_notMem hS f.2 (hqS y (List.mem_of_mem_head? hy))
    · obtain rfl : e.1 = y := by simpa using hy
      rw [List.getLast?_append] at hx
      rcases Option.or_eq_some_iff.mp hx with hx | ⟨-, hx⟩
      · exact fun h => e.2 (h ▸ hS x (hqS x (List.mem_of_mem_getLast? hx)))
      · obtain ⟨f, hf, rfl⟩ := Option.map_eq_some_iff.mp (hlast ▸ hx)
        exact fun h => hP.2.2 f hf e rfl (Subtype.ext h)

variable {Γ} in
/-- The collapse of a forest is a forest. -/
theorem IsAcyclic.collapse (h : Γ.IsAcyclic) : (Γ.collapse S hS).IsAcyclic := by
  refine (isAcyclic_iff _).mpr fun x P hP => ?_
  obtain ⟨a, rfl⟩ := Γ.collapseVertex_surjective S hS x
  obtain ⟨b, p, hb, hp, hlast⟩ := Γ.exists_isReduced_path_of_collapse S hS P hP a rfl
  obtain ⟨q, hq, hqS⟩ := exists_isReduced_path_of_collapseVertex_eq hS hb
  -- Closing the lift by a reduced path of collapsed darts gives a reduced closed path.
  have hpq : Path.IsReduced Γ (p.comp q) := by
    refine (Path.isReduced_comp_iff Γ p q).mpr ⟨hp, hq, fun e he f hf => ?_⟩
    obtain ⟨g, -, rfl⟩ := Option.mem_map.mp (hlast ▸ he)
    exact ne_rev_of_mem_of_notMem hS g.2 (hqS f (List.mem_of_mem_head? hf))
  have hnil := congrArg (Path.darts Γ) ((isAcyclic_iff Γ).mp h a _ hpq)
  rw [Path.darts_comp, Path.darts_nil, List.append_eq_nil_iff] at hnil
  rw [hnil.1, List.getLast?_nil, eq_comm, Option.map_eq_none_iff,
    List.getLast?_eq_none_iff] at hlast
  exact Quiver.Path.eq_nil_of_length_zero _ (by rw [← Path.length_darts, hlast, List.length_nil])

variable {Γ} in
/-- The collapse of a tree is a tree. -/
theorem IsTree.collapse (h : Γ.IsTree) : (Γ.collapse S hS).IsTree :=
  (isTree_iff _).mpr ⟨h.connected.collapse S hS, h.isAcyclic.collapse S hS⟩

variable {Γ S} in
/-- In a forest, the reduced path between two vertices with the same image in the collapse
consists of collapsed darts. -/
theorem IsAcyclic.mem_of_collapseVertex_eq (h : Γ.IsAcyclic) {a b : Γ.V}
    (hab : Γ.collapseVertex S hS a = Γ.collapseVertex S hS b) {p : Γ.Path a b}
    (hp : Path.IsReduced Γ p) {e : Γ.E} (he : e ∈ Path.darts Γ p) : e ∈ S := by
  obtain ⟨q, hq, hqS⟩ := exists_isReduced_path_of_collapseVertex_eq hS hab
  exact hqS e (h.eq_of_isReduced hp hq ▸ he)

variable {Γ} in
/-- In a forest, the vertices over a vertex of the collapse form a convex set: the fibres of the
collapse map of a tree are subtrees. -/
theorem IsAcyclic.isConvex_collapseVertex_preimage (h : Γ.IsAcyclic) (x : (Γ.collapse S hS).V) :
    Γ.IsConvex (Γ.collapseVertex S hS ⁻¹' {x}) := by
  refine isConvex_iff.mpr fun a ha b hb p hp e he => ?_
  obtain rfl : Γ.collapseVertex S hS a = x := ha
  obtain ⟨q, r, rfl⟩ := Path.exists_eq_cons_comp_of_mem_darts Γ p he
  refine ((collapseVertex_eq_iff hS).mpr ⟨q, fun f hf => ?_⟩).symm
  exact h.mem_of_collapseVertex_eq hS hb.symm hp (by simp [hf])

/-! ### The extreme collapses -/

/-- The collapse map is injective exactly when every collapsed dart is a loop. -/
theorem collapseVertex_injective_iff :
    Function.Injective (Γ.collapseVertex S hS) ↔ ∀ e ∈ S, Γ.src e = Γ.tgt e := by
  refine ⟨fun h e he => h (collapseVertex_src_eq_tgt hS he), fun h a b hab => ?_⟩
  obtain ⟨p, hp⟩ := (collapseVertex_eq_iff hS).mp hab
  exact ((Path.mem_iff_mem_of_forall_mem_darts Γ (R := {a}) hS
    (fun e he hea => (h e he).symm.trans hea) p hp).mp rfl).symm

/-- Collapsing no dart identifies no vertices. -/
theorem collapseVertex_empty_injective (hS : ∀ e ∈ (∅ : Set Γ.E), Γ.rev e ∈ (∅ : Set Γ.E)) :
    Function.Injective (Γ.collapseVertex ∅ hS) :=
  (Γ.collapseVertex_injective_iff ∅ hS).mpr fun _ he => he.elim

/-- Collapsing every dart leaves no dart. -/
instance isEmpty_collapse_univ_E (hS : ∀ e ∈ (Set.univ : Set Γ.E), Γ.rev e ∈ (Set.univ : Set Γ.E)) :
    IsEmpty (Γ.collapse Set.univ hS).E :=
  ⟨fun e => e.2 (Set.mem_univ _)⟩

variable {Γ} in
/-- Collapsing every dart of a preconnected graph leaves at most one vertex. -/
theorem Preconnected.subsingleton_collapse_univ (h : Γ.Preconnected)
    (hS : ∀ e ∈ (Set.univ : Set Γ.E), Γ.rev e ∈ (Set.univ : Set Γ.E)) :
    Subsingleton (Γ.collapse Set.univ hS).V := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨a, rfl⟩ := Γ.collapseVertex_surjective _ hS x
  obtain ⟨b, rfl⟩ := Γ.collapseVertex_surjective _ hS y
  exact (collapseVertex_eq_iff hS).mpr
    ⟨(Γ.preconnected_iff.mp h a b).some, fun _ _ => Set.mem_univ _⟩

/-! ### Induced automorphisms -/

namespace Aut

variable {Γ S}

/-- An automorphism mapping collapsed darts to collapsed darts preserves the fibres of the
collapse map. -/
theorem collapseVertex_smul_eq (φ : Γ.Aut) (hφ : ∀ e ∈ S, φ • e ∈ S) {a b : Γ.V}
    (h : Γ.collapseVertex S hS a = Γ.collapseVertex S hS b) :
    Γ.collapseVertex S hS (φ • a) = Γ.collapseVertex S hS (φ • b) := by
  obtain ⟨p, hp⟩ := (collapseVertex_eq_iff hS).mp h
  clear h
  induction p with
  | nil => rfl
  | cons p e ih =>
    obtain ⟨e, rfl, rfl⟩ := e
    rw [ih fun f hf => hp f (by simp [hf]), ← src_smul, ← tgt_smul]
    exact collapseVertex_src_eq_tgt hS (hφ e (hp e (by simp)))

/-- The automorphism of the collapse induced by an automorphism preserving the set of collapsed
darts. -/
def collapse (φ : Γ.Aut) (hφ : ∀ e, φ • e ∈ S ↔ e ∈ S) : (Γ.collapse S hS).Aut where
  equivV :=
    { toFun := Quotient.lift (fun a => Γ.collapseVertex S hS (φ • a)) fun _ _ h =>
        φ.collapseVertex_smul_eq hS (fun e => (hφ e).mpr) (Quotient.sound h)
      invFun := Quotient.lift (fun a => Γ.collapseVertex S hS (φ⁻¹ • a)) fun _ _ h =>
        φ⁻¹.collapseVertex_smul_eq hS (fun e he => (hφ _).mp (by rwa [smul_inv_smul]))
          (Quotient.sound h)
      left_inv := by
        rintro ⟨a⟩
        exact congrArg (Γ.collapseVertex S hS) (inv_smul_smul φ a)
      right_inv := by
        rintro ⟨a⟩
        exact congrArg (Γ.collapseVertex S hS) (smul_inv_smul φ a) }
  equivE :=
    { toFun e := ⟨φ • e.1, fun h => e.2 ((hφ _).mp h)⟩
      invFun e := ⟨φ⁻¹ • e.1, fun h => e.2 (by simpa using (hφ _).mpr h)⟩
      left_inv e := Subtype.ext (inv_smul_smul φ e.1)
      right_inv e := Subtype.ext (smul_inv_smul φ e.1) }
  map_src e := congrArg (Γ.collapseVertex S hS) (src_smul φ e.1)
  map_rev e := Subtype.ext (rev_smul φ e.1).symm

/-- The induced automorphism of the collapse commutes with the collapse map. -/
@[simp] theorem collapse_smul_collapseVertex (φ : Γ.Aut) (hφ : ∀ e, φ • e ∈ S ↔ e ∈ S)
    (a : Γ.V) :
    φ.collapse hS hφ • Γ.collapseVertex S hS a = Γ.collapseVertex S hS (φ • a) := (rfl)

/-- The induced automorphism of the collapse acts on the remaining darts as the given one. -/
@[simp] theorem collapse_smul_val (φ : Γ.Aut) (hφ : ∀ e, φ • e ∈ S ↔ e ∈ S)
    (e : (Γ.collapse S hS).E) : (φ.collapse hS hφ • e).1 = φ • e.1 := (rfl)

/-- The identity induces the identity of the collapse. -/
theorem collapse_one (h : ∀ e, (1 : Γ.Aut) • e ∈ S ↔ e ∈ S) :
    (1 : Γ.Aut).collapse hS h = 1 := by
  refine ext (fun x => ?_) fun e => Subtype.ext ?_
  · obtain ⟨a, rfl⟩ := Γ.collapseVertex_surjective S hS x
    rw [← smul_vertex_def, ← smul_vertex_def, collapse_smul_collapseVertex, one_smul, one_smul]
  · rw [← smul_dart_def, ← smul_dart_def, collapse_smul_val, one_smul, one_smul]

/-- The automorphism of the collapse induced by a composite is the composite of the induced
automorphisms. -/
theorem collapse_mul (φ ψ : Γ.Aut) (hφ : ∀ e, φ • e ∈ S ↔ e ∈ S)
    (hψ : ∀ e, ψ • e ∈ S ↔ e ∈ S) (h : ∀ e, (φ * ψ) • e ∈ S ↔ e ∈ S) :
    (φ * ψ).collapse hS h = φ.collapse hS hφ * ψ.collapse hS hψ := by
  refine ext (fun x => ?_) fun e => Subtype.ext ?_
  · obtain ⟨a, rfl⟩ := Γ.collapseVertex_surjective S hS x
    simp only [← smul_vertex_def, collapse_smul_collapseVertex, mul_smul]
  · simp only [← smul_dart_def, collapse_smul_val, mul_smul]

end Aut

end SerreGraph

end TauCeti
