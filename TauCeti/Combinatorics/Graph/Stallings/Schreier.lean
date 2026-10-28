/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Graph.Stallings.Folded
public import TauCeti.Combinatorics.Graph.Serre.OfQuiver
public import TauCeti.Combinatorics.Quiver.Schreier
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Schreier graphs and accepted subgroups

`StallingsGraph.actionGraph` turns an action of a free group into a folded labelled
Serre graph. Its accepted subgroup at a vertex is exactly that vertex's stabilizer.
`Subgroup.schreierGraph H` specializes this to cosets of a subgroup `H`: it is
connected, folded, has every outgoing label, and accepts precisely `H` at its base.
Taking its based core is the usual construction of the subgroup graph.

The construction reuses Runtian Zhou's `Quiver.SchreierGraph` and `pathFromWord` in Mathlib.
We use the inverse basis elements in the left action, so a path reading `g` ends at
`g⁻¹ • v`. On cosets, inversion identifies these vertices with right cosets `H g`,
and positive labels act by right multiplication, as in the usual convention.

## References

* I. Kapovich and A. Myasnikov, *Stallings foldings and subgroups of free groups*,
  Section 5, Theorem 5.1.
-/

public section

namespace TauCeti.StallingsGraph

open Quiver

variable {α V : Type*} [MulAction (FreeGroup α) V]

/-- The labelled Serre graph of a free-group action, with a specified base vertex.
A positive `a`-dart moves `v` to `(FreeGroup.of a)⁻¹ • v`. -/
@[expose, instance_reducible] def actionGraph (base : V) : StallingsGraph α where
  graph := SerreGraph.ofQuiver (SchreierGraph V (fun a : α => (FreeGroup.of a)⁻¹))
  base := ⟨base⟩
  label := fun e => e.hom.elim (fun f => (f.1, true)) (fun f => (f.1, false))
  label_rev := by
    rintro ⟨a, b, e⟩
    cases e <;> rfl

@[simp] theorem actionGraph_base (base : V) :
    (actionGraph (α := α) base).base = SchreierGraph.ofVertex base := (rfl)

@[simp] theorem actionGraph_label_pos (base : V)
    {a b : SchreierGraph V (fun a : α => (FreeGroup.of a)⁻¹)} (e : a ⟶ b) :
    (actionGraph base).label ⟨a, b, Sum.inl e⟩ = (e.1, true) := (rfl)

@[simp] theorem actionGraph_label_neg (base : V)
    {a b : SchreierGraph V (fun a : α => (FreeGroup.of a)⁻¹)} (e : b ⟶ a) :
    (actionGraph base).label ⟨a, b, Sum.inr e⟩ = (e.1, false) := (rfl)

/-- A dart translates its source vertex to its target by the inverse of its reading. -/
theorem actionGraph_dart_endpoint (base : V)
    (e : (actionGraph (α := α) base).graph.E) :
    (FreeGroup.mk [(actionGraph base).label e])⁻¹ •
      ((actionGraph base).graph.src e).toVertex =
        ((actionGraph base).graph.tgt e).toVertex := by
  -- Endpoint rewriting crosses the semireducible symmetrified vertex carrier.
  erw [SerreGraph.ofQuiver_src, SerreGraph.ofQuiver_tgt]
  rcases e with ⟨a, b, e | e⟩
  · -- The label lemma has the same carrier transport as the endpoint lemmas.
    erw [actionGraph_label_pos]
    exact congrArg SchreierGraph.toVertex e.2
  · have hneg : FreeGroup.mk [(e.1, false)] = (FreeGroup.of e.1)⁻¹ := by
      simp [FreeGroup.of, FreeGroup.inv_mk, FreeGroup.invRev]
    -- Rewriting the label also crosses the semireducible vertex carrier.
    erw [actionGraph_label_neg]
    simpa only [hneg, inv_inv] using
      (inv_smul_eq_iff.mp (congrArg SchreierGraph.toVertex e.2)).symm

/-- A path reading `g` ends at the translate by `g⁻¹` of its starting vertex. -/
theorem actionGraph_read_endpoint (base : V)
    {a b : (actionGraph (α := α) base).graph.V}
    (p : (actionGraph base).graph.Path a b) :
    ((actionGraph base).read p)⁻¹ • a.toVertex = b.toVertex := by
  induction p with
  | nil => simp
  | cons p e ih =>
    rw [read_cons, mul_inv_rev, mul_smul, ih]
    simpa only [e.2.1, e.2.2] using actionGraph_dart_endpoint base e.1

/-- Every free-group element can be read starting at any vertex of the action graph. -/
theorem actionGraph_exists_path_read_eq (base : V)
    (a : (actionGraph (α := α) base).graph.V) (g : FreeGroup α) :
    ∃ b, ∃ p : (actionGraph base).graph.Path a b, (actionGraph base).read p = g := by
  classical
  have h := SchreierGraph.weight_pathFromWord
    (fun a : α => (FreeGroup.of a)⁻¹)
    (SchreierGraph.ofVertex a.toVertex) g.toWord.reverse
  let p := (SerreGraph.ofQuiverPrefunctor
    (SchreierGraph V (fun a : α => (FreeGroup.of a)⁻¹))).mapPath
      (SchreierGraph.pathFromWord (fun a : α => (FreeGroup.of a)⁻¹)
        (SchreierGraph.ofVertex a.toVertex) g.toWord.reverse)
  refine ⟨_, p.cast ?_ rfl, ?_⟩
  · simp only [SerreGraph.ofQuiverPrefunctor_obj]
    rfl
  dsimp only [p]
  simp only [List.reverse_reverse, FreeGroup.mk_toWord] at h
  -- Transport crosses the semireducible symmetrified vertex carrier.
  erw [read_eq_weight, Quiver.Path.weight_cast, Prefunctor.weight_mapPath]
  convert h using 1
  congr 1
  funext x y e
  -- The map's vertex parameters use the semireducible Symmetrify carrier,
  -- so rewriting its dart value requires the same transport transparency as above.
  erw [SerreGraph.ofQuiverPrefunctor_map_val]
  -- On each summand the action-graph label reduces to the signed Schreier weight.
  cases e <;> rfl

/-- Reading closed paths in an action graph gives exactly the vertex stabilizer. -/
@[simp] theorem actionGraph_subgroup (base : V)
    (a : (actionGraph (α := α) base).graph.V) :
    (actionGraph base).subgroup a = MulAction.stabilizer (FreeGroup α) a.toVertex := by
  ext g
  rw [mem_subgroup_iff, MulAction.mem_stabilizer_iff]
  constructor
  · rintro ⟨p, rfl⟩
    have hp := actionGraph_read_endpoint base p
    exact inv_smul_eq_iff.mp hp |>.symm
  · intro hg
    obtain ⟨b, p, hp⟩ := actionGraph_exists_path_read_eq base a g
    have hb : b = a := by
      apply SchreierGraph.ext
      rw [← actionGraph_read_endpoint base p, hp]
      exact inv_smul_eq_iff.mpr hg.symm
    subst b
    exact ⟨p, hp⟩

/-- The label and initial vertex determine a dart of the action graph. -/
theorem actionGraph_isFolded (base : V) : (actionGraph (α := α) base).IsFolded := by
  rw [isFolded_def]
  rintro ⟨a, b, e | e⟩ ⟨c, d, f | f⟩ hs hl
  all_goals simp only [actionGraph, SerreGraph.ofQuiver_src] at hs hl
  · cases hs
    have he : e.1 = f.1 := congrArg Prod.fst hl
    have hb : b = d := e.2.symm.trans (he ▸ f.2)
    cases hb
    congr 2
    exact Subtype.ext he
  · simp at hl
  · simp at hl
  · cases hs
    have he : e.1 = f.1 := congrArg Prod.fst hl
    have hb : b = d := (inv_smul_eq_iff.mp e.2).trans
      (he ▸ (inv_smul_eq_iff.mp f.2).symm)
    cases hb
    congr 2
    exact Subtype.ext he

/-- Every signed letter occurs on an outgoing dart at every action-graph vertex. -/
theorem actionGraph_exists_dart (base : V)
    (a : (actionGraph (α := α) base).graph.V) (l : α × Bool) :
    ∃ e : (actionGraph base).graph.E,
      (actionGraph base).graph.src e = a ∧ (actionGraph base).label e = l := by
  rcases l with ⟨i, b⟩
  cases b
  · exact ⟨⟨a, SchreierGraph.ofVertex (FreeGroup.of i • a.toVertex),
      Sum.inr ⟨i, by
        apply SchreierGraph.ext
        exact inv_smul_smul (FreeGroup.of i) a.toVertex⟩⟩, rfl, rfl⟩
  · exact ⟨⟨a, SchreierGraph.ofVertex ((FreeGroup.of i)⁻¹ • a.toVertex),
      Sum.inl ⟨i, rfl⟩⟩, rfl, rfl⟩

end TauCeti.StallingsGraph

namespace Subgroup

open Quiver TauCeti TauCeti.StallingsGraph

variable {α : Type*}

/-- The Schreier coset graph of a subgroup, based at the identity coset. -/
@[expose, instance_reducible] def schreierGraph (H : Subgroup (FreeGroup α)) : StallingsGraph α :=
  actionGraph ((1 : FreeGroup α) : FreeGroup α ⧸ H)

@[simp] theorem schreierGraph_base (H : Subgroup (FreeGroup α)) :
    H.schreierGraph.base = SchreierGraph.ofVertex ((1 : FreeGroup α) : FreeGroup α ⧸ H) :=
  (rfl)

/-- The coset graph accepts precisely the original subgroup at its base vertex. -/
@[simp] theorem schreierGraph_subgroup (H : Subgroup (FreeGroup α)) :
    H.schreierGraph.subgroup (SchreierGraph.ofVertex ((1 : FreeGroup α) : FreeGroup α ⧸ H)) =
      H := by
  exact (actionGraph_subgroup _ _).trans (MulAction.stabilizer_quotient H)

/-- The Schreier coset graph is folded. -/
theorem schreierGraph_isFolded (H : Subgroup (FreeGroup α)) :
    (schreierGraph H).IsFolded := actionGraph_isFolded _

/-- Every vertex of the coset graph can be reached from its base vertex. -/
theorem schreierGraph_reachable (H : Subgroup (FreeGroup α))
    (a : (schreierGraph H).graph.V) :
    Nonempty ((schreierGraph H).graph.Path (schreierGraph H).base a) := by
  rcases a with ⟨a⟩
  induction a using Quotient.inductionOn' with
  | h g =>
    obtain ⟨b, p, hp⟩ := actionGraph_exists_path_read_eq
      ((1 : FreeGroup α) : FreeGroup α ⧸ H) (schreierGraph H).base g⁻¹
    have hb : b = SchreierGraph.ofVertex (g : FreeGroup α ⧸ H) := by
      apply SchreierGraph.ext
      rw [← actionGraph_read_endpoint _ p, hp]
      simp [schreierGraph_base]
    subst b
    exact ⟨p⟩

end Subgroup
