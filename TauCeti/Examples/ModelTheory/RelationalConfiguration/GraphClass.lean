/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Operations
public import Mathlib.ModelTheory.Order
public import TauCeti.ModelTheory.RelationalConfiguration.GraphClass

/-!
# Examples of codes of simple graphs

The code of the empty graph on `ℕ` lies in `graphClass`; a code with `adj(0, 0)`, or with
`adj(0, 1)` but not `adj(1, 0)`, does not. The codes of the one-edge graphs on `{0, 1}` and on
`{5, 7}` are isomorphic, and the code of the one-edge graph is not isomorphic to that of the path
`0 - 1 - 2`. The class is the range of the coding of simple graphs, membership depends only on
the adjacency atoms, and it is an intersection of clopen sets, so closed and standard Borel.

Borel completeness passes to unions but not to intersections: `graphClass` meets the class of the
single code of the empty graph, which is isomorphism invariant and Borel, in that one code, and a
class with one isomorphism class is not Borel complete. Renaming the symbol `adj` to the distinct
binary symbol `le` of `Language.order` is a language equivalence, and the image of `graphClass`
under it is Borel complete.
-/

public section

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The code of the empty graph is a code of a simple graph.
example : (⊥ : SimpleGraph ℕ).toRelationalConfiguration ∈ graphClass := by
  simp

-- A code with `adj(0, 0)` is not.
example : adjArrayEquiv.symm (fun p => decide (p = (0, 0))) ∉ graphClass := fun h => by
  simpa using (isSimpleGraph_iff.1 (mem_graphClass.1 h)).2 0

-- A code with `adj(0, 1)` but not `adj(1, 0)` is not.
example : adjArrayEquiv.symm (fun p => decide (p = (0, 1))) ∉ graphClass := fun h => by
  simpa using (isSimpleGraph_iff.1 (mem_graphClass.1 h)).1 0 1

-- The codes of the one-edge graphs on `{0, 1}` and on `{5, 7}` are isomorphic.
example : isoSetoid Language.graph ℕ (SimpleGraph.edge 0 1).toRelationalConfiguration
    (SimpleGraph.edge 5 7).toRelationalConfiguration := by
  refine isoSetoid_toRelationalConfiguration_iff.2
    ⟨⟨(Equiv.swap 1 7).trans (Equiv.swap 0 5), fun {a b} => ?_⟩⟩
  simp only [Equiv.trans_apply, SimpleGraph.edge_adj, Equiv.swap_apply_def]
  grind

-- The code of the one-edge graph is not isomorphic to that of the path `0 - 1 - 2`: in the path,
-- `1` has the two neighbours `0` and `2`.
example : ¬isoSetoid Language.graph ℕ (SimpleGraph.edge 0 1).toRelationalConfiguration
    (SimpleGraph.edge 0 1 ⊔ SimpleGraph.edge 1 2).toRelationalConfiguration := by
  rw [isoSetoid_toRelationalConfiguration_iff]
  rintro ⟨f⟩
  have h0 : (SimpleGraph.edge 0 1).Adj (f.symm 1) (f.symm 0) :=
    f.symm.map_adj_iff.2 (by simp [SimpleGraph.edge_adj])
  have h2 : (SimpleGraph.edge 0 1).Adj (f.symm 1) (f.symm 2) :=
    f.symm.map_adj_iff.2 (by simp [SimpleGraph.edge_adj])
  have hne : f.symm 0 ≠ f.symm 2 := fun h => by simpa using f.symm.injective h
  simp only [SimpleGraph.edge_adj] at h0 h2
  omega

/-! ### The class as a set of codes -/

-- `graphClass` is the range of the coding of simple graphs.
example : Set.range (SimpleGraph.toRelationalConfiguration :
    SimpleGraph ℕ → RelationalConfiguration Language.graph ℕ) = graphClass :=
  range_toRelationalConfiguration_eq_graphClass

-- Membership of a code depends only on its values at the adjacency atoms.
example {c d : RelationalConfiguration Language.graph ℕ}
    (h : ∀ u v, c.eval (adjAtom u v) = d.eval (adjAtom u v)) :
    c ∈ graphClass ↔ d ∈ graphClass := by
  simp only [mem_graphClass, isSimpleGraph_iff, h]

-- `graphClass` is the intersection of the clopen sets `{adj(u, v) = adj(v, u)}` and
-- `{adj(v, v) = false}`.
example : graphClass = (⋂ u, ⋂ v, {c : RelationalConfiguration Language.graph ℕ |
      c.eval (adjAtom u v) = c.eval (adjAtom v u)}) ∩
    ⋂ v, {c : RelationalConfiguration Language.graph ℕ | c.eval (adjAtom v v) = false} := by
  ext c
  simp [isSimpleGraph_iff]

example (u v : ℕ) : IsClopen {c : RelationalConfiguration Language.graph ℕ |
    c.eval (adjAtom u v) = c.eval (adjAtom v u)} := by
  have : {c : RelationalConfiguration Language.graph ℕ |
      c.eval (adjAtom u v) = c.eval (adjAtom v u)} =
      ({c | c.eval (adjAtom u v) = true} ∩ {c | c.eval (adjAtom v u) = true}) ∪
        ({c | c.eval (adjAtom u v) = false} ∩ {c | c.eval (adjAtom v u) = false}) := by
    ext c
    rcases h₁ : c.eval (adjAtom u v) <;> rcases h₂ : c.eval (adjAtom v u) <;> simp [h₁, h₂]
  rw [this]
  exact ((isClopen_setOf_eval _ _).inter (isClopen_setOf_eval _ _)).union
    ((isClopen_setOf_eval _ _).inter (isClopen_setOf_eval _ _))

example (v : ℕ) : IsClopen {c : RelationalConfiguration Language.graph ℕ |
    c.eval (adjAtom v v) = false} :=
  isClopen_setOf_eval _ _

-- Hence it is closed, and a standard Borel space.
example : IsClosed graphClass := isClosed_graphClass

example : StandardBorelSpace graphClass := inferInstance

/-! ### Unions and intersections -/

namespace TauCeti.Examples.ModelTheory.GraphClass

/-- The class whose only member is the code of the empty graph on `ℕ`. -/
noncomputable def emptyGraphClass : Set (RelationalConfiguration Language.graph ℕ) :=
  {(⊥ : SimpleGraph ℕ).toRelationalConfiguration}

-- The code of the empty graph is fixed by every permutation, so its class is invariant.
example : IsomorphismInvariant emptyGraphClass := by
  refine isomorphismInvariant_iff.2 fun c d hcd hc => ?_
  obtain ⟨σ, rfl⟩ := isoSetoid_iff_exists_perm_smul_eq.1 hcd
  rw [emptyGraphClass, Set.mem_singleton_iff] at hc ⊢
  rw [hc, perm_smul_def, ← SimpleGraph.toRelationalConfiguration_comap]
  rfl

-- The class is Borel.
example : MeasurableSet emptyGraphClass :=
  measurableSet_singleton _

-- The union of `graphClass` with an invariant Borel class is Borel complete.
example : BorelComplete (graphClass ∪ emptyGraphClass) :=
  borelComplete_graphClass.mono Set.subset_union_left

-- The intersection of `graphClass` with that class is the single code of the empty graph.
example : graphClass ∩ emptyGraphClass = emptyGraphClass :=
  Set.inter_eq_right.2 <| Set.singleton_subset_iff.2 (toRelationalConfiguration_mem_graphClass _)

-- The intersection is not Borel complete: a reduction of isomorphism on `graphClass` into a class
-- with one code would make the empty graph isomorphic to the complete graph.
example : ¬BorelComplete (graphClass ∩ emptyGraphClass) := by
  intro h
  obtain ⟨f, -, hf⟩ := Setoid.borelReducible_iff.1 <| borelComplete_iff.1 h Language.graph
    graphClass measurableSet_graphClass isomorphismInvariant_graphClass
  have hsub : graphClass ∩ emptyGraphClass ⊆ emptyGraphClass := Set.inter_subset_right
  let x : graphClass := ⟨_, toRelationalConfiguration_mem_graphClass ⊥⟩
  let y : graphClass := ⟨_, toRelationalConfiguration_mem_graphClass ⊤⟩
  have hxy : f x = f y := Subtype.ext <| (Set.mem_singleton_iff.1 (hsub (f x).property)).trans
    (Set.mem_singleton_iff.1 (hsub (f y).property)).symm
  obtain ⟨e⟩ := isoSetoid_toRelationalConfiguration_iff.1 <| classIso_apply.1 <|
    (hf x y).2 (hxy ▸ (classIso _).refl _)
  simpa using e.symm.map_adj_iff.2 (show (⊤ : SimpleGraph ℕ).Adj 0 1 by simp)

/-! ### Renaming the symbol -/

/-- Renaming `adj` to the binary symbol `le` of `Language.order` is an equivalence of
languages. -/
def graphEquivOrder : Language.graph ≃ᴸ Language.order where
  toLHom := ⟨fun _ => isEmptyElim, fun _ r => by cases r; exact .le⟩
  invLHom := ⟨fun _ => isEmptyElim, fun _ r => by cases r; exact .adj⟩
  left_inv := LHom.funext (funext fun _ => funext fun f => isEmptyElim f)
    (funext fun _ => funext fun r => by cases r; rfl)
  right_inv := LHom.funext (funext fun _ => funext fun f => isEmptyElim f)
    (funext fun _ => funext fun r => by cases r; rfl)

-- The image of `graphClass` under the renaming is Borel complete.
example : BorelComplete (graphEquivOrder.onConfiguration '' graphClass) :=
  (borelComplete_image_onConfiguration_iff _).2 borelComplete_graphClass

end TauCeti.Examples.ModelTheory.GraphClass
