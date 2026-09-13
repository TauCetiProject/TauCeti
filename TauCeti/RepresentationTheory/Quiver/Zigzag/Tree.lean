/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# Skew-zigzag algebras of trees and forests

A skew-zigzag parameter records ratios between backtracks along edges incident to the same vertex.
On an acyclic graph these local ratios can be integrated to a global scale on the unoriented edges:
choose a root in every connected component, transport vertex normalizations along the unique paths
from it, and use the resulting edge scales to rescale one orientation of every edge. Consequently
every skew-zigzag parameter on a forest is gauge equivalent to the constant parameter, and its
relation quotient is isomorphic to the ordinary zigzag relation quotient. Connectedness enters only
at the last step, where the ordinary relation quotient of a tree is identified with the public
componentwise zigzag algebra.

## Main results

* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_isAcyclic`: every skew parameter on a
  forest is gauge equivalent to the constant parameter.
* `TauCeti.nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic`: every skew-zigzag relation
  quotient of a finite forest is isomorphic to the ordinary relation quotient.
* `TauCeti.nonempty_algEquiv_zigzagAlgebra_of_isTree`: on a nontrivial finite tree, that ordinary
  quotient is the public componentwise zigzag algebra.

## References

C. Couture, *Skew-Zigzag Algebras*, Theorem 4.8 and Corollary 4.13,
https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w

namespace SkewZigzagParameter

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V}

/-! ### Local edge coordinates -/

variable (G) in
/-- A distinguished incident edge at a vertex having at least one. -/
private noncomputable def reference (v : V) (hv : (G.neighborSet v).Nonempty) :
    G.neighborSet v :=
  Classical.choice hv.to_subtype

/-- The local coordinate of an incident edge relative to the distinguished edge at its source. -/
private noncomputable def localCoordinate (c : SkewZigzagParameter k G) {v w : V}
    (h : G.Adj v w) : kˣ :=
  c.ratio h (reference G v ⟨w, h⟩).property

/-- The change of local edge coordinates across an oriented edge. -/
private noncomputable def transition (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    kˣ :=
  localCoordinate c h / localCoordinate c h.symm

private theorem ratio_eq_localCoordinate_div (c : SkewZigzagParameter k G) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    c.ratio h h' = localCoordinate c h / localCoordinate c h' := by
  rw [eq_div_iff_mul_eq']
  exact ratio_mul_ratio c h h' (reference G i ⟨j, h⟩).property

@[simp]
private theorem transition_symm (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition c h.symm = (transition c h)⁻¹ := by
  rw [transition, transition, inv_div]

private theorem transition_arrow (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition c (arrow G h).down = transition c h := by
  congr <;> simp

/-! ### The potential of a forest -/

variable (G) in
/-- The chosen root of the connected component of a vertex. -/
private noncomputable def root (v : V) : V :=
  (G.connectedComponentMk v).nonempty_supp.some

private theorem reachable_root (v : V) : G.Reachable (root G v) v :=
  SimpleGraph.ConnectedComponent.exact
    ((G.connectedComponentMk v).nonempty_supp.some_mem)

private theorem root_eq_of_adj {v w : V} (h : G.Adj v w) : root G w = root G v :=
  congrArg (fun C : G.ConnectedComponent => C.nonempty_supp.some)
    (SimpleGraph.ConnectedComponent.sound h.symm.reachable)

variable (G) in
/-- The distance from a vertex to the chosen root of its connected component. -/
private noncomputable def depth (v : V) : ℕ :=
  G.dist (root G v) v

private theorem depth_eq_add_one_of_adj (hG : G.IsAcyclic) {v w : V} (h : G.Adj v w) :
    depth G v = depth G w + 1 ∨ depth G w = depth G v + 1 := by
  unfold depth
  rw [root_eq_of_adj h]
  exact hG.dist_eq_dist_add_one_of_adj_of_reachable _ h (reachable_root v)

variable (G) in
/-- A shortest path from the chosen root of a connected component to one of its vertices. -/
private noncomputable def rootPath (v : V) : G.Walk (root G v) v :=
  (reachable_root v).exists_path_of_dist.choose

private theorem rootPath_isPath (v : V) : (rootPath G v).IsPath :=
  (reachable_root v).exists_path_of_dist.choose_spec.1

private theorem length_rootPath (v : V) : (rootPath G v).length = depth G v :=
  (reachable_root v).exists_path_of_dist.choose_spec.2

/-- The product of the transition factors along a walk. -/
private noncomputable def walkTransition (c : SkewZigzagParameter k G) {v w : V}
    (q : G.Walk v w) : kˣ :=
  Quiver.Path.weight (fun {x y : DoubledQuiver G} (e : x ⟶ y) ↦ transition c e.down)
    (walkToPath G q)

private theorem walkTransition_concat (c : SkewZigzagParameter k G) {r v w : V} (q : G.Walk r v)
    (h : G.Adj v w) : walkTransition c (q.concat h) = walkTransition c q * transition c h := by
  simp only [walkTransition, SimpleGraph.Walk.concat_eq_append, walkToPath_append,
    Quiver.Path.weight_comp, walkToPath_toWalk, Quiver.Path.weight_toPath]
  rw [transition_arrow c h]

/-- The potential obtained by multiplying transition factors along the path from the root of the
component of a vertex. -/
private noncomputable def potential (c : SkewZigzagParameter k G) (v : V) : kˣ :=
  walkTransition c (rootPath G v)

private theorem potential_eq_walkTransition (hG : G.IsAcyclic) (c : SkewZigzagParameter k G)
    {r v : V} (hr : root G v = r) (q : G.Walk r v) (hq : q.IsPath) :
    potential c v = walkTransition c q := by
  subst hr
  have hpath : rootPath G v = q :=
    congrArg Subtype.val
      ((hG.subsingleton_path _ _).allEq ⟨rootPath G v, rootPath_isPath v⟩ ⟨q, hq⟩)
  rw [potential, hpath]

private theorem potential_mul_transition (hG : G.IsAcyclic) (c : SkewZigzagParameter k G)
    {v w : V} (h : G.Adj v w) : potential c w = potential c v * transition c h := by
  have hrt : root G w = root G v := root_eq_of_adj h
  have hdw : G.dist (root G v) w = depth G w := by unfold depth; rw [hrt]
  rcases depth_eq_add_one_of_adj hG h with hvw | hwv
  -- The root path to `v` runs through `w`, so it is the root path to `w` extended by the edge.
  · obtain ⟨q, hq, hlq⟩ :=
      (hrt ▸ reachable_root w : G.Reachable (root G v) w).exists_path_of_dist
    have hcat : (q.concat h.symm).IsPath := by
      apply SimpleGraph.Walk.isPath_of_length_eq_dist
      rw [SimpleGraph.Walk.length_concat, hlq, hdw, ← hvw, depth]
    have hv := potential_eq_walkTransition hG c rfl _ hcat
    rw [walkTransition_concat, ← potential_eq_walkTransition hG c hrt q hq,
      transition_symm c h] at hv
    rw [hv, mul_assoc, inv_mul_cancel, mul_one]
  -- The root path to `w` is the root path to `v` extended by the edge.
  · have hcat : ((rootPath G v).concat h).IsPath := by
      apply SimpleGraph.Walk.isPath_of_length_eq_dist
      rw [SimpleGraph.Walk.length_concat, length_rootPath, ← hwv, hdw]
    rw [potential_eq_walkTransition hG c hrt _ hcat, walkTransition_concat, potential]

/-! ### Trivializing the parameter -/

/-- The unoriented edge scale obtained from a vertex potential and the local edge coordinates. -/
private noncomputable def edgeScale (c : SkewZigzagParameter k G) (a : V → kˣ) {v w : V}
    (h : G.Adj v w) : kˣ :=
  a v * localCoordinate c h

private theorem edgeScale_symm_of_potential (c : SkewZigzagParameter k G) (a : V → kˣ)
    (ha : ∀ {v w : V} (h : G.Adj v w), a w = a v * transition c h)
    {v w : V} (h : G.Adj v w) :
    edgeScale c a h.symm = edgeScale c a h := by
  rw [edgeScale, edgeScale, ha h, transition]
  simp only [div_mul_cancel, mul_assoc]

private theorem ratio_eq_edgeScale_div (c : SkewZigzagParameter k G) (a : V → kˣ) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    c.ratio h h' = edgeScale c a h / edgeScale c a h' := by
  rw [ratio_eq_localCoordinate_div c h h', edgeScale, edgeScale, mul_div_mul_left_eq_div]

/-- Orient each edge away from the root of its component and put its scale on that orientation
only. -/
private noncomputable def forestLabelling (c : SkewZigzagParameter k G) (a : V → kˣ) :
    ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ :=
  fun ⦃x y⦄ e ↦
    if depth G ((vertexEquiv G).symm x) < depth G ((vertexEquiv G).symm y) then
      edgeScale c a e.down
    else 1

private theorem backtrackScale_forestLabelling (c : SkewZigzagParameter k G) (hG : G.IsAcyclic)
    (a : V → kˣ) (ha : ∀ {v w : V} (h : G.Adj v w), a w = a v * transition c h)
    {v w : V} (h : G.Adj v w) :
    backtrackScale G (forestLabelling c a) h = edgeScale c a h := by
  rcases depth_eq_add_one_of_adj hG h with hvw | hwv
  · rw [DoubledQuiver.backtrackScale_apply]
    unfold forestLabelling
    simp only [vertexEquiv_symm_vertex]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), one_mul,
      edgeScale_symm_of_potential c a ha h]
  · rw [DoubledQuiver.backtrackScale_apply]
    unfold forestLabelling
    simp only [vertexEquiv_symm_vertex]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), mul_one]

/-- **Every skew-zigzag parameter on a forest is gauge equivalent to the constant parameter.** This
includes graphs with isolated vertices, at which there are no incident-edge ratios to trivialize. -/
theorem isGaugeEquivalent_one_of_isAcyclic (c : SkewZigzagParameter k G) (hG : G.IsAcyclic) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  have ha : ∀ {v w : V} (h : G.Adj v w), potential c w = potential c v * transition c h :=
    fun h ↦ potential_mul_transition hG c h
  apply IsGaugeEquivalent.symm
  rw [isGaugeEquivalent_iff]
  refine ⟨forestLabelling c (potential c), ?_⟩
  ext i j j' h h'
  rw [one_ratio, gauge_ratio,
    backtrackScale_forestLabelling c hG (potential c) ha h,
    backtrackScale_forestLabelling c hG (potential c) ha h',
    ratio_eq_edgeScale_div c (potential c) h h']
  simp

end SkewZigzagParameter

/-- **Every skew-zigzag relation quotient of a finite forest is isomorphic to the ordinary zigzag
relation quotient.** The isomorphism is induced by rescaling the doubled arrows. -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic
    (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
    (c : SkewZigzagParameter k G) (hG : G.IsAcyclic) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] nonisolatedZigzagQuotient k G) :=
  nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one k G
    (c.isGaugeEquivalent_one_of_isAcyclic hG)

/-- **Every skew-zigzag relation quotient of a finite nontrivial tree is isomorphic to the public
ordinary zigzag algebra.** The nontriviality assumption excludes the exceptional one-vertex
convention, where the public ordinary zigzag algebra is the dual numbers rather than the doubled
path-algebra quotient. -/
theorem nonempty_algEquiv_zigzagAlgebra_of_isTree
    (k : Type w) [CommRing k] {V : Type u} [Finite V] [Nontrivial V]
    (G : SimpleGraph V) (c : SkewZigzagParameter k G) (hG : G.IsTree) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] zigzagAlgebra k G) := by
  obtain ⟨e⟩ := nonempty_algEquiv_nonisolatedZigzagQuotient_of_isAcyclic k G c hG.isAcyclic
  exact ⟨e.trans (zigzagAlgebraEquivNonisolated k G hG.connected).symm⟩

end TauCeti
