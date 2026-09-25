/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Metric

public import Mathlib.Combinatorics.SimpleGraph.Paths
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# Transition factors of a skew-zigzag parameter and their integration

A skew-zigzag parameter records ratios between backtracks along edges incident to the same vertex.
Choosing a reference edge at every vertex turns these ratios into local edge coordinates, and
comparing the two ends of an edge gives a transition factor across it. Multiplying transition
factors along the darts of a walk gives the transition factor of the walk.

When the transition factor of a path depends only on its endpoints, multiplying transition factors
along paths from a chosen root in every connected component gives a vertex potential, a unit at
every vertex changing by the transition factor across every edge. The local ratios then integrate
to a global scale on the unoriented edges, and rescaling one orientation of every edge by it
trivializes the parameter.

## Main definitions

* `TauCeti.SkewZigzagParameter.localCoordinate`: the ratio from an incident edge to a chosen
  reference edge at its source.
* `TauCeti.SkewZigzagParameter.transition`: the change of local edge coordinates across an
  oriented edge.
* `TauCeti.SkewZigzagParameter.walkTransition`: the product of the transition factors along a
  walk.

## Main results

* `TauCeti.SkewZigzagParameter.ratio_eq_localCoordinate_div`: every ratio is a quotient of local
  edge coordinates.
* `TauCeti.SkewZigzagParameter.transition_mul`: transition factors are multiplicative in the
  parameter.
* `TauCeti.SkewZigzagParameter.localCoordinate_map`: local coordinates are carried by the
  monoid homomorphism mapping a parameter.
* `TauCeti.SkewZigzagParameter.transition_map`: transition factors are carried by the monoid
  homomorphism mapping a parameter.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_potential`: a vertex potential for the
  transition factors trivializes the parameter.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_walkTransition_eq`: a parameter whose
  transition factor along a path depends only on its endpoints is gauge trivial.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, Theorem 4.8, https://arxiv.org/abs/1509.08405.
-/

public section

namespace TauCeti

open DoubledQuiver

universe u w z

namespace SkewZigzagParameter

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V}

/-! ### Local edge coordinates -/

variable (G) in
/-- A distinguished incident edge at a vertex having at least one. -/
private noncomputable def reference (v : V) (hv : (G.neighborSet v).Nonempty) :
    G.neighborSet v :=
  Classical.choice hv.to_subtype

/-- The **local coordinate** of an incident edge: its ratio to a chosen reference edge at its
source. -/
noncomputable def localCoordinate (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) : kˣ :=
  c.ratio h (reference G v ⟨w, h⟩).property

/-- The **transition factor** across an oriented edge: the change of local edge coordinates from
its source to its target. -/
noncomputable def transition (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) : kˣ :=
  localCoordinate c h / localCoordinate c h.symm

/-- The transition factor is the quotient of the local coordinates at the two ends of an edge. -/
theorem transition_def (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition c h = localCoordinate c h / localCoordinate c h.symm := (rfl)

/-- **Every ratio is a quotient of local edge coordinates.** -/
theorem ratio_eq_localCoordinate_div (c : SkewZigzagParameter k G) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    c.ratio h h' = localCoordinate c h / localCoordinate c h' := by
  rw [eq_div_iff_mul_eq']
  exact ratio_mul_ratio c h h' (reference G i ⟨j, h⟩).property

/-- **Reversing an edge inverts its transition factor.** -/
@[simp]
theorem transition_symm (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition c h.symm = (transition c h)⁻¹ := by
  rw [transition, transition, inv_div]

/-- The local coordinates of a product of parameters are the products of their local
coordinates. -/
@[simp]
theorem localCoordinate_mul (c c' : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    localCoordinate (c * c') h = localCoordinate c h * localCoordinate c' h := by
  unfold localCoordinate
  exact mul_ratio c c' _ _

/-- The transition factors of a product of parameters are the products of their transition
factors. -/
@[simp]
theorem transition_mul (c c' : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition (c * c') h = transition c h * transition c' h := by
  rw [transition_def, transition_def, transition_def, localCoordinate_mul, localCoordinate_mul,
    mul_div_mul_comm]

/-! ### Transition factors under a coefficient homomorphism -/

section Map

variable {l : Type z} [CommMonoid l]

/-- The local coordinates of a mapped parameter are the images of the local coordinates. -/
@[simp]
theorem localCoordinate_map (f : k →* l) (c : SkewZigzagParameter k G) {v w : V}
    (h : G.Adj v w) :
    localCoordinate (c.map f) h = Units.map f (localCoordinate c h) := by
  unfold localCoordinate
  exact map_ratio f c h _

/-- The transition factors of a mapped parameter are the images of the transition factors. -/
@[simp]
theorem transition_map (f : k →* l) (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    transition (c.map f) h = Units.map f (transition c h) := by
  rw [transition_def, transition_def, localCoordinate_map, localCoordinate_map, map_div]

end Map

/-! ### Transition factors along walks -/

/-- The **transition factor of a walk**: the product of the transition factors along its darts. -/
noncomputable def walkTransition (c : SkewZigzagParameter k G) {v w : V} (q : G.Walk v w) : kˣ :=
  (q.darts.map fun d ↦ transition c d.adj).prod

/-- The transition factor of a walk is the product of the transition factors along its darts. -/
theorem walkTransition_def (c : SkewZigzagParameter k G) {v w : V} (q : G.Walk v w) :
    walkTransition c q = (q.darts.map fun d ↦ transition c d.adj).prod := (rfl)

/-- The transition factor of the empty walk is one. -/
@[simp]
theorem walkTransition_nil (c : SkewZigzagParameter k G) (v : V) :
    walkTransition c (.nil : G.Walk v v) = 1 := by
  rw [walkTransition_def]
  rfl

/-- The transition factor of a one-edge walk is the transition factor of that edge. -/
@[simp]
theorem walkTransition_toWalk (c : SkewZigzagParameter k G) {v w : V} (h : G.Adj v w) :
    walkTransition c h.toWalk = transition c h := by
  simp [walkTransition, SimpleGraph.Adj.toWalk]

/-- **Extending a walk by an edge multiplies its transition factor by that of the edge.** -/
@[simp]
theorem walkTransition_concat (c : SkewZigzagParameter k G) {r v w : V} (q : G.Walk r v)
    (h : G.Adj v w) : walkTransition c (q.concat h) = walkTransition c q * transition c h := by
  simp [walkTransition]

/-- **The transition factor of a concatenation of walks is the product of theirs.** -/
@[simp]
theorem walkTransition_append (c : SkewZigzagParameter k G) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkTransition c (p.append q) = walkTransition c p * walkTransition c q := by
  simp [walkTransition]

/-- **Reversing a walk inverts its transition factor.** -/
@[simp]
theorem walkTransition_reverse (c : SkewZigzagParameter k G) {u v : V}
    (p : G.Walk u v) : walkTransition c p.reverse = (walkTransition c p)⁻¹ := by
  simp [walkTransition, Function.comp_def, List.prod_inv]

/-! ### Trivializing a parameter from a vertex potential -/

/-- The unoriented edge scale obtained from a vertex potential and the local edge coordinates. -/
private noncomputable def edgeScale (c : SkewZigzagParameter k G) (a : V → kˣ) {v w : V}
    (h : G.Adj v w) : kˣ :=
  a v * localCoordinate c h

/-- A **vertex potential** for the transition factors, a unit at every vertex changing by the
transition factor across every edge, trivializes the parameter: the resulting edge scales are
symmetric and the ratios are their quotients. -/
theorem isGaugeEquivalent_one_of_potential (c : SkewZigzagParameter k G) (a : V → kˣ)
    (ha : ∀ ⦃v w : V⦄ (h : G.Adj v w), a w = a v * transition c h) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  refine isGaugeEquivalent_one_iff_exists_ratio_eq_div.mpr
    ⟨fun _ _ h ↦ edgeScale c a h, fun _ _ h ↦ ?_, fun _ _ _ h h' ↦ ?_⟩
  · dsimp only
    rw [edgeScale, edgeScale, ha h, transition, mul_assoc, div_mul_cancel]
  · dsimp only
    rw [ratio_eq_localCoordinate_div c h h', edgeScale, edgeScale, mul_div_mul_left_eq_div]

/-! ### The potential along paths from a root -/

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
/-- A chosen path from the root of a connected component to one of its vertices. -/
private noncomputable def rootPath (v : V) : G.Walk (root G v) v :=
  (reachable_root v).exists_path_of_dist.choose

private theorem rootPath_isPath (v : V) : (rootPath G v).IsPath :=
  (reachable_root v).exists_path_of_dist.choose_spec.1

/-- The potential obtained by multiplying transition factors along the chosen path from the root
of the component of a vertex. -/
private noncomputable def potential (c : SkewZigzagParameter k G) (v : V) : kˣ :=
  walkTransition c (rootPath G v)

/-- **A parameter whose transition factor along a path depends only on its endpoints is gauge
equivalent to the constant parameter.** The transition factors along paths from a root in every
connected component form a vertex potential, which trivializes the parameter. -/
theorem isGaugeEquivalent_one_of_walkTransition_eq (c : SkewZigzagParameter k G)
    (hc : ∀ ⦃u v : V⦄ (p q : G.Walk u v), p.IsPath → q.IsPath →
      walkTransition c p = walkTransition c q) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  classical
  have hpot {r w : V} (hr : root G w = r) (q : G.Walk r w) (hq : q.IsPath) :
      potential c w = walkTransition c q := by
    subst hr
    exact hc _ _ (rootPath_isPath w) hq
  refine isGaugeEquivalent_one_of_potential c (potential c) fun v w h ↦ ?_
  by_cases hw : w ∈ (rootPath G v).support
  -- The path to `v` runs through `w`; the part after `w` has the transition factor of the edge.
  · have hsplit := congrArg (walkTransition c) ((rootPath G v).take_spec hw)
    rw [walkTransition_append,
      ← hpot (root_eq_of_adj h) _ ((rootPath_isPath v).takeUntil hw),
      hc _ h.symm.toWalk ((rootPath_isPath v).dropUntil hw) h.symm.isPath_toWalk] at hsplit
    have hedge : walkTransition c h.symm.toWalk = (transition c h)⁻¹ := by
      rw [walkTransition_toWalk, transition_symm]
    rw [hedge] at hsplit
    exact (eq_mul_inv_iff_mul_eq.mp hsplit.symm).symm
  -- Otherwise the path to `v` extended by the edge is a path to `w`.
  · rw [hpot (root_eq_of_adj h) _ ((rootPath_isPath v).concat hw h), walkTransition_concat,
      potential]

end SkewZigzagParameter

end TauCeti
