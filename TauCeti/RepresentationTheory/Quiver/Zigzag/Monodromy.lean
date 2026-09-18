/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Combinatorics.SimpleGraph.Acyclic

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# The monodromy of a skew-zigzag parameter around a closed edge cycle

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph by the
unit-valued ratio between the two backtracks they carry, and gauge equivalent parameters present
isomorphic algebras. This file supplies a complete invariant of gauge equivalence.

The invariant is the **monodromy** of a closed edge cycle: the product, over the vertices of the
cycle, of the ratio from the edge along which the cycle arrives at a vertex to the edge along
which it leaves.  A gauge transform multiplies each factor by the quotient of two backtrack
scales, and consecutive factors share those scales, so the correction telescopes around the cycle
and the monodromy depends only on the gauge class. Conversely, trivial monodromy makes the
transition factors between local edge coordinates integrate to a vertex potential, which
trivializes the parameter. Thus two parameters are gauge equivalent exactly when all their
monodromies agree.

## Main definitions

* `TauCeti.SkewZigzagParameter.monodromy`: the monodromy of a parameter around a closed edge
  cycle.

## Main results

* `TauCeti.SkewZigzagParameter.monodromy_def`: the defining product for monodromy.
* `TauCeti.SkewZigzagParameter.monodromy_rotate`: changing the starting vertex does not change
  monodromy.
* `TauCeti.SkewZigzagParameter.monodromy_reverse`: reversing orientation inverts monodromy.
* `TauCeti.SkewZigzagParameter.monodromy_gauge`: the monodromy is a gauge invariant.
* `TauCeti.SkewZigzagParameter.monodromy_eq_one_of_isGaugeEquivalent_one`: a gauge-trivial
  parameter has trivial monodromy.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_iff_monodromy_eq_one`: a skew parameter is
  gauge trivial exactly when its monodromy around every closed edge cycle is one.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_iff_monodromy_eq`: two skew parameters are gauge
  equivalent exactly when their monodromies around every closed edge cycle agree.

## References

C. Couture, *Skew-Zigzag Algebras*, Section 4, https://arxiv.org/abs/1509.08405, for the gauge
relation on skew parameters and its cohomological classification.
-/

public section

namespace TauCeti

open DoubledQuiver SimpleGraph

universe u w

namespace SkewZigzagParameter

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V} {m : ℕ} [NeZero m]
  {x : Fin m → V}

/-- The **monodromy** of a skew-zigzag parameter around a closed edge cycle `x`, a cyclically
indexed family of vertices consecutive ones of which are adjacent: the product, over the vertices
of the cycle, of the ratio from the edge along which the cycle arrives at a vertex to the edge
along which it leaves.  It is unchanged by a gauge transform and is one for the constant
parameter, so it obstructs gauge triviality. -/
def monodromy (c : SkewZigzagParameter k G) (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) : kˣ :=
  ∏ i : Fin m, c.ratio (hx i).symm (hx (i + 1))

/-- **The monodromy is the product, over the vertices of the cycle, of the ratio between the
edge along which the cycle arrives and the edge along which it leaves.** -/
theorem monodromy_def (c : SkewZigzagParameter k G)
    (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) :
    monodromy c hx = ∏ i : Fin m, c.ratio (hx i).symm (hx (i + 1)) := (rfl)

/-- **Changing the starting vertex of a closed edge cycle does not change its monodromy.** -/
theorem monodromy_rotate (c : SkewZigzagParameter k G)
    (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) (n : Fin m) :
    monodromy (x := fun i => x (i + n)) c (fun i => by
      simpa only [add_assoc, add_comm, add_left_comm] using hx (i + n)) = monodromy c hx := by
  unfold monodromy
  exact Fintype.prod_equiv (Equiv.addRight n) _ _ fun i => by
    -- Reindexing changes the endpoints definitionally but leaves different adjacency proofs.
    change c.ratio _ _ = c.ratio (hx (i + n)).symm (hx (i + n + 1))
    congr 1
    all_goals
      apply congrArg x
      abel_nf

/-- **Reversing the orientation of a closed edge cycle inverts its monodromy.** -/
theorem monodromy_reverse (c : SkewZigzagParameter k G)
    (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) :
    monodromy (x := fun i => x (-i)) c (fun i => by
      convert (hx (-i - 1)).symm using 1 <;> congr 1 <;> abel) =
      (monodromy c hx)⁻¹ := by
  unfold monodromy
  rw [← Finset.prod_inv_distrib]
  let e : Fin m ≃ Fin m :=
    { toFun := fun i => -i - 1 - 1
      invFun := fun i => -i - 1 - 1
      left_inv := by intro i; dsimp; abel
      right_inv := by intro i; dsimp; abel }
  exact Fintype.prod_equiv e _ _ fun i => by
    -- Align the reversed edge proofs with the original ratio in the opposite order.
    change c.ratio _ _ = (c.ratio (hx (-i - 1 - 1)).symm (hx (-i - 1 - 1 + 1)))⁻¹
    apply eq_inv_of_mul_eq_one_right
    convert c.ratio_inv (hx (-i - 1 - 1)).symm (hx (-i - 1 - 1 + 1)) using 1
    congr 1
    all_goals congr 1
    all_goals
      apply congrArg x
      abel

/-- **The constant parameter has trivial monodromy.** -/
@[simp]
theorem monodromy_one (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) :
    monodromy (1 : SkewZigzagParameter k G) hx = 1 :=
  Finset.prod_eq_one fun _ _ => one_ratio _ _

/-- **The monodromy is a gauge invariant**: the backtrack scales a gauge transform contributes at
a vertex of the cycle cancel against those it contributes at the neighbouring vertices. -/
@[simp]
theorem monodromy_gauge (c : SkewZigzagParameter k G)
    (u : ∀ ⦃y z : DoubledQuiver G⦄, (y ⟶ z) → kˣ)
    (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) :
    monodromy (c.gauge u) hx = monodromy c hx := by
  have hshift : ∏ i : Fin m, backtrackScale G u (hx (i + 1)) =
      ∏ i : Fin m, backtrackScale G u (hx i).symm :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ fun i =>
      (backtrackScale_symm G u (hx (i + 1))).symm
  simp only [monodromy, gauge_ratio]
  rw [Finset.prod_mul_distrib, Finset.prod_div_distrib, hshift, div_self', mul_one]

/-- **Gauge equivalent parameters have the same monodromy.** -/
theorem monodromy_eq_of_isGaugeEquivalent {c c' : SkewZigzagParameter k G}
    (hc : c.IsGaugeEquivalent c') (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) :
    monodromy c hx = monodromy c' hx := by
  obtain ⟨u, rfl⟩ := isGaugeEquivalent_iff.mp hc
  rw [monodromy_gauge]

/-- **A gauge-trivial parameter has trivial monodromy around every closed edge cycle.** -/
theorem monodromy_eq_one_of_isGaugeEquivalent_one {c : SkewZigzagParameter k G}
    (hc : IsGaugeEquivalent (1 : SkewZigzagParameter k G) c)
    (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) : monodromy c hx = 1 := by
  rw [← monodromy_eq_of_isGaugeEquivalent hc hx, monodromy_one]

/-! ### Integrating transition factors -/

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

/-- A transition factor depends only on the endpoints of its edge. -/
private theorem transition_congr (c : SkewZigzagParameter k G) {v w v' w' : V} (h : G.Adj v w)
    (h' : G.Adj v' w') (hv : v = v') (hw : w = w') : transition c h = transition c h' := by
  subst hv hw
  rfl

/-- The product of the transition factors along the darts of a walk. -/
private noncomputable def walkTransition (c : SkewZigzagParameter k G) {v w : V}
    (q : G.Walk v w) : kˣ :=
  (q.darts.map fun d ↦ transition c d.adj).prod

private theorem walkTransition_concat (c : SkewZigzagParameter k G) {r v w : V} (q : G.Walk r v)
    (h : G.Adj v w) : walkTransition c (q.concat h) = walkTransition c q * transition c h := by
  simp [walkTransition]

private theorem walkTransition_append (c : SkewZigzagParameter k G) {u v w : V}
    (p : G.Walk u v) (q : G.Walk v w) :
    walkTransition c (p.append q) = walkTransition c p * walkTransition c q := by
  simp [walkTransition]

private theorem walkTransition_reverse (c : SkewZigzagParameter k G) {u v : V}
    (p : G.Walk u v) : walkTransition c p.reverse = (walkTransition c p)⁻¹ := by
  simp [walkTransition, Function.comp_def, List.prod_inv]

/-- The unoriented edge scale obtained from a vertex potential and the local edge coordinates. -/
private noncomputable def edgeScale (c : SkewZigzagParameter k G) (a : V → kˣ) {v w : V}
    (h : G.Adj v w) : kˣ :=
  a v * localCoordinate c h

/-- A vertex potential for the transition factors trivializes the parameter. -/
private theorem isGaugeEquivalent_one_of_potential (c : SkewZigzagParameter k G) (a : V → kˣ)
    (ha : ∀ ⦃v w : V⦄ (h : G.Adj v w), a w = a v * transition c h) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  refine isGaugeEquivalent_one_iff_exists_ratio_eq_div.mpr
    ⟨fun _ _ h ↦ edgeScale c a h, fun _ _ h ↦ ?_, fun _ _ _ h h' ↦ ?_⟩
  · dsimp only
    rw [edgeScale, edgeScale, ha h, transition, mul_assoc, div_mul_cancel]
  · dsimp only
    rw [ratio_eq_localCoordinate_div c h h', edgeScale, edgeScale, mul_div_mul_left_eq_div]

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
/-- A shortest path from the chosen root of a connected component to one of its vertices. -/
private noncomputable def rootPath (v : V) : G.Walk (root G v) v :=
  (reachable_root v).exists_path_of_dist.choose

/-- The potential obtained by multiplying transition factors along a chosen path from the root of
the component of a vertex. -/
private noncomputable def potential (c : SkewZigzagParameter k G) (v : V) : kˣ :=
  walkTransition c (rootPath G v)

/-! ### Trivial monodromy -/

/-- Around a closed edge cycle, the transition factors multiply to the inverse of the monodromy. -/
private theorem prod_transition_eq_inv_monodromy (c : SkewZigzagParameter k G) {n : ℕ}
    [NeZero n] {y : Fin n → V} (hy : ∀ i : Fin n, G.Adj (y i) (y (i + 1))) :
    ∏ i, transition c (hy i) = (monodromy c hy)⁻¹ := by
  have hshift : ∏ i : Fin n, localCoordinate c (hy (i + 1)) = ∏ i, localCoordinate c (hy i) :=
    Fintype.prod_equiv (Equiv.addRight 1) _ _ fun _ ↦ rfl
  simp only [monodromy_def, transition, ratio_eq_localCoordinate_div c, Finset.prod_div_distrib,
    hshift, inv_div]

/-- Cyclic indexing of the vertices of a closed walk agrees with ordinary indexing one step past
every position. -/
private theorem getVert_val_add_one {u : V} (q : G.Walk u u) [NeZero q.length]
    (i : Fin q.length) : q.getVert ↑(i + 1) = q.getVert (↑i + 1) := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  have hi : (i : ℕ) + 1 ≤ q.length := by omega
  rcases hi.lt_or_eq with hlt | heq
  · rw [Nat.mod_eq_of_lt hlt]
  · rw [heq, Nat.mod_self, SimpleGraph.Walk.getVert_zero, SimpleGraph.Walk.getVert_length]

/-- The vertices of a closed walk of positive length, indexed cyclically, form a closed edge
cycle. -/
private theorem adj_getVert_add_one {u : V} (q : G.Walk u u) [NeZero q.length]
    (i : Fin q.length) : G.Adj (q.getVert i) (q.getVert ↑(i + 1)) := by
  rw [getVert_val_add_one]
  exact q.adj_getVert_succ i.isLt

/-- Along a closed walk, the transition factors multiply to one when the monodromy around every
closed edge cycle is trivial. -/
private theorem walkTransition_eq_one_of_monodromy_eq_one (c : SkewZigzagParameter k G)
    (hc : ∀ (n : ℕ) [NeZero n] (y : Fin n → V) (hy : ∀ i : Fin n, G.Adj (y i) (y (i + 1))),
      monodromy c hy = 1)
    {u : V} (q : G.Walk u u) : walkTransition c q = 1 := by
  rcases Nat.eq_zero_or_pos q.length with hq | hq
  · rw [walkTransition, List.eq_nil_of_length_eq_zero (q.length_darts.trans hq)]
    rfl
  have : NeZero q.length := ⟨hq.ne'⟩
  have hprod : walkTransition c q = ∏ i, transition c (adj_getVert_add_one q i) := by
    rw [walkTransition, ← List.ofFn_getElem_eq_map, List.prod_ofFn,
      ← Fin.prod_congr' _ q.length_darts]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    have hd := SimpleGraph.Walk.darts_getElem_eq_getVert (p := q) i i.isLt
    exact transition_congr c _ _ (by rw [hd]; rfl) (by rw [hd, getVert_val_add_one, Fin.val_cast])
  rw [hprod, prod_transition_eq_inv_monodromy, hc, inv_one]

/-- **A skew-zigzag parameter is gauge trivial exactly when its monodromy around every closed edge
cycle is one.** This is the converse of `monodromy_eq_one_of_isGaugeEquivalent_one`, and holds on
every graph, including disconnected graphs and graphs with isolated vertices. -/
theorem isGaugeEquivalent_one_iff_monodromy_eq_one {c : SkewZigzagParameter k G} :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c ↔
      ∀ (n : ℕ) [NeZero n] (y : Fin n → V) (hy : ∀ i : Fin n, G.Adj (y i) (y (i + 1))),
        monodromy c hy = 1 := by
  refine ⟨fun h _ _ _ hy ↦ monodromy_eq_one_of_isGaugeEquivalent_one h hy, fun hc ↦ ?_⟩
  have hwalk {r v : V} (p q : G.Walk r v) : walkTransition c p = walkTransition c q := by
    have h := walkTransition_eq_one_of_monodromy_eq_one c hc (p.append q.reverse)
    rwa [walkTransition_append, walkTransition_reverse, mul_inv_eq_one] at h
  have hroot {r w : V} (hr : root G w = r) (q : G.Walk r w) :
      potential c w = walkTransition c q := by
    subst hr
    exact hwalk _ _
  refine isGaugeEquivalent_one_of_potential c (potential c) fun v w h ↦ ?_
  rw [hroot (root_eq_of_adj h) ((rootPath G v).concat h), walkTransition_concat, potential]

/-- The parameter whose ratios are those of `c'` divided by those of `c`. -/
private def ratioDiv (c c' : SkewZigzagParameter k G) : SkewZigzagParameter k G where
  ratio _ _ _ h h' := c'.ratio h h' / c.ratio h h'
  ratio_self _ _ h := by simp
  ratio_inv _ _ _ h h' := by rw [div_mul_div_comm, c'.ratio_inv, c.ratio_inv, div_one]
  ratio_cocycle _ _ _ _ h h' h'' := by
    rw [div_mul_div_comm, div_mul_div_comm, c'.ratio_cocycle, c.ratio_cocycle, div_one]

private theorem ratioDiv_ratio (c c' : SkewZigzagParameter k G) {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') : (ratioDiv c c').ratio h h' = c'.ratio h h' / c.ratio h h' := (rfl)

private theorem isGaugeEquivalent_iff_isGaugeEquivalent_one_ratioDiv
    {c c' : SkewZigzagParameter k G} :
    c.IsGaugeEquivalent c' ↔ IsGaugeEquivalent 1 (ratioDiv c c') := by
  rw [isGaugeEquivalent_iff, isGaugeEquivalent_iff]
  refine exists_congr fun u ↦ ?_
  simp only [SkewZigzagParameter.ext_iff, funext_iff, gauge_ratio, one_ratio, one_mul,
    ratioDiv_ratio, div_eq_iff_eq_mul']

/-- **The monodromy is a complete gauge invariant**: two skew-zigzag parameters are gauge
equivalent exactly when they have the same monodromy around every closed edge cycle. -/
theorem isGaugeEquivalent_iff_monodromy_eq {c c' : SkewZigzagParameter k G} :
    c.IsGaugeEquivalent c' ↔
      ∀ (n : ℕ) [NeZero n] (y : Fin n → V) (hy : ∀ i : Fin n, G.Adj (y i) (y (i + 1))),
        monodromy c hy = monodromy c' hy := by
  rw [isGaugeEquivalent_iff_isGaugeEquivalent_one_ratioDiv,
    isGaugeEquivalent_one_iff_monodromy_eq_one]
  refine forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦ forall_congr' fun hy ↦ ?_
  simp only [monodromy_def, ratioDiv_ratio, Finset.prod_div_distrib]
  rw [div_eq_one, eq_comm]

end SkewZigzagParameter

end TauCeti
