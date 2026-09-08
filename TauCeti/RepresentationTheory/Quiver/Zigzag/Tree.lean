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
# Skew-zigzag algebras of trees

A skew-zigzag parameter records ratios between backtracks along edges incident to the same vertex.
On a tree these local ratios can be integrated to a global scale on the unoriented edges: start at
a root, transport vertex normalizations along the unique paths from it, and use the resulting edge
scales to rescale one orientation of every edge. Consequently every skew-zigzag parameter on a
tree is gauge equivalent to the constant parameter, and its relation quotient is isomorphic to the
ordinary zigzag relation quotient.

## Main results

* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_of_isTree`: every skew parameter on a tree is
  gauge equivalent to the constant parameter.
* `TauCeti.nonempty_algEquiv_nonisolatedZigzagQuotient_of_isTree`: every skew-zigzag relation
  quotient of a finite tree is isomorphic to the ordinary relation quotient.
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

/-- A distinguished incident edge at every vertex of a nontrivial connected graph. -/
private noncomputable def reference (hG : G.Connected) [Nontrivial V] (v : V) :
    G.neighborSet v := by
  exact Classical.choice (G.neighborSet_nonempty.mpr (hG.preconnected.not_isIsolated v)).to_subtype

/-- The local coordinate of an incident edge relative to the distinguished edge at its source. -/
private noncomputable def localCoordinate (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] {v w : V} (h : G.Adj v w) : kˣ :=
  c.ratio h (reference hG v).property

/-- The change of local edge coordinates across an oriented edge. -/
private noncomputable def transition (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] {v w : V} (h : G.Adj v w) : kˣ :=
  localCoordinate c hG h / localCoordinate c hG h.symm

private theorem ratio_mul_ratio (c : SkewZigzagParameter k G) {i j j' j'' : V}
    (h : G.Adj i j) (h' : G.Adj i j') (h'' : G.Adj i j'') :
    c.ratio h h' * c.ratio h' h'' = c.ratio h h'' := by
  calc
    c.ratio h h' * c.ratio h' h'' = (c.ratio h'' h)⁻¹ :=
      eq_inv_of_mul_eq_one_left (c.ratio_cocycle h h' h'')
    _ = c.ratio h h'' := by
      rw [eq_inv_of_mul_eq_one_left (c.ratio_inv h'' h), inv_inv]

private theorem ratio_eq_localCoordinate_div (c : SkewZigzagParameter k G)
    (hG : G.Connected) [Nontrivial V] {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') :
    c.ratio h h' = localCoordinate c hG h / localCoordinate c hG h' := by
  rw [eq_div_iff_mul_eq']
  exact ratio_mul_ratio c h h' (reference hG i).property

@[simp]
private theorem transition_symm (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] {v w : V} (h : G.Adj v w) :
    transition c hG h.symm = (transition c hG h)⁻¹ := by
  rw [transition, transition, inv_div]

private theorem transition_arrow (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] {v w : V} (h : G.Adj v w) :
    transition c hG (arrow G h).down = transition c hG h := by
  congr <;> simp

/-- The potential obtained by multiplying transition factors along a chosen rooted walk. -/
private noncomputable def rootedPotential (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] (r : V) (p : ∀ v, G.Walk r v) (v : V) : kˣ :=
  Quiver.Path.weight
    (fun {x y : DoubledQuiver G} (e : x ⟶ y) ↦ transition c hG e.down)
    (walkToPath G (p v))

private theorem rootedPotential_mul_transition (c : SkewZigzagParameter k G)
    (hG : G.Connected) [Nontrivial V] (r : V) (p : ∀ v, G.Walk r v)
    {v w : V} (h : G.Adj v w) (hp : p w = (p v).concat h) :
    rootedPotential c hG r p w = rootedPotential c hG r p v * transition c hG h := by
  simp only [rootedPotential, hp, SimpleGraph.Walk.concat_eq_append,
    walkToPath_append, Quiver.Path.weight_comp, walkToPath_toWalk,
    Quiver.Path.weight_toPath]
  rw [transition_arrow c hG h]

/-- The unoriented edge scale obtained from a vertex potential and the local edge coordinates. -/
private noncomputable def edgeScale (c : SkewZigzagParameter k G) (hG : G.Connected)
    [Nontrivial V] (a : V → kˣ) {v w : V} (h : G.Adj v w) : kˣ :=
  a v * localCoordinate c hG h

private theorem edgeScale_symm_of_potential (c : SkewZigzagParameter k G)
    (hG : G.Connected) [Nontrivial V] (a : V → kˣ)
    (ha : ∀ {v w : V} (h : G.Adj v w), a w = a v * transition c hG h)
    {v w : V} (h : G.Adj v w) :
    edgeScale c hG a h.symm = edgeScale c hG a h := by
  rw [edgeScale, edgeScale, ha h, transition]
  simp only [div_mul_cancel, mul_assoc]

private theorem ratio_eq_edgeScale_div (c : SkewZigzagParameter k G)
    (hG : G.Connected) [Nontrivial V] (a : V → kˣ) {i j j' : V}
    (h : G.Adj i j) (h' : G.Adj i j') :
    c.ratio h h' = edgeScale c hG a h / edgeScale c hG a h' := by
  rw [ratio_eq_localCoordinate_div c hG h h', edgeScale, edgeScale,
    mul_div_mul_left_eq_div]

/-- Orient each edge away from a root and put its scale on that orientation only. -/
private noncomputable def treeLabelling (c : SkewZigzagParameter k G) (hG : G.IsTree)
    [Nontrivial V] (r : V) (a : V → kˣ) :
    ∀ ⦃x y : DoubledQuiver G⦄, (x ⟶ y) → kˣ :=
  fun ⦃x y⦄ e ↦
    if G.dist r ((vertexEquiv G).symm x) < G.dist r ((vertexEquiv G).symm y) then
      edgeScale c hG.connected a e.down
    else 1

private theorem backtrackScale_treeLabelling (c : SkewZigzagParameter k G)
    (hG : G.IsTree) [Nontrivial V] (r : V) (a : V → kˣ)
    (ha : ∀ {v w : V} (h : G.Adj v w), a w = a v * transition c hG.connected h)
    {v w : V} (h : G.Adj v w) :
    backtrackScale G (treeLabelling c hG r a) h = edgeScale c hG.connected a h := by
  rcases hG.dist_eq_dist_add_one_of_adj r h with hvw | hwv
  · rw [DoubledQuiver.backtrackScale_apply]
    unfold treeLabelling
    simp only [vertexEquiv_symm_vertex]
    rw [ite_eq_right (by omega), ite_eq_left (by omega), one_mul,
      edgeScale_symm_of_potential c hG.connected a ha h]
  · rw [DoubledQuiver.backtrackScale_apply]
    unfold treeLabelling
    simp only [vertexEquiv_symm_vertex]
    rw [ite_eq_left (by omega), ite_eq_right (by omega), mul_one]

private theorem isGaugeEquivalent_one_of_isTree_of_nontrivial
    (c : SkewZigzagParameter k G) [Nontrivial V] (hG : G.IsTree) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  let r : V := hG.connected.nonempty.some
  choose p hp hplen using hG.connected.exists_path_of_dist r
  let a : V → kˣ := rootedPotential c hG.connected r p
  have ha : ∀ {v w : V} (h : G.Adj v w), a w = a v * transition c hG.connected h := by
    intro v w h
    rcases hG.dist_eq_dist_add_one_of_adj r h with hvw | hwv
    · have hpv : p v = (p w).concat h.symm := by
        apply (hG.existsUnique_path r v).unique (hp v)
        apply SimpleGraph.Walk.isPath_of_length_eq_dist
        rw [SimpleGraph.Walk.length_concat, hplen, hvw]
      have hav := rootedPotential_mul_transition c hG.connected r p h.symm hpv
      dsimp only [a] at hav ⊢
      rw [transition_symm c hG.connected h] at hav
      rw [hav]
      simp
    · have hpw : p w = (p v).concat h := by
        apply (hG.existsUnique_path r w).unique (hp w)
        apply SimpleGraph.Walk.isPath_of_length_eq_dist
        rw [SimpleGraph.Walk.length_concat, hplen, hwv]
      exact rootedPotential_mul_transition c hG.connected r p h hpw
  apply IsGaugeEquivalent.symm
  rw [isGaugeEquivalent_iff]
  refine ⟨treeLabelling c hG r a, ?_⟩
  ext i j j' h h'
  rw [one_ratio, gauge_ratio,
    backtrackScale_treeLabelling c hG r a ha h,
    backtrackScale_treeLabelling c hG r a ha h',
    ratio_eq_edgeScale_div c hG.connected a h h']
  simp

/-- **Every skew-zigzag parameter on a tree is gauge equivalent to the constant parameter.** This
includes the one-vertex tree, where there are no incident-edge ratios to choose. -/
theorem isGaugeEquivalent_one_of_isTree (c : SkewZigzagParameter k G) (hG : G.IsTree) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k G) c := by
  classical
  cases subsingleton_or_nontrivial V with
  | inl hV =>
      let _ := hV
      have hc : c = 1 := by
        ext i j j' h
        exact (h.ne (Subsingleton.elim i j)).elim
      rw [hc]
  | inr hV =>
      let _ := hV
      exact isGaugeEquivalent_one_of_isTree_of_nontrivial c hG

end SkewZigzagParameter

/-- **Every skew-zigzag relation quotient of a finite tree is isomorphic to the ordinary zigzag
relation quotient.** The isomorphism is induced by rescaling the doubled arrows. -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_of_isTree
    (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
    (c : SkewZigzagParameter k G) (hG : G.IsTree) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] nonisolatedZigzagQuotient k G) :=
  nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one k G
    (c.isGaugeEquivalent_one_of_isTree hG)

/-- **Every skew-zigzag relation quotient of a finite nontrivial tree is isomorphic to the public
ordinary zigzag algebra.** The nontriviality assumption excludes the exceptional one-vertex
convention, where the public ordinary zigzag algebra is the dual numbers rather than the doubled
path-algebra quotient. -/
theorem nonempty_algEquiv_zigzagAlgebra_of_isTree
    (k : Type w) [CommRing k] {V : Type u} [Finite V] [Nontrivial V]
    (G : SimpleGraph V) (c : SkewZigzagParameter k G) (hG : G.IsTree) :
    Nonempty (skewZigzagQuotient k G c ≃ₐ[k] zigzagAlgebra k G) := by
  obtain ⟨e⟩ := nonempty_algEquiv_nonisolatedZigzagQuotient_of_isTree k G c hG
  exact ⟨e.trans (zigzagAlgebraEquivNonisolated k G hG.connected).symm⟩

end TauCeti
