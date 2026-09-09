/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# The exterior skew-zigzag parameter and the skew-zigzag algebras of cycles

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph by the
unit-valued ratio between the two backtracks they carry, and gauge equivalent parameters present
isomorphic algebras.  This file supplies the invariant which detects that a parameter is *not*
gauge trivial, and settles the cycles.

The invariant is the **monodromy** of a closed edge cycle: the product, over the vertices of the
cycle, of the ratio from the edge along which the cycle arrives at a vertex to the edge along
which it leaves.  A gauge transform multiplies each factor by the quotient of two backtrack
scales, and consecutive factors share those scales, so the correction telescopes around the cycle
and the monodromy depends only on the gauge class.  It is one for the constant parameter.

The **exterior** parameter of a graph in which no vertex has three pairwise distinct neighbours
gives distinct incident edges the ratio `-1`, so its relation makes the two backtracks at a vertex
sum to zero.  This is the parameter carried by the basic algebra of the exterior skew group algebra
of an odd cyclic group.  Around a cycle graph on `m` vertices its monodromy is `(-1) ^ m`, and
consequently:

* on an even cycle it is gauge equivalent to the constant parameter, the gauge being the
  alternating sign on the edges of the cycle, so it presents the ordinary zigzag algebra;
* on an odd cycle, over a coefficient ring in which `2` is not zero, it is not gauge equivalent to
  the constant parameter;
* when `2` is zero the exterior parameter *is* the constant parameter, on any graph, so the two
  presentations agree identically in characteristic two.

The odd-cycle statement is a statement about gauge classes.  Whether inequivalent classes present
nonisomorphic algebras is the separate classification question, which needs the identification of
vertex-fixing graded isomorphism classes with `H¹(G, kˣ)`.

## Main definitions

* `TauCeti.SkewZigzagParameter.monodromy`: the monodromy of a parameter around a closed edge
  cycle.
* `TauCeti.SkewZigzagParameter.exterior`: the exterior skew-zigzag parameter of a graph whose
  degrees are at most two.
* `TauCeti.SkewZigzagParameter.exteriorCycle`: the exterior parameter of a cycle graph.

## Main results

* `TauCeti.SkewZigzagParameter.monodromy_gauge`: the monodromy is a gauge invariant.
* `TauCeti.skewZigzagMk_backtrackElem_add_backtrackElem`: in the exterior relation quotient the two
  backtracks at a vertex sum to zero.
* `TauCeti.skewZigzagIdeal_exterior_eq_zigzagIdeal`: in characteristic two the exterior parameter
  presents the ordinary zigzag relations.
* `TauCeti.SkewZigzagParameter.monodromy_exteriorCycle`: the monodromy of the exterior parameter
  around a cycle graph on `m` vertices is `(-1) ^ m`.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_exteriorCycle` and
  `TauCeti.nonempty_algEquiv_zigzagAlgebra_exteriorCycle`: on an even cycle the exterior parameter
  is gauge trivial, and therefore presents the ordinary zigzag algebra.
* `TauCeti.SkewZigzagParameter.not_isGaugeEquivalent_one_exteriorCycle`: on an odd cycle, over a
  ring in which `2` is not zero, it is not gauge trivial.

## References

C. Couture, *Skew-Zigzag Algebras*, Sections 3 and 4, https://arxiv.org/abs/1509.08405, for the
gauge relation on skew parameters and its cohomological classification.

S. Huerfano and M. Khovanov, *A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060, for the skew-zigzag relations of the cycles and the exterior
skew group algebras they match.
-/

public section

namespace TauCeti

open DoubledQuiver SimpleGraph

universe u w

namespace SkewZigzagParameter

/-! ### The monodromy of a closed edge cycle -/

section Monodromy

variable {k : Type w} [CommMonoid k] {V : Type u} {G : SimpleGraph V} {m : ℕ} [NeZero m]
  {x : Fin m → V}

/-- The **monodromy** of a skew-zigzag parameter around a closed edge cycle `x`, a cyclically
indexed family of vertices consecutive ones of which are adjacent: the product, over the vertices
of the cycle, of the ratio from the edge along which the cycle arrives at a vertex to the edge
along which it leaves.  It is unchanged by a gauge transform and is one for the constant
parameter, so it obstructs gauge triviality. -/
def monodromy (c : SkewZigzagParameter k G) (hx : ∀ i : Fin m, G.Adj (x i) (x (i + 1))) : kˣ :=
  ∏ i : Fin m, c.ratio (hx i).symm (hx (i + 1))

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

end Monodromy

/-! ### The exterior parameter -/

section Exterior

variable (k : Type w) [CommRing k] {V : Type u} [DecidableEq V] {G : SimpleGraph V}
  (hG : ∀ ⦃i j j' j'' : V⦄, G.Adj i j → G.Adj i j' → G.Adj i j'' → j = j' ∨ j' = j'' ∨ j'' = j)

/-- The two signs comparing a pair of neighbours in either order cancel. -/
private theorem exteriorSign_mul_exteriorSign (a b : V) :
    (if a = b then (1 : kˣ) else -1) * (if b = a then 1 else -1) = 1 := by
  rcases eq_or_ne a b with rfl | hne
  · rw [ite_eq_left rfl, one_mul]
  · rw [ite_eq_right hne, ite_eq_right hne.symm, neg_mul_neg, one_mul]

/-- The **exterior skew-zigzag parameter** of a graph no vertex of which has three pairwise
distinct neighbours, that is, of a graph all of whose degrees are at most two: the ratio between
the backtracks along two distinct incident edges is `-1`, so the relation it imposes makes the two
backtracks at a vertex sum to zero.  The degree hypothesis is what makes the ratios a cocycle: at
a vertex with three pairwise distinct neighbours the three signs would multiply to `-1`.

The odd cycles are the McKay graphs of the odd cyclic subgroups of `SU(2)`, and it is this
relation, rather than the ordinary one, that the exterior skew group algebras of those subgroups
carry. -/
def exterior : SkewZigzagParameter k G where
  ratio _ j j' _ _ := if j = j' then 1 else -1
  ratio_self := by intro i j h; exact ite_eq_left rfl
  ratio_inv := by
    intro i j j' h h'
    exact exteriorSign_mul_exteriorSign k j j'
  ratio_cocycle := by
    intro i j j' j'' h h' h''
    rcases hG h h' h'' with rfl | rfl | rfl
    · rw [ite_eq_left rfl, one_mul, exteriorSign_mul_exteriorSign]
    · rw [ite_eq_left rfl, mul_one, exteriorSign_mul_exteriorSign]
    · rw [ite_eq_left rfl, mul_one, exteriorSign_mul_exteriorSign]

variable {k}

/-- **The exterior ratio of two distinct incident edges is minus one.** -/
theorem exterior_ratio_of_ne {i j j' : V} (h : G.Adj i j) (h' : G.Adj i j') (hne : j ≠ j') :
    (exterior k hG).ratio h h' = -1 :=
  ite_eq_right hne

/-- **In characteristic two the exterior parameter is the constant parameter.** The sign
distinguishing the two backtracks at a vertex collapses, so the exterior and the ordinary zigzag
presentations agree identically. -/
theorem exterior_eq_one (h2 : (2 : k) = 0) : exterior k hG = 1 := by
  have hneg : (-1 : kˣ) = 1 :=
    Units.ext (by rw [Units.val_neg, Units.val_one]; linear_combination -h2)
  ext i j j' h h'
  rw [← Units.ext_iff]
  rcases eq_or_ne j j' with rfl | hne
  · rw [one_ratio]
    exact (exterior k hG).ratio_self h
  · rw [exterior_ratio_of_ne hG h h' hne, one_ratio, hneg]

end Exterior

end SkewZigzagParameter

section ExteriorRelations

variable (k : Type w) [CommRing k] {V : Type u} [DecidableEq V] [Finite V] (G : SimpleGraph V)
  (hG : ∀ ⦃i j j' j'' : V⦄, G.Adj i j → G.Adj i j' → G.Adj i j'' → j = j' ∨ j' = j'' ∨ j'' = j)

/-- **In the exterior relation quotient the two backtracks at a vertex sum to zero.** This is the
shape in which the exterior relation appears for the basic algebra of an exterior skew group
algebra. -/
theorem skewZigzagMk_backtrackElem_add_backtrackElem {i j j' : V} (h : G.Adj i j)
    (h' : G.Adj i j') (hne : j ≠ j') :
    skewZigzagMk k G (SkewZigzagParameter.exterior k hG) (backtrackElem G k h) +
        skewZigzagMk k G (SkewZigzagParameter.exterior k hG) (backtrackElem G k h') = 0 := by
  rw [skewZigzagMk_backtrackElem_eq_smul k G _ h h',
    SkewZigzagParameter.exterior_ratio_of_ne hG h h' hne, Units.val_neg, Units.val_one,
    neg_one_smul, neg_add_cancel]

/-- **In characteristic two the exterior parameter presents the ordinary zigzag relations.** -/
theorem skewZigzagIdeal_exterior_eq_zigzagIdeal (h2 : (2 : k) = 0) :
    skewZigzagIdeal k G (SkewZigzagParameter.exterior k hG) = zigzagIdeal k G := by
  rw [SkewZigzagParameter.exterior_eq_one hG h2, skewZigzagIdeal_one_eq_zigzagIdeal]

end ExteriorRelations

/-! ### Cycle graphs -/

section CycleGraph

variable {m : ℕ} [NeZero m]

/-- **Adjacent vertices of a cycle graph differ by one.** -/
theorem eq_add_one_or_eq_add_one_of_cycleGraph_adj {u v : Fin m} (h : (cycleGraph m).Adj u v) :
    v = u + 1 ∨ u = v + 1 := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by have := NeZero.ne m; omega⟩
  obtain _ | n := n
  · exact absurd h cycleGraph_one_adj
  · rcases cycleGraph_adj.mp h with hd | hd
    · exact Or.inr ((sub_eq_iff_eq_add.mp hd).trans (add_comm 1 v))
    · exact Or.inl ((sub_eq_iff_eq_add.mp hd).trans (add_comm 1 u))

/-- **No vertex of a cycle graph has three pairwise distinct neighbours**: every degree is at most
two. -/
theorem cycleGraph_eq_or_eq_or_eq_of_adj {i j j' j'' : Fin m} (h : (cycleGraph m).Adj i j)
    (h' : (cycleGraph m).Adj i j') (h'' : (cycleGraph m).Adj i j'') :
    j = j' ∨ j' = j'' ∨ j'' = j := by
  rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h with hj | hj <;>
    rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h' with hj' | hj' <;>
      rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h'' with hj'' | hj''
  · exact Or.inl (hj.trans hj'.symm)
  · exact Or.inl (hj.trans hj'.symm)
  · exact Or.inr (Or.inr (hj''.trans hj.symm))
  · exact Or.inr (Or.inl (add_right_cancel (hj'.symm.trans hj'')))
  · exact Or.inr (Or.inl (hj'.trans hj''.symm))
  · exact Or.inr (Or.inr (add_right_cancel (hj''.symm.trans hj)))
  · exact Or.inl (add_right_cancel (hj.symm.trans hj'))
  · exact Or.inl (add_right_cancel (hj.symm.trans hj'))

/-- **Consecutive vertices of a cycle graph on at least three vertices are adjacent.** -/
theorem cycleGraph_adj_add_one (hm : 3 ≤ m) (v : Fin m) : (cycleGraph m).Adj v (v + 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  exact cycleGraph_adj.mpr (Or.inr (add_sub_cancel_left v 1))

/-- The underlying natural number of a successor in `Fin m`. -/
private theorem val_add_one (v : Fin m) : ((v + 1 : Fin m) : ℕ) = (v.val + 1) % m := by
  rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]

private theorem one_add_one_ne_zero (hm : 3 ≤ m) : (1 : Fin m) + 1 ≠ 0 := by
  have h1 : ((1 : Fin m) : ℕ) = 1 := by rw [Fin.val_one', Nat.mod_eq_of_lt (by omega)]
  rw [Ne, Fin.ext_iff, val_add_one, h1, Fin.val_zero, Nat.mod_eq_of_lt (by omega)]
  omega

/-- **Adding one twice in `Fin m` never returns to the same element** when `3 ≤ m`.  For a cycle
graph this says that the two neighbours of a vertex are distinct. -/
theorem add_one_add_one_ne_self (hm : 3 ≤ m) (v : Fin m) : v + 1 + 1 ≠ v := by
  intro h
  refine one_add_one_ne_zero hm (add_left_cancel (a := v) ?_)
  rw [add_zero, ← add_assoc, h]

end CycleGraph

namespace SkewZigzagParameter

/-! ### The exterior parameter of a cycle -/

section ExteriorCycle

variable (k : Type w) [CommRing k] (m : ℕ) [NeZero m]

/-- The **exterior skew-zigzag parameter of a cycle graph**: the two backtracks at a vertex of the
cycle sum to zero.  On an odd cycle over a field of characteristic other than two this is the
nontrivial skew class; on an even cycle it is gauge equivalent to the constant parameter. -/
def exteriorCycle : SkewZigzagParameter k (cycleGraph m) :=
  exterior k fun _ _ _ _ h h' h'' => cycleGraph_eq_or_eq_or_eq_of_adj h h' h''

variable {k m}

/-- **The exterior ratio of the two distinct edges at a vertex of a cycle is minus one.** -/
theorem exteriorCycle_ratio_of_ne {i j j' : Fin m} (h : (cycleGraph m).Adj i j)
    (h' : (cycleGraph m).Adj i j') (hne : j ≠ j') : (exteriorCycle k m).ratio h h' = -1 :=
  exterior_ratio_of_ne _ h h' hne

/-- **In characteristic two the exterior parameter of a cycle is the constant parameter.** -/
theorem exteriorCycle_eq_one (h2 : (2 : k) = 0) : exteriorCycle k m = 1 :=
  exterior_eq_one _ h2

/-- **The monodromy of the exterior parameter around a cycle graph on `m` vertices is
`(-1) ^ m`.** Every one of the `m` vertices contributes the sign between its two distinct
incident edges. -/
theorem monodromy_exteriorCycle (hm : 3 ≤ m) :
    monodromy (exteriorCycle k m) (cycleGraph_adj_add_one hm) = (-1 : kˣ) ^ m := by
  rw [monodromy, Finset.prod_congr rfl fun i _ =>
    exteriorCycle_ratio_of_ne (k := k) _ _ (add_one_add_one_ne_self hm i).symm,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The alternating sign on the edges of a cycle graph, carried by the arrow which increases the
vertex index. -/
private def cycleLabelling (k : Type w) [CommRing k] (m : ℕ) [NeZero m] :
    ∀ ⦃y z : DoubledQuiver (cycleGraph m)⦄, (y ⟶ z) → kˣ :=
  fun ⦃y z⦄ _ =>
    if (vertexEquiv (cycleGraph m)).symm z = (vertexEquiv (cycleGraph m)).symm y + 1 then
      (-1 : kˣ) ^ (((vertexEquiv (cycleGraph m)).symm y : Fin m) : ℕ)
    else 1

private theorem backtrackScale_cycleLabelling (hm : 3 ≤ m) (v : Fin m)
    (hv : (cycleGraph m).Adj v (v + 1)) :
    backtrackScale (cycleGraph m) (cycleLabelling k m) hv = (-1 : kˣ) ^ (v : ℕ) := by
  rw [backtrackScale_apply]
  unfold cycleLabelling
  simp only [vertexEquiv_symm_vertex]
  rw [ite_eq_left trivial, ite_eq_right (add_one_add_one_ne_self hm v).symm, mul_one]

private theorem neg_one_pow_val_add_one (hev : Even m) (v : Fin m) :
    (-1 : kˣ) ^ ((v + 1 : Fin m) : ℕ) = -((-1 : kˣ) ^ (v : ℕ)) := by
  rw [val_add_one]
  rcases Nat.lt_or_ge (v.val + 1) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_succ, mul_neg_one]
  · have hv : v.val + 1 = m := by have := v.isLt; omega
    have hev' : Even (v.val + 1) := by rw [hv]; exact hev
    have hodd : Odd v.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev')
    rw [hv, Nat.mod_self, pow_zero, hodd.neg_one_pow, neg_neg]

/-- **On an even cycle the exterior parameter is gauge equivalent to the constant parameter**, and
so presents the ordinary zigzag relations.  The gauge is the alternating sign on the edges of the
cycle, which closes up exactly because the number of vertices is even. -/
theorem isGaugeEquivalent_one_exteriorCycle (hm : 3 ≤ m) (hev : Even m) :
    IsGaugeEquivalent (1 : SkewZigzagParameter k (cycleGraph m)) (exteriorCycle k m) := by
  rw [isGaugeEquivalent_iff]
  refine ⟨cycleLabelling k m, ?_⟩
  ext v j j' h h'
  rw [← Units.ext_iff, gauge_ratio, one_ratio, one_mul]
  rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h with hj | hv <;>
    rcases eq_add_one_or_eq_add_one_of_cycleGraph_adj h' with hj' | hv'
  · subst hj
    subst hj'
    exact ((exteriorCycle k m).ratio_self h).trans (div_self' _).symm
  · subst hj
    subst hv'
    have hS : backtrackScale (cycleGraph m) (cycleLabelling k m) h = -((-1 : kˣ) ^ (j' : ℕ)) := by
      rw [backtrackScale_cycleLabelling hm _ h, neg_one_pow_val_add_one hev]
    have hS' : backtrackScale (cycleGraph m) (cycleLabelling k m) h' = (-1 : kˣ) ^ (j' : ℕ) := by
      rw [← backtrackScale_symm (cycleGraph m) (cycleLabelling k m) h',
        backtrackScale_cycleLabelling hm _ h'.symm]
    rw [exteriorCycle_ratio_of_ne h h' (add_one_add_one_ne_self hm j'), hS, hS',
      eq_div_iff_mul_eq', neg_one_mul, neg_neg]
  · subst hv
    subst hj'
    have hS : backtrackScale (cycleGraph m) (cycleLabelling k m) h = (-1 : kˣ) ^ (j : ℕ) := by
      rw [← backtrackScale_symm (cycleGraph m) (cycleLabelling k m) h,
        backtrackScale_cycleLabelling hm _ h.symm]
    have hS' : backtrackScale (cycleGraph m) (cycleLabelling k m) h' = -((-1 : kˣ) ^ (j : ℕ)) := by
      rw [backtrackScale_cycleLabelling hm _ h', neg_one_pow_val_add_one hev]
    rw [exteriorCycle_ratio_of_ne h h' (add_one_add_one_ne_self hm j).symm, hS, hS',
      eq_div_iff_mul_eq', neg_one_mul]
  · subst hv
    have hjj : j = j' := add_right_cancel hv'
    subst hjj
    exact ((exteriorCycle k m).ratio_self h).trans (div_self' _).symm

/-- **On an odd cycle, over a coefficient ring in which `2` is not zero, the exterior parameter is
not gauge equivalent to the constant parameter**: its monodromy around the cycle is `-1`.  For a
field this is the hypothesis that the characteristic is not two. -/
theorem not_isGaugeEquivalent_one_exteriorCycle (hm : 3 ≤ m) (hodd : Odd m) (h2 : (2 : k) ≠ 0) :
    ¬ IsGaugeEquivalent (1 : SkewZigzagParameter k (cycleGraph m)) (exteriorCycle k m) := by
  intro hgauge
  refine h2 ?_
  have hone : (-1 : kˣ) = 1 := by
    rw [← hodd.neg_one_pow, ← monodromy_exteriorCycle (k := k) hm]
    exact monodromy_eq_one_of_isGaugeEquivalent_one hgauge _
  have := congrArg (Units.val (α := k)) hone
  rw [Units.val_neg, Units.val_one] at this
  linear_combination -this

end ExteriorCycle

end SkewZigzagParameter

section ExteriorCycleAlgebra

variable (k : Type w) [CommRing k] (m : ℕ) [NeZero m]

/-- **On an even cycle the exterior skew-zigzag relation quotient is the ordinary zigzag relation
quotient.** -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_exteriorCycle (hm : 3 ≤ m) (hev : Even m) :
    Nonempty (skewZigzagQuotient k (cycleGraph m) (SkewZigzagParameter.exteriorCycle k m) ≃ₐ[k]
      nonisolatedZigzagQuotient k (cycleGraph m)) :=
  nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one k (cycleGraph m)
    (SkewZigzagParameter.isGaugeEquivalent_one_exteriorCycle hm hev)

/-- **On an even cycle the exterior skew-zigzag algebra is the public zigzag algebra.** -/
theorem nonempty_algEquiv_zigzagAlgebra_exteriorCycle (hm : 3 ≤ m) (hev : Even m) :
    Nonempty (skewZigzagQuotient k (cycleGraph m) (SkewZigzagParameter.exteriorCycle k m) ≃ₐ[k]
      zigzagAlgebra k (cycleGraph m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨e⟩ := nonempty_algEquiv_nonisolatedZigzagQuotient_exteriorCycle k m hm hev
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact ⟨e.trans (zigzagAlgebraEquivNonisolated k _ cycleGraph_connected).symm⟩

end ExteriorCycleAlgebra

end TauCeti
