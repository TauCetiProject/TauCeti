/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.SimpleGraph.CycleGraph
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Componentwise
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Exterior
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Monodromy

/-!
# The skew-zigzag algebras of the cycles

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph by the
unit-valued ratio between the two backtracks they carry, and gauge equivalent parameters present
isomorphic algebras.  This file settles the cycles, the invariant detecting that a parameter is
*not* gauge trivial being the monodromy around a closed edge cycle.

Around a cycle graph on `m ≥ 3` vertices the monodromy of the exterior parameter is `(-1) ^ m`,
and consequently:

* on an even cycle with at least three vertices it is gauge equivalent to the constant parameter,
  the gauge being the alternating sign on the edges of the cycle, so it presents the ordinary
  zigzag algebra;
* on an odd cycle with at least three vertices, over a coefficient ring in which `2` is not zero,
  it is not gauge equivalent to the constant parameter.

In characteristic two the exterior parameter *is* the constant parameter, on any graph, so the two
presentations agree identically by `TauCeti.SkewZigzagParameter.exterior_eq_one`.

The odd-cycle statement is a statement about gauge classes.  Whether inequivalent classes present
nonisomorphic algebras is the separate classification question, which needs the identification of
vertex-fixing graded isomorphism classes with `H¹(G, kˣ)`.

## Main definitions

* `TauCeti.SkewZigzagParameter.exteriorCycle`: the exterior parameter of a cycle graph.

## Main results

* `TauCeti.SkewZigzagParameter.exteriorCycle_ratio`: the exterior ratio of two incident edges of
  a cycle graph is one when they agree and minus one otherwise.
* `TauCeti.SkewZigzagParameter.monodromy_exteriorCycle`: the monodromy of the exterior parameter
  around a cycle graph on `m ≥ 3` vertices is `(-1) ^ m`.
* `TauCeti.SkewZigzagParameter.isGaugeEquivalent_one_exteriorCycle` and
  `TauCeti.nonempty_algEquiv_zigzagAlgebra_exteriorCycle`: on an even cycle with at least three
  vertices the exterior parameter is gauge trivial, and therefore presents the ordinary zigzag
  algebra.
* `TauCeti.SkewZigzagParameter.not_isGaugeEquivalent_one_exteriorCycle`: on an odd cycle with at
  least three vertices, over a ring in which `2` is not zero, it is not gauge trivial.

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

/-! ### The exterior parameter of a cycle -/

section ExteriorCycle

variable (k : Type w) [CommRing k] (m : ℕ) [NeZero m]

/-- The **exterior skew-zigzag parameter of a cycle graph**.  On a cycle with at least three
vertices, the two backtracks at a vertex sum to zero.  On such an odd cycle over a field of
characteristic other than two this is the nontrivial skew class; on such an even cycle it is gauge
equivalent to the constant parameter. -/
def exteriorCycle : SkewZigzagParameter k (cycleGraph m) :=
  exterior k (Or.inr fun _ _ _ _ h h' h'' => eq_or_eq_or_eq_of_cycleGraph_adj h h' h'')

/-- **The exterior ratio of two incident edges of a cycle graph** is one when they agree and minus
one otherwise. -/
@[simp]
theorem exteriorCycle_ratio {i j j' : Fin m} (h : (cycleGraph m).Adj i j)
    (h' : (cycleGraph m).Adj i j') :
    (exteriorCycle k m).ratio h h' = if j = j' then 1 else -1 :=
  exterior_ratio _ h h'

variable {k m}

/-- **The monodromy of the exterior parameter around a cycle graph on `m` vertices is
`(-1) ^ m`.** Every one of the `m` vertices contributes the sign between its two distinct
incident edges. -/
theorem monodromy_exteriorCycle (hm : 3 ≤ m) :
    monodromy (exteriorCycle k m) (cycleGraph_adj_add_one hm) = (-1 : kˣ) ^ m := by
  have hratio (i : Fin m) : (exteriorCycle k m).ratio (cycleGraph_adj_add_one hm i).symm
      (cycleGraph_adj_add_one hm (i + 1)) = -1 :=
    (exteriorCycle_ratio k m _ _).trans (ite_eq_right (add_one_add_one_ne_self hm i).symm)
  rw [monodromy_def, Finset.prod_congr rfl fun i _ => hratio i,
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
  have hval : ((v + 1 : Fin m) : ℕ) = (v.val + 1) % m := by
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  rcases Nat.lt_or_ge (v.val + 1) m with h1 | h1
  · rw [Nat.mod_eq_of_lt h1, pow_succ, mul_neg_one]
  · have hv : v.val + 1 = m := by have := v.isLt; omega
    have hev' : Even (v.val + 1) := by rw [hv]; exact hev
    have hodd : Odd v.val := Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hev')
    rw [hv, Nat.mod_self, pow_zero, hodd.neg_one_pow, neg_neg]

/-- **On an even cycle with at least three vertices the exterior parameter is gauge equivalent to
the constant parameter**, and so presents the ordinary zigzag relations.  The gauge is the
alternating sign on the edges of the cycle, which closes up exactly because the number of vertices
is even. -/
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
    have hratio : (exteriorCycle k m).ratio h h' = -1 :=
      (exteriorCycle_ratio k m h h').trans (ite_eq_right (add_one_add_one_ne_self hm j'))
    rw [hratio, hS, hS',
      eq_div_iff_mul_eq', neg_one_mul, neg_neg]
  · subst hv
    subst hj'
    have hS : backtrackScale (cycleGraph m) (cycleLabelling k m) h = (-1 : kˣ) ^ (j : ℕ) := by
      rw [← backtrackScale_symm (cycleGraph m) (cycleLabelling k m) h,
        backtrackScale_cycleLabelling hm _ h.symm]
    have hS' : backtrackScale (cycleGraph m) (cycleLabelling k m) h' = -((-1 : kˣ) ^ (j : ℕ)) := by
      rw [backtrackScale_cycleLabelling hm _ h', neg_one_pow_val_add_one hev]
    have hratio : (exteriorCycle k m).ratio h h' = -1 :=
      (exteriorCycle_ratio k m h h').trans (ite_eq_right (add_one_add_one_ne_self hm j).symm)
    rw [hratio, hS, hS',
      eq_div_iff_mul_eq', neg_one_mul]
  · subst hv
    have hjj : j = j' := add_right_cancel hv'
    subst hjj
    exact ((exteriorCycle k m).ratio_self h).trans (div_self' _).symm

/-- **On an odd cycle with at least three vertices, over a coefficient ring in which `2` is not
zero, the exterior parameter is not gauge equivalent to the constant parameter**: its monodromy
around the cycle is `-1`.  For a field this is the hypothesis that the characteristic is not two. -/
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

/-- **On an even cycle with at least three vertices the exterior skew-zigzag relation quotient is
the ordinary zigzag relation quotient.** -/
theorem nonempty_algEquiv_nonisolatedZigzagQuotient_exteriorCycle (hm : 3 ≤ m) (hev : Even m) :
    Nonempty (skewZigzagQuotient k (cycleGraph m) (SkewZigzagParameter.exteriorCycle k m) ≃ₐ[k]
      nonisolatedZigzagQuotient k (cycleGraph m)) :=
  nonempty_algEquiv_nonisolatedZigzagQuotient_of_isGaugeEquivalent_one k (cycleGraph m)
    (SkewZigzagParameter.isGaugeEquivalent_one_exteriorCycle hm hev)

/-- **On an even cycle with at least three vertices the exterior skew-zigzag algebra is the public
zigzag algebra.** -/
theorem nonempty_algEquiv_zigzagAlgebra_exteriorCycle (hm : 3 ≤ m) (hev : Even m) :
    Nonempty (skewZigzagQuotient k (cycleGraph m) (SkewZigzagParameter.exteriorCycle k m) ≃ₐ[k]
      zigzagAlgebra k (cycleGraph m)) := by
  have : Nontrivial (Fin m) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨e⟩ := nonempty_algEquiv_nonisolatedZigzagQuotient_exteriorCycle k m hm hev
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  exact ⟨e.trans (zigzagAlgebraEquivNonisolated k _ cycleGraph_connected).symm⟩

end ExteriorCycleAlgebra

end TauCeti
