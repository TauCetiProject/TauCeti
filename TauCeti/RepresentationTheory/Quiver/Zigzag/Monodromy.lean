/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Quiver.Zigzag.Gauge

/-!
# The monodromy of a skew-zigzag parameter around a closed edge cycle

A skew-zigzag parameter labels each ordered pair of incident edges of a simple graph by the
unit-valued ratio between the two backtracks they carry, and gauge equivalent parameters present
isomorphic algebras.  This file supplies the invariant which detects that a parameter is *not*
gauge trivial.

The invariant is the **monodromy** of a closed edge cycle: the product, over the vertices of the
cycle, of the ratio from the edge along which the cycle arrives at a vertex to the edge along
which it leaves.  A gauge transform multiplies each factor by the quotient of two backtrack
scales, and consecutive factors share those scales, so the correction telescopes around the cycle
and the monodromy depends only on the gauge class.  It is one for the constant parameter, so a
parameter whose monodromy around some closed edge cycle is not one is not gauge trivial.

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

end SkewZigzagParameter

end TauCeti
